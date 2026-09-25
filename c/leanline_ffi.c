/*
 * Minimal POSIX terminal shim for Leanline.
 *
 * Everything that Lean's standard library cannot express lives here:
 * termios raw mode, window size, poll(2) with a self-pipe (woken by
 * SIGWINCH, SIGINT and by other threads that want to print), and job
 * control suspension. The functions are deliberately small; all policy
 * is on the Lean side.
 */
#include <lean/lean.h>

#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>

static struct termios g_orig;
static int g_raw_fd = -1;
static int g_pipe[2] = {-1, -1};
static volatile sig_atomic_t g_winch = 0;
static volatile sig_atomic_t g_sigint = 0;
static struct sigaction g_old_winch;
static struct sigaction g_old_int;
static int g_winch_installed = 0;
static int g_int_installed = 0;
static int g_atexit_registered = 0;

static lean_obj_res ok_unit(void) { return lean_io_result_mk_ok(lean_box(0)); }

static lean_obj_res err_errno(const char *what) {
  char buf[256];
  int e = errno;
  snprintf(buf, sizeof buf, "leanline: %s: %s", what, strerror(e));
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

static void set_nonblock_cloexec(int fd) {
  int fl = fcntl(fd, F_GETFL);
  if (fl >= 0) fcntl(fd, F_SETFL, fl | O_NONBLOCK);
  int fdfl = fcntl(fd, F_GETFD);
  if (fdfl >= 0) fcntl(fd, F_SETFD, fdfl | FD_CLOEXEC);
}

static int ensure_pipe(void) {
  if (g_pipe[0] >= 0) return 0;
  if (pipe(g_pipe) != 0) return -1;
  set_nonblock_cloexec(g_pipe[0]);
  set_nonblock_cloexec(g_pipe[1]);
  return 0;
}

static void poke(void) {
  if (g_pipe[1] >= 0) {
    char c = 1;
    ssize_t r = write(g_pipe[1], &c, 1);
    (void)r;
  }
}

static int drain_pipe(void) {
  int any = 0;
  if (g_pipe[0] < 0) return 0;
  char buf[64];
  for (;;) {
    ssize_t r = read(g_pipe[0], buf, sizeof buf);
    if (r > 0) { any = 1; continue; }
    if (r < 0 && errno == EINTR) continue;
    break;
  }
  return any;
}

static void on_winch(int sig) {
  (void)sig;
  int e = errno;
  g_winch = 1;
  poke();
  errno = e;
}

static void on_int(int sig) {
  (void)sig;
  int e = errno;
  g_sigint = 1;
  poke();
  errno = e;
}

static void restore_at_exit(void) {
  if (g_raw_fd >= 0) tcsetattr(g_raw_fd, TCSAFLUSH, &g_orig);
}

/* Create the self-pipe. Idempotent. */
LEAN_EXPORT lean_obj_res leanline_init(void) {
  if (ensure_pipe() != 0) return err_errno("pipe");
  return ok_unit();
}

LEAN_EXPORT lean_obj_res leanline_isatty(uint32_t fd) {
  return lean_io_result_mk_ok(lean_box(isatty((int)fd) ? 1 : 0));
}

LEAN_EXPORT lean_obj_res leanline_open_tty(void) {
  int fd = open("/dev/tty", O_RDWR | O_CLOEXEC);
  if (fd < 0) return err_errno("open /dev/tty");
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

LEAN_EXPORT lean_obj_res leanline_close(uint32_t fd) {
  close((int)fd);
  return ok_unit();
}

/*
 * Raw mode: no line buffering, no echo, no signal generation (Ctrl-C and
 * Ctrl-Z arrive as bytes and are handled by the editor), no flow control
 * (so Ctrl-S / Ctrl-Q are usable), no CR->NL translation. Output
 * post-processing is left on so that ordinary program output still works.
 */
LEAN_EXPORT lean_obj_res leanline_raw_enable(uint32_t fd) {
  struct termios t;
  if (tcgetattr((int)fd, &t) != 0) return err_errno("tcgetattr");
  if (g_raw_fd < 0) {
    g_orig = t;
    g_raw_fd = (int)fd;
  }
  if (!g_atexit_registered) {
    atexit(restore_at_exit);
    g_atexit_registered = 1;
  }
  t.c_iflag &= ~(tcflag_t)(BRKINT | ICRNL | INPCK | ISTRIP | IXON);
  t.c_cflag |= CS8;
  t.c_lflag &= ~(tcflag_t)(ECHO | ICANON | IEXTEN | ISIG);
  t.c_cc[VMIN] = 1;
  t.c_cc[VTIME] = 0;
  if (tcsetattr((int)fd, TCSADRAIN, &t) != 0) return err_errno("tcsetattr");
  return ok_unit();
}

LEAN_EXPORT lean_obj_res leanline_raw_disable(uint32_t fd) {
  (void)fd;
  if (g_raw_fd >= 0) {
    int rfd = g_raw_fd;
    g_raw_fd = -1;
    if (tcsetattr(rfd, TCSADRAIN, &g_orig) != 0) return err_errno("tcsetattr");
  }
  return ok_unit();
}

/* Returns (cols << 32) | rows, or 0 when the size is unknown. */
LEAN_EXPORT lean_obj_res leanline_get_size(uint32_t fd) {
  struct winsize ws;
  uint64_t r = 0;
  if (ioctl((int)fd, TIOCGWINSZ, &ws) == 0 && ws.ws_col > 0)
    r = ((uint64_t)ws.ws_col << 32) | (uint64_t)ws.ws_row;
  return lean_io_result_mk_ok(lean_box_uint64(r));
}

/*
 * Wait until `fd` is readable or something else happens.
 * timeout_ms == UINT32_MAX waits forever.
 * Result: 0 timeout, 1 input ready, 2 window resized, 3 woken by another
 * thread, 4 SIGINT received, 5 hang-up / error on the descriptor.
 */
LEAN_EXPORT lean_obj_res leanline_wait(uint32_t fd, uint32_t timeout_ms) {
  if (ensure_pipe() != 0) return err_errno("pipe");
  for (;;) {
    if (g_winch) { g_winch = 0; drain_pipe(); return lean_io_result_mk_ok(lean_box(2)); }
    if (g_sigint) { drain_pipe(); return lean_io_result_mk_ok(lean_box(4)); }
    struct pollfd fds[2];
    fds[0].fd = (int)fd; fds[0].events = POLLIN; fds[0].revents = 0;
    fds[1].fd = g_pipe[0]; fds[1].events = POLLIN; fds[1].revents = 0;
    int t = timeout_ms == UINT32_MAX ? -1 : (int)timeout_ms;
    int r = poll(fds, 2, t);
    if (r < 0) {
      if (errno == EINTR) continue;
      return err_errno("poll");
    }
    if (r == 0) return lean_io_result_mk_ok(lean_box(0));
    if (fds[1].revents & POLLIN) {
      drain_pipe();
      if (g_winch) { g_winch = 0; return lean_io_result_mk_ok(lean_box(2)); }
      if (g_sigint) return lean_io_result_mk_ok(lean_box(4));
      return lean_io_result_mk_ok(lean_box(3));
    }
    if (fds[0].revents & POLLIN) return lean_io_result_mk_ok(lean_box(1));
    if (fds[0].revents & (POLLHUP | POLLERR | POLLNVAL)) return lean_io_result_mk_ok(lean_box(5));
  }
}

/* Read at most `max` bytes. An empty result means end of file. */
LEAN_EXPORT lean_obj_res leanline_read(uint32_t fd, size_t max) {
  if (max == 0) max = 1;
  lean_object *arr = lean_alloc_sarray(1, 0, max);
  for (;;) {
    ssize_t r = read((int)fd, lean_sarray_cptr(arr), max);
    if (r >= 0) {
      lean_sarray_set_size(arr, (size_t)r);
      return lean_io_result_mk_ok(arr);
    }
    if (errno == EINTR) continue;
    if (errno == EAGAIN || errno == EWOULDBLOCK) {
      lean_sarray_set_size(arr, 0);
      return lean_io_result_mk_ok(arr);
    }
    lean_dec(arr);
    return err_errno("read");
  }
}

LEAN_EXPORT lean_obj_res leanline_write(uint32_t fd, b_lean_obj_arg bytes) {
  const uint8_t *p = lean_sarray_cptr(bytes);
  size_t n = lean_sarray_size(bytes);
  while (n > 0) {
    ssize_t r = write((int)fd, p, n);
    if (r < 0) {
      if (errno == EINTR) continue;
      return err_errno("write");
    }
    p += r;
    n -= (size_t)r;
  }
  return ok_unit();
}

LEAN_EXPORT lean_obj_res leanline_winch_install(void) {
  if (ensure_pipe() != 0) return err_errno("pipe");
  if (!g_winch_installed) {
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = on_winch;
    sigemptyset(&sa.sa_mask);
    if (sigaction(SIGWINCH, &sa, &g_old_winch) != 0) return err_errno("sigaction");
    g_winch_installed = 1;
  }
  return ok_unit();
}

LEAN_EXPORT lean_obj_res leanline_winch_uninstall(void) {
  if (g_winch_installed) {
    sigaction(SIGWINCH, &g_old_winch, NULL);
    g_winch_installed = 0;
  }
  return ok_unit();
}

LEAN_EXPORT lean_obj_res leanline_sigint_install(void) {
  if (ensure_pipe() != 0) return err_errno("pipe");
  if (!g_int_installed) {
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = on_int;
    sigemptyset(&sa.sa_mask);
    if (sigaction(SIGINT, &sa, &g_old_int) != 0) return err_errno("sigaction");
    g_int_installed = 1;
  }
  return ok_unit();
}

LEAN_EXPORT lean_obj_res leanline_sigint_uninstall(void) {
  if (g_int_installed) {
    sigaction(SIGINT, &g_old_int, NULL);
    g_int_installed = 0;
  }
  return ok_unit();
}

/* Test and clear the "SIGINT arrived" flag. */
LEAN_EXPORT lean_obj_res leanline_sigint_take(void) {
  int v = g_sigint ? 1 : 0;
  g_sigint = 0;
  return lean_io_result_mk_ok(lean_box(v));
}

/* Wake a thread blocked in leanline_wait. Safe to call from any thread. */
LEAN_EXPORT lean_obj_res leanline_wake(void) {
  poke();
  return ok_unit();
}

static volatile sig_atomic_t g_cont = 0;
static void on_cont(int sig) { (void)sig; g_cont = 1; }

/*
 * Job-control suspend: restore the terminal and stop the process group as
 * the terminal driver would have done for Ctrl-Z. The signal is
 * process-directed, so with several threads the stop can take effect after
 * kill() returns; wait for SIGCONT before returning. If the stop signal is
 * discarded (orphaned process group) give up after about half a second.
 * The caller re-enters raw mode afterwards.
 */
LEAN_EXPORT lean_obj_res leanline_suspend(uint32_t fd) {
  (void)fd;
  struct sigaction cur;
  if (sigaction(SIGTSTP, NULL, &cur) == 0 && cur.sa_handler == SIG_IGN) return ok_unit();
  struct sigaction sa, old_cont;
  memset(&sa, 0, sizeof sa);
  sa.sa_handler = on_cont;
  sigemptyset(&sa.sa_mask);
  g_cont = 0;
  sigaction(SIGCONT, &sa, &old_cont);
  if (g_raw_fd >= 0) tcsetattr(g_raw_fd, TCSADRAIN, &g_orig);
  kill(0, SIGTSTP);
  for (int i = 0; i < 50 && !g_cont; i++) {
    struct timespec ts = {0, 10 * 1000 * 1000};
    nanosleep(&ts, NULL);
  }
  sigaction(SIGCONT, &old_cont, NULL);
  return ok_unit();
}

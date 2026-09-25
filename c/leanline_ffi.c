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

#ifdef _WIN32
/*
 * Windows. The console is put into virtual-terminal mode, so input arrives
 * as the same byte sequences an xterm sends and output understands the same
 * escape sequences; everything above this shim is shared with POSIX. Consoles
 * without VT support (before Windows 10) report "not a terminal", and
 * Leanline then reads plain lines.
 */
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef ENABLE_VIRTUAL_TERMINAL_INPUT
#define ENABLE_VIRTUAL_TERMINAL_INPUT 0x0200
#endif
#ifndef ENABLE_VIRTUAL_TERMINAL_PROCESSING
#define ENABLE_VIRTUAL_TERMINAL_PROCESSING 0x0004
#endif

static HANDLE g_wake = NULL;
static volatile LONG g_sigint = 0;
static DWORD g_orig_in = 0;
static DWORD g_orig_out = 0;
static UINT g_orig_cp_in = 0;
static int g_raw = 0;
static WCHAR g_high_surrogate = 0;

static lean_obj_res ok_unit(void) { return lean_io_result_mk_ok(lean_box(0)); }

static lean_obj_res err_win(const char *what) {
  char buf[256];
  snprintf(buf, sizeof buf, "leanline: %s failed (error %lu)", what, (unsigned long)GetLastError());
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

static HANDLE handle_of(uint32_t fd) { return GetStdHandle(fd == 0 ? STD_INPUT_HANDLE : STD_OUTPUT_HANDLE); }

static int ensure_event(void) {
  if (g_wake == NULL) g_wake = CreateEventW(NULL, TRUE, FALSE, NULL);
  return g_wake != NULL;
}

static size_t encode_utf8(uint32_t cp, uint8_t *out) {
  if (cp < 0x80) { out[0] = (uint8_t)cp; return 1; }
  if (cp < 0x800) { out[0] = (uint8_t)(0xC0 | (cp >> 6)); out[1] = (uint8_t)(0x80 | (cp & 0x3F)); return 2; }
  if (cp < 0x10000) {
    out[0] = (uint8_t)(0xE0 | (cp >> 12)); out[1] = (uint8_t)(0x80 | ((cp >> 6) & 0x3F));
    out[2] = (uint8_t)(0x80 | (cp & 0x3F)); return 3;
  }
  out[0] = (uint8_t)(0xF0 | (cp >> 18)); out[1] = (uint8_t)(0x80 | ((cp >> 12) & 0x3F));
  out[2] = (uint8_t)(0x80 | ((cp >> 6) & 0x3F)); out[3] = (uint8_t)(0x80 | (cp & 0x3F)); return 4;
}

static BOOL WINAPI on_ctrl(DWORD type) {
  if (type == CTRL_C_EVENT || type == CTRL_BREAK_EVENT) {
    InterlockedExchange(&g_sigint, 1);
    if (g_wake != NULL) SetEvent(g_wake);
    return TRUE;
  }
  return FALSE;
}

LEAN_EXPORT lean_obj_res leanline_init(void) {
  if (!ensure_event()) return err_win("CreateEvent");
  return ok_unit();
}

/* A console that accepts virtual-terminal mode counts as a terminal. */
LEAN_EXPORT lean_obj_res leanline_isatty(uint32_t fd) {
  HANDLE h = handle_of(fd);
  DWORD mode = 0;
  int ok = 0;
  if (h != NULL && h != INVALID_HANDLE_VALUE && GetConsoleMode(h, &mode)) {
    DWORD vt = fd == 0 ? ENABLE_VIRTUAL_TERMINAL_INPUT : ENABLE_VIRTUAL_TERMINAL_PROCESSING;
    ok = SetConsoleMode(h, mode | vt) != 0;
    SetConsoleMode(h, mode);
  }
  return lean_io_result_mk_ok(lean_box(ok ? 1 : 0));
}

LEAN_EXPORT lean_obj_res leanline_open_tty(void) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("leanline: no controlling terminal on Windows")));
}

LEAN_EXPORT lean_obj_res leanline_close(uint32_t fd) { (void)fd; return ok_unit(); }

LEAN_EXPORT lean_obj_res leanline_raw_enable(uint32_t fd) {
  (void)fd;
  HANDLE hin = GetStdHandle(STD_INPUT_HANDLE);
  HANDLE hout = GetStdHandle(STD_OUTPUT_HANDLE);
  DWORD in_mode = 0, out_mode = 0;
  if (!GetConsoleMode(hin, &in_mode) || !GetConsoleMode(hout, &out_mode)) return err_win("GetConsoleMode");
  if (!g_raw) {
    g_orig_in = in_mode;
    g_orig_out = out_mode;
    g_orig_cp_in = GetConsoleCP();
    g_raw = 1;
  }
  DWORD raw_in = (in_mode & ~(DWORD)(ENABLE_LINE_INPUT | ENABLE_ECHO_INPUT | ENABLE_PROCESSED_INPUT))
                 | ENABLE_VIRTUAL_TERMINAL_INPUT | ENABLE_WINDOW_INPUT;
  if (!SetConsoleMode(hin, raw_in)) return err_win("SetConsoleMode");
  if (!SetConsoleMode(hout, out_mode | ENABLE_PROCESSED_OUTPUT | ENABLE_VIRTUAL_TERMINAL_PROCESSING))
    return err_win("SetConsoleMode");
  SetConsoleCP(CP_UTF8);
  return ok_unit();
}

LEAN_EXPORT lean_obj_res leanline_raw_disable(uint32_t fd) {
  (void)fd;
  if (g_raw) {
    SetConsoleMode(GetStdHandle(STD_INPUT_HANDLE), g_orig_in);
    SetConsoleMode(GetStdHandle(STD_OUTPUT_HANDLE), g_orig_out);
    SetConsoleCP(g_orig_cp_in);
    g_raw = 0;
  }
  return ok_unit();
}

LEAN_EXPORT lean_obj_res leanline_get_size(uint32_t fd) {
  CONSOLE_SCREEN_BUFFER_INFO info;
  uint64_t r = 0;
  (void)fd;
  if (GetConsoleScreenBufferInfo(GetStdHandle(STD_OUTPUT_HANDLE), &info)) {
    uint64_t cols = (uint64_t)(info.srWindow.Right - info.srWindow.Left + 1);
    uint64_t rows = (uint64_t)(info.srWindow.Bottom - info.srWindow.Top + 1);
    r = (cols << 32) | rows;
  }
  return lean_io_result_mk_ok(lean_box_uint64(r));
}

static int is_char_key(const INPUT_RECORD *rec) {
  return rec->EventType == KEY_EVENT && rec->Event.KeyEvent.bKeyDown && rec->Event.KeyEvent.uChar.UnicodeChar != 0;
}

/* Same contract as the POSIX version. */
LEAN_EXPORT lean_obj_res leanline_wait(uint32_t fd, uint32_t timeout_ms) {
  HANDLE hin = GetStdHandle(STD_INPUT_HANDLE);
  DWORD start = GetTickCount();
  (void)fd;
  if (!ensure_event()) return err_win("CreateEvent");
  for (;;) {
    DWORD wait_ms = INFINITE;
    if (timeout_ms != UINT32_MAX) {
      DWORD elapsed = GetTickCount() - start;
      wait_ms = elapsed >= timeout_ms ? 0 : timeout_ms - elapsed;
    }
    HANDLE hs[2];
    hs[0] = g_wake;
    hs[1] = hin;
    DWORD r = WaitForMultipleObjects(2, hs, FALSE, wait_ms);
    if (r == WAIT_TIMEOUT) return lean_io_result_mk_ok(lean_box(0));
    if (r == WAIT_OBJECT_0) {
      ResetEvent(g_wake);
      return lean_io_result_mk_ok(lean_box(3));
    }
    if (r != WAIT_OBJECT_0 + 1) return err_win("WaitForMultipleObjects");
    /* Key presses mean input; size changes are reported; other records are dropped. */
    int resized = 0;
    for (;;) {
      INPUT_RECORD rec;
      DWORD n = 0;
      if (!PeekConsoleInputW(hin, &rec, 1, &n) || n == 0) break;
      if (is_char_key(&rec)) return lean_io_result_mk_ok(lean_box(1));
      if (!ReadConsoleInputW(hin, &rec, 1, &n)) break;
      if (rec.EventType == WINDOW_BUFFER_SIZE_EVENT) resized = 1;
    }
    if (resized) return lean_io_result_mk_ok(lean_box(2));
  }
}

/* Read the characters of pending key presses as UTF-8. */
LEAN_EXPORT lean_obj_res leanline_read(uint32_t fd, size_t max) {
  HANDLE hin = GetStdHandle(STD_INPUT_HANDLE);
  (void)fd;
  if (max < 16) max = 16;
  lean_object *arr = lean_alloc_sarray(1, 0, max);
  uint8_t *out = lean_sarray_cptr(arr);
  size_t len = 0;
  for (;;) {
    DWORD avail = 0;
    if (!GetNumberOfConsoleInputEvents(hin, &avail)) {
      lean_dec(arr);
      return err_win("GetNumberOfConsoleInputEvents");
    }
    if (avail == 0 && len > 0) break;
    DWORD room = (DWORD)((max - len) / 4);
    if (room == 0) break;
    DWORD want = avail == 0 ? 1 : avail;
    if (want > room) want = room;
    if (want > 64) want = 64;
    INPUT_RECORD recs[64];
    DWORD n = 0;
    if (!ReadConsoleInputW(hin, recs, want, &n)) {
      lean_dec(arr);
      return err_win("ReadConsoleInput");
    }
    for (DWORD i = 0; i < n; i++) {
      if (!is_char_key(&recs[i])) continue;
      WCHAR w = recs[i].Event.KeyEvent.uChar.UnicodeChar;
      WORD repeat = recs[i].Event.KeyEvent.wRepeatCount ? recs[i].Event.KeyEvent.wRepeatCount : 1;
      uint32_t cp;
      if (w >= 0xD800 && w <= 0xDBFF) { g_high_surrogate = w; continue; }
      if (w >= 0xDC00 && w <= 0xDFFF) {
        if (g_high_surrogate == 0) continue;
        cp = 0x10000 + (((uint32_t)g_high_surrogate - 0xD800) << 10) + ((uint32_t)w - 0xDC00);
        g_high_surrogate = 0;
      } else {
        cp = (uint32_t)w;
      }
      for (WORD k = 0; k < repeat && len + 4 <= max; k++) len += encode_utf8(cp, out + len);
    }
    if (len > 0 && avail <= n) break;
  }
  lean_sarray_set_size(arr, len);
  return lean_io_result_mk_ok(arr);
}

/* UTF-8 is converted to UTF-16 for the console, so the code page does not matter. */
LEAN_EXPORT lean_obj_res leanline_write(uint32_t fd, b_lean_obj_arg bytes) {
  HANDLE h = handle_of(fd);
  const char *p = (const char *)lean_sarray_cptr(bytes);
  size_t n = lean_sarray_size(bytes);
  DWORD mode = 0;
  if (n == 0) return ok_unit();
  if (GetConsoleMode(h, &mode)) {
    int wn = MultiByteToWideChar(CP_UTF8, 0, p, (int)n, NULL, 0);
    WCHAR *w = wn > 0 ? (WCHAR *)malloc(sizeof(WCHAR) * (size_t)wn) : NULL;
    if (w != NULL) {
      DWORD written = 0;
      MultiByteToWideChar(CP_UTF8, 0, p, (int)n, w, wn);
      BOOL ok = WriteConsoleW(h, w, (DWORD)wn, &written, NULL);
      free(w);
      if (!ok) return err_win("WriteConsole");
      return ok_unit();
    }
  }
  while (n > 0) {
    DWORD written = 0;
    if (!WriteFile(h, p, (DWORD)n, &written, NULL)) return err_win("WriteFile");
    p += written;
    n -= written;
  }
  return ok_unit();
}

/* Size changes arrive as console input records (see leanline_wait). */
LEAN_EXPORT lean_obj_res leanline_winch_install(void) { return ok_unit(); }
LEAN_EXPORT lean_obj_res leanline_winch_uninstall(void) { return ok_unit(); }

LEAN_EXPORT lean_obj_res leanline_sigint_install(void) {
  if (!ensure_event()) return err_win("CreateEvent");
  if (!SetConsoleCtrlHandler(on_ctrl, TRUE)) return err_win("SetConsoleCtrlHandler");
  return ok_unit();
}

LEAN_EXPORT lean_obj_res leanline_sigint_uninstall(void) {
  SetConsoleCtrlHandler(on_ctrl, FALSE);
  return ok_unit();
}

LEAN_EXPORT lean_obj_res leanline_sigint_take(void) {
  LONG v = InterlockedExchange(&g_sigint, 0);
  return lean_io_result_mk_ok(lean_box(v ? 1 : 0));
}

LEAN_EXPORT lean_obj_res leanline_wake(void) {
  if (ensure_event()) SetEvent(g_wake);
  return ok_unit();
}

/* No job control on Windows. */
LEAN_EXPORT lean_obj_res leanline_suspend(uint32_t fd) { (void)fd; return ok_unit(); }
#else

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
 * Result: 0 timeout, 1 input ready, 2 window resized, 3 woken (by another
 * thread or a signal), 5 hang-up / error on the descriptor.
 */
LEAN_EXPORT lean_obj_res leanline_wait(uint32_t fd, uint32_t timeout_ms) {
  if (ensure_pipe() != 0) return err_errno("pipe");
  for (;;) {
    if (g_winch) { g_winch = 0; drain_pipe(); return lean_io_result_mk_ok(lean_box(2)); }
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
      /* Woken by another thread or by SIGINT (whose flag stays set for
         leanline_sigint_take). */
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

#endif

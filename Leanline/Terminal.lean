/-!
# Terminal primitives

Thin bindings to the C shim in `c/leanline_ffi.c`. Nothing here knows about
line editing; the driver in `Leanline.Session` builds on these.
-/

namespace Leanline.Terminal

/-- A POSIX file descriptor. -/
structure Fd where
  val : UInt32
  deriving DecidableEq, Repr, Inhabited

def Fd.stdin : Fd := ⟨0⟩
def Fd.stdout : Fd := ⟨1⟩

@[extern "leanline_init"] private opaque initPrim : IO Unit
@[extern "leanline_isatty"] private opaque isattyPrim (fd : UInt32) : IO Bool
@[extern "leanline_open_tty"] private opaque openTtyPrim : IO UInt32
@[extern "leanline_close"] private opaque closePrim (fd : UInt32) : IO Unit
@[extern "leanline_raw_enable"] private opaque rawEnablePrim (fd : UInt32) : IO Unit
@[extern "leanline_raw_disable"] private opaque rawDisablePrim (fd : UInt32) : IO Unit
@[extern "leanline_get_size"] private opaque getSizePrim (fd : UInt32) : IO UInt64
@[extern "leanline_wait"] private opaque waitPrim (fd : UInt32) (timeoutMs : UInt32) : IO UInt8
@[extern "leanline_read"] private opaque readPrim (fd : UInt32) (max : USize) : IO ByteArray
@[extern "leanline_write"] private opaque writePrim (fd : UInt32) (bytes : @& ByteArray) : IO Unit
@[extern "leanline_winch_install"] private opaque winchInstallPrim : IO Unit
@[extern "leanline_winch_uninstall"] private opaque winchUninstallPrim : IO Unit
@[extern "leanline_sigint_install"] private opaque sigintInstallPrim : IO Unit
@[extern "leanline_sigint_uninstall"] private opaque sigintUninstallPrim : IO Unit
@[extern "leanline_sigint_take"] private opaque sigintTakePrim : IO Bool
@[extern "leanline_wake"] private opaque wakePrim : IO Unit
@[extern "leanline_suspend"] private opaque suspendPrim (fd : UInt32) : IO Unit

/-- Prepare the process-wide self-pipe. Idempotent. -/
def init : IO Unit := initPrim

def isTerminal (fd : Fd) : IO Bool := isattyPrim fd.val

/-- Open the controlling terminal (`/dev/tty`) for reading and writing. -/
def openControllingTerminal : IO Fd := return ⟨← openTtyPrim⟩

def close (fd : Fd) : IO Unit := closePrim fd.val

def enableRawMode (fd : Fd) : IO Unit := rawEnablePrim fd.val
def disableRawMode (fd : Fd) : IO Unit := rawDisablePrim fd.val

/-- Terminal dimensions in character cells. -/
structure Size where
  cols : Nat
  rows : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Current window size, or `none` if the descriptor has no size (not a tty). -/
def getSize? (fd : Fd) : IO (Option Size) := do
  let r ← getSizePrim fd.val
  if r == 0 then return none
  return some { cols := (r >>> 32).toNat, rows := (r &&& 0xffffffff).toNat }

/-- Why `wait` returned. -/
inductive WaitResult where
  | timeout
  | ready
  | resized
  | woken
  | sigint
  | hangup
  deriving DecidableEq, Repr, Inhabited

/-- Block until input is available, the window is resized, another thread
calls `wake`, SIGINT is delivered (if `withSigintHandler` is active), or the
timeout expires. `none` waits indefinitely. -/
def wait (fd : Fd) (timeoutMs : Option Nat := none) : IO WaitResult := do
  let t : UInt32 := match timeoutMs with
    | none => 0xffffffff
    | some ms => (min ms 0xfffffffe).toUInt32
  return match ← waitPrim fd.val t with
    | 0 => .timeout
    | 1 => .ready
    | 2 => .resized
    | 3 => .woken
    | 4 => .sigint
    | _ => .hangup

/-- Read at most `max` bytes; an empty array means end of file. -/
def read (fd : Fd) (max : Nat := 1024) : IO ByteArray := readPrim fd.val max.toUSize

def write (fd : Fd) (bytes : ByteArray) : IO Unit := writePrim fd.val bytes

def writeString (fd : Fd) (s : String) : IO Unit := write fd s.toUTF8

/-- Start reporting window size changes through `wait`. -/
def installResizeHandler : IO Unit := winchInstallPrim
def uninstallResizeHandler : IO Unit := winchUninstallPrim

def installSigintHandler : IO Unit := sigintInstallPrim
def uninstallSigintHandler : IO Unit := sigintUninstallPrim

/-- Test-and-clear the flag set by the SIGINT handler. -/
def takeSigint : IO Bool := sigintTakePrim

/-- Wake a thread blocked in `wait`. Safe to call from any thread. -/
def wake : IO Unit := wakePrim

/-- Restore the terminal and stop the process group (job control).
Returns once the process is continued; the caller must re-enter raw mode. -/
def suspend (fd : Fd) : IO Unit := suspendPrim fd.val

end Leanline.Terminal

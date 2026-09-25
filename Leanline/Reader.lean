import Leanline.Terminal
import Leanline.KeyDecoder

/-!
# Terminal input reader

Reads bytes from the terminal and decodes them into events, waiting a short
time for the rest of an escape sequence before deciding that a lone `ESC`
was the Escape key.
-/

namespace Leanline

inductive TermInput where
  | event (e : InputEvent)
  | resized
  /-- Another thread wants the display (external print). -/
  | woken
  | eof
  deriving Repr, Inhabited

structure Reader where
  fd : Terminal.Fd
  table : KeySeqTable
  /-- Milliseconds to wait for the remainder of an escape sequence. -/
  timeoutMs : Nat
  pending : IO.Ref (List UInt8)
  events : IO.Ref (List InputEvent)

namespace Reader

def create (fd : Terminal.Fd) (table : KeySeqTable) (timeoutMs : Nat) : IO Reader := do
  return { fd, table, timeoutMs, pending := ← IO.mkRef [], events := ← IO.mkRef [] }

private def pasteStart : List UInt8 := [0x1B, 0x5B, 0x32, 0x30, 0x30, 0x7E]

private def decodeInto (r : Reader) (final : Bool) : IO Unit := do
  let (evs, rest) := KeyDecoder.decodeAll r.table final (← r.pending.get)
  r.pending.set rest
  r.events.modify (· ++ evs)

/-- Are decoded events waiting to be consumed? -/
def hasBuffered (r : Reader) : IO Bool := return !(← r.events.get).isEmpty

/-- Discard buffered input (for example after the editor has finished). -/
def reset (r : Reader) : IO Unit := do
  r.pending.set []
  r.events.set []

/-- The next input. Blocks until something happens. -/
partial def next (r : Reader) : IO TermInput := do
  match ← r.events.modifyGet (fun es => (es.head?, es.drop 1)) with
  | some e => return .event e
  | none =>
    let pending ← r.pending.get
    -- Pastes can be long; give them more time to arrive completely.
    let timeout :=
      if pending.isEmpty then none
      else if pasteStart.isPrefixOf pending then some 2000
      else some r.timeoutMs
    match ← Terminal.wait r.fd timeout with
    | .ready =>
      let bytes ← Terminal.read r.fd 4096
      if bytes.isEmpty then
        if pending.isEmpty then return .eof
        decodeInto r true
        next r
      else
        r.pending.set (pending ++ bytes.toList)
        decodeInto r false
        next r
    | .timeout =>
      decodeInto r true
      next r
    | .resized => return .resized
    | .woken | .sigint => return .woken
    | .hangup =>
      if pending.isEmpty then return .eof
      decodeInto r true
      next r

/-- The next key or paste, ignoring resizes and wake-ups; `none` at end of input. -/
partial def nextEvent (r : Reader) : IO (Option InputEvent) := do
  match ← r.next with
  | .event e => return some e
  | .eof => return none
  | _ => r.nextEvent

end Reader

end Leanline

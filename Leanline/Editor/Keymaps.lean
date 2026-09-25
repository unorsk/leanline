import Leanline.Editor.Types

/-!
# Built-in keymaps

Keymaps are ordinary data. `EditorConfig.bindings` is consulted first, so a
program can add or override bindings with a list of `(keys, command)` pairs.
-/

namespace Leanline.Keymaps

open Key

private def k (b : BaseKey) : List Key := [Key.plain b]
private def c (ch : Char) : List Key := [Key.ctrl ch]
private def m (ch : Char) : List Key := [Key.alt ch]

/-- Bindings shared by Emacs mode and vi insert mode. -/
def common : Keymap :=
  [ (k .enter, .acceptLine), (c 'j', .acceptLine),
    (k .left, .backwardChar), (k .right, .forwardChar),
    (k .home, .beginningOfLine), (k .end, .endOfLine),
    (k .up, .previousHistory), (k .down, .nextHistory),
    (k .delete, .deleteChar),
    (k .backspace, .backwardDeleteChar), (c 'h', .backwardDeleteChar),
    ([⟨.left, { ctrl := true }⟩], .backwardWord), ([⟨.right, { ctrl := true }⟩], .forwardWord),
    ([⟨.left, { alt := true }⟩], .backwardWord), ([⟨.right, { alt := true }⟩], .forwardWord),
    (k .tab, .complete), ([⟨.tab, { shift := true }⟩], .menuCompleteBackward),
    (c 'l', .clearScreen), (c 'c', .interrupt), (c 'z', .suspend),
    (c 'v', .quotedInsert), (c 'r', .reverseSearchHistory), (c 's', .forwardSearchHistory) ]

def emacs : Keymap :=
  common ++
  [ (c 'a', .beginningOfLine), (c 'e', .endOfLine),
    (c 'b', .backwardChar), (c 'f', .forwardChar),
    (m 'b', .backwardWord), (m 'f', .forwardWord),
    (c 'd', .deleteCharOrEof),
    (c 'k', .killLine), (c 'u', .backwardKillLine), (c 'w', .unixWordRubout),
    (m 'd', .killWord), ([⟨.backspace, { alt := true }⟩], .backwardKillWord),
    ([Key.ctrl 'x', Key.plain .backspace], .backwardKillLine),
    (c 'y', .yank), (m 'y', .yankPop), (m '.', .yankLastArg), (m '_', .yankLastArg),
    (c 't', .transposeChars),
    (m 'u', .upcaseWord), (m 'l', .downcaseWord), (m 'c', .capitalizeWord),
    (c 'p', .previousHistory), (c 'n', .nextHistory),
    (m '<', .beginningOfHistory), (m '>', .endOfHistory),
    (k .pageUp, .beginningOfHistory), (k .pageDown, .endOfHistory),
    (m 'p', .historySearchBackward), (m 'n', .historySearchForward),
    (m '?', .possibleCompletions), (m '=', .possibleCompletions),
    (c '_', .undo), ([Key.ctrl 'x', Key.ctrl 'u'], .undo), (m 'r', .revertLine),
    ([⟨.enter, { alt := true }⟩], .newline),
    ([Key.ctrl 'x', Key.ctrl 'e'], .editInEditor),
    (c 'g', .abort), (c 'q', .quotedInsert),
    (m '0', .digitArgument 0), (m '1', .digitArgument 1), (m '2', .digitArgument 2),
    (m '3', .digitArgument 3), (m '4', .digitArgument 4), (m '5', .digitArgument 5),
    (m '6', .digitArgument 6), (m '7', .digitArgument 7), (m '8', .digitArgument 8),
    (m '9', .digitArgument 9) ]

def viInsert : Keymap :=
  common ++
  [ (k .escape, .viCommandMode),
    (c 'd', .deleteCharOrEof),
    (c 'w', .unixWordRubout), (c 'u', .backwardKillLine),
    (c 'y', .yank), (c 't', .transposeChars),
    (c 'p', .previousHistory), (c 'n', .nextHistory),
    ([⟨.enter, { alt := true }⟩], .newline) ]

end Leanline.Keymaps

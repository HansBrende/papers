import Transpose.Tape.Defs

/-!
# A small data-dependent transposer (non-vacuity witness for Theorem P′)

`tr2dd` is `Witness.tr2` (no work tapes) with an extra `stay` step at the start when the first input
bit is `1`. So its running time is `6` or `5` depending on the input, and it is not oblivious.

On input `[a, b, c, d]` it outputs `[a, c, b, d]`: states `0`/`9` handle the first bit (with the
extra step when it is `1`), and states `1`–`8` behave as in `tr2`.
-/

namespace Transpose.Tape.Witness

open Transpose

/-- The data-dependent `2 × 2` transposer. -/
def tr2dd : TM where
  k := 0
  g := 0
  q := 9
  δ := fun s sym _ =>
    let bit := sym.getD false
    match s.val with
    | 0 => if bit then some (9, .stay, fun i => i.elim0, some bit)
           else some (1, .right, fun i => i.elim0, some bit)
    | 9 => some (1, .right, fun i => i.elim0, none)
    | 1 => some (if bit then 3 else 2, .right, fun i => i.elim0, none)
    | 2 => some (4, .right, fun i => i.elim0, some bit)
    | 3 => some (5, .right, fun i => i.elim0, some bit)
    | 4 => some (if bit then 7 else 6, .stay, fun i => i.elim0, some false)
    | 5 => some (if bit then 7 else 6, .stay, fun i => i.elim0, some true)
    | 6 => some (8, .stay, fun i => i.elim0, some false)
    | 7 => some (8, .stay, fun i => i.elim0, some true)
    | _ => none

end Transpose.Tape.Witness

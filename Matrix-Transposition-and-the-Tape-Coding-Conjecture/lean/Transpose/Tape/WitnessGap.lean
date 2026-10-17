import Transpose.Tape.Defs

/-!
# A counterexample machine for the offsets-only Block Locality Lemma

`gapTM` (`k = 1`, `g = 1`, 17 states) transposes `1 × 1` matrices with `1`-bit entries. It is the
machine of `block_locality_offsets_counterexample` (`OffsetsCounterexample.lean`).

At step 0 it reads the input bit `x`, moves the input head off the input and marks work cell `1`.
Then, with slot length `r = 4`, it follows one of two work-head motions:
* `x = 0`: positions `1, 2, 3, 3, 4, 5, 6, 5` at times `1, …, 8`;
* `x = 1`: positions `1, 2, 3, 3, 4, 3, 2, 1`.

Both runs have pair residency `{0}`, `{0, 1}`, `{0, 1}` at slots `0, 1, 2`. At time `8` the heads
stand at offset `1` of blocks `1` and `0` respectively. Step 8 outputs whether the cell under the
head is marked, which is `x`.
-/

namespace Transpose.Tape.Witness

open Transpose

/-- The work-tape action "write `s`, move `d`" on the single work tape. -/
def gapWr (s : Fin 2) (d : Dir) : Fin 1 → Fin 2 × Dir := fun _ => (s, d)

/-- The counterexample machine. States: `0` start; `1`–`7` the motion for `x = 0`; `8`–`14` the
motion for `x = 1`; `15` output; `16` halt. -/
def gapTM : TM where
  k := 1
  g := 1
  q := 16
  δ := fun s inp syms =>
    match s.val with
    | 0 => some (if inp = some true then 8 else 1, Dir.left, gapWr 0 Dir.right, none)
    | 1 => some (2, Dir.stay, gapWr 1 Dir.right, none)
    | 2 => some (3, Dir.stay, gapWr 0 Dir.right, none)
    | 3 => some (4, Dir.stay, gapWr 0 Dir.stay, none)
    | 4 => some (5, Dir.stay, gapWr 0 Dir.right, none)
    | 5 => some (6, Dir.stay, gapWr 0 Dir.right, none)
    | 6 => some (7, Dir.stay, gapWr 0 Dir.right, none)
    | 7 => some (15, Dir.stay, gapWr 0 Dir.left, none)
    | 8 => some (9, Dir.stay, gapWr 1 Dir.right, none)
    | 9 => some (10, Dir.stay, gapWr 0 Dir.right, none)
    | 10 => some (11, Dir.stay, gapWr 0 Dir.stay, none)
    | 11 => some (12, Dir.stay, gapWr 0 Dir.right, none)
    | 12 => some (13, Dir.stay, gapWr 0 Dir.left, none)
    | 13 => some (14, Dir.stay, gapWr 0 Dir.left, none)
    | 14 => some (15, Dir.stay, gapWr 0 Dir.left, none)
    | 15 => some (16, Dir.stay, fun _ => (syms 0, Dir.stay), some (decide (syms 0 = 1)))
    | _ => none

end Transpose.Tape.Witness

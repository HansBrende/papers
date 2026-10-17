import Transpose.Tape.Defs

/-!
# A small oblivious transposer (non-vacuity witness)

`tr2` is a machine with no work tapes and 9 states that transposes `2 × 2` matrices with 1-bit
entries obliviously.

On input `[a, b, c, d]`, i.e. `[[a, b], [c, d]]` row-major, it outputs `[a, c, b, d]`:
* step 0 outputs `a` and moves right;
* step 1 remembers `b` in the state;
* step 2 outputs `c`;
* step 3 outputs the remembered `b` and remembers `d`;
* step 4 outputs `d`;
* the machine halts at time 5.

The head schedule (positions 0, 1, 2, 3, 3, 3) and the output schedule are the same for every
input. For `J = {2, 3, 4}` the cut is non-trivial: `S_J = {(0, 1)}`.

`tr2k` is `tr2` with one idle work tape (`k = 1`): every step writes blank there and stays. It
shows that Theorem P's hypotheses hold with `k ≥ 1`.
-/

namespace Transpose.Tape.Witness

open Transpose

/-- The `2 × 2` oblivious transposer. States: 0 start; 1 at position 1; 2/3 hold `b` at
position 2; 4/5 hold `b` at position 3; 6/7 hold `d`; 8 halts. -/
def tr2 : TM where
  k := 0
  g := 0
  q := 8
  δ := fun s sym _ =>
    let bit := sym.getD false
    match s.val with
    | 0 => some (1, .right, fun i => i.elim0, some bit)
    | 1 => some (if bit then 3 else 2, .right, fun i => i.elim0, none)
    | 2 => some (4, .right, fun i => i.elim0, some bit)
    | 3 => some (5, .right, fun i => i.elim0, some bit)
    | 4 => some (if bit then 7 else 6, .stay, fun i => i.elim0, some false)
    | 5 => some (if bit then 7 else 6, .stay, fun i => i.elim0, some true)
    | 6 => some (8, .stay, fun i => i.elim0, some false)
    | 7 => some (8, .stay, fun i => i.elim0, some true)
    | _ => none

/-- `tr2` with one idle work tape. -/
def tr2k : TM where
  k := 1
  g := 0
  q := 8
  δ := fun s sym _ =>
    let bit := sym.getD false
    let idle : Fin 1 → Fin 1 × Dir := fun _ => (0, .stay)
    match s.val with
    | 0 => some (1, .right, idle, some bit)
    | 1 => some (if bit then 3 else 2, .right, idle, none)
    | 2 => some (4, .right, idle, some bit)
    | 3 => some (5, .right, idle, some bit)
    | 4 => some (if bit then 7 else 6, .stay, idle, some false)
    | 5 => some (if bit then 7 else 6, .stay, idle, some true)
    | 6 => some (8, .stay, idle, some false)
    | 7 => some (8, .stay, idle, some true)
    | _ => none

end Transpose.Tape.Witness

import Transpose.Statement

/-!
# Sanity checks on the frozen statement (not frozen; may be extended)

These checks confirm that the model in `Statement.lean` behaves as intended,
so that a proof of `LinearTimeTransposable` or its negation cannot come from a
modelling bug.
-/

namespace Transpose.Sanity
open Transpose

/-- Run until halt (with fuel), returning `(steps, output)`. -/
def run (M : TM) (w : List Bool) : Nat → Nat → Config M → Option (Nat × List Bool)
  | 0, _, _ => none
  | fuel + 1, s, c =>
    match step M w c with
    | none => some (s, c.outRev.reverse)
    | some c' => run M w fuel (s + 1) c'

/-- The copy machine: no work tapes, one state, echoes the input to the output. -/
def copyTM : TM where
  k := 0
  g := 0
  q := 0
  δ := fun _ sym _ =>
    match sym with
    | none => none
    | some b => some (0, .right, fun i => i.elim0, some b)

#guard run copyTM [true, false, false, true] 100 0 (init copyTM) == some (4, [true, false, false, true])
#guard run copyTM [] 100 0 (init copyTM) == some (0, [])

/-- A machine with one work tape that writes the input to the work tape, then
walks back and outputs it *reversed*: this exercises the work tapes. -/
def reverseTM : TM where
  k := 1
  g := 2   -- symbols: 0 blank, 1 = bit 0, 2 = bit 1
  q := 1   -- state 0: copying forward; state 1: walking back and outputting
  δ := fun st sym tape =>
    let cur := tape 0
    if st = 0 then
      match sym with
      | some b => some (0, .right, fun _ => (if b then 2 else 1, .right), none)
      | none   => some (1, .stay, fun _ => (cur, .left), none)
    else
      if cur = 0 then none
      else some (1, .stay, fun _ => (cur, .left), some (cur = 2))

#guard (run reverseTM [true, true, false] 100 0 (init reverseTM)).map (·.2) == some [false, true, true]

-- Encoding checks.
#guard entryBits 1 == 1
#guard entryBits 2 == 1
#guard entryBits 3 == 2
#guard entryBits 4 == 2
#guard entryBits 5 == 3
#guard entryBits 8 == 3
#guard entryBits 9 == 4
#guard entryBits 1024 == 10
#guard entryBits 1025 == 11

/-- A 2×2 matrix with 1-bit entries `[[a,b],[c,d]] = [[1,0],[1,1]]`. -/
def A2 : Matrix := fun i j _ => (i, j) != (0, 1)
#guard encode 2 1 A2 == [true, false, true, true]
#guard encode 2 1 (transpose A2) == [true, true, false, true]

/-- 3×3, 2-bit entries: entry (i,j) has bit 0 = (i < j) and bit 1 = (i = 2). -/
def A3 : Matrix := fun i j t => if t = 0 then decide (i < j) else decide (i = 2)
#guard encode 3 2 A3 ==
  [false,false, true,false, true,false,
   false,false, false,false, true,false,
   false,true,  false,true,  false,true]

#guard (List.range 40).all fun n => (encode n (entryBits n) A3).length == inputLength n

/-- Reference implementation of `max(1, ⌈log₂ n⌉)`. -/
def clog (n : Nat) : Nat := Id.run do
  let mut b := 0
  while 2 ^ b < n do b := b + 1
  return max 1 b

#guard (List.range 5000).all fun i => entryBits (i + 1) == clog (i + 1)

-- `L(n)` is strictly increasing, so the machine can recover `n` from the input length.
#guard (List.range 5000).all fun i => inputLength (i + 1) < inputLength (i + 2)

-- Bit `p` of the input is bit `p % b` of entry `(r, c)`, and bit `p` of the output
-- is bit `p % b` of input entry `(c, r)`, where `e = p / b`, `r = e / n`, `c = e % n`.
#guard (List.range 12).all fun i =>
  let n := i + 1; let b := entryBits n
  let w := encode n b A3; let o := encode n b (transpose A3)
  (List.range (n * n * b)).all fun p =>
    let e := p / b
    o[p]? == some (A3 (e % n) (e / n) (p % b)) && w[p]? == some (A3 (e / n) (e % n) (p % b))

theorem length_concatUpTo (f : Nat → List Bool) (l : Nat) (h : ∀ i, (f i).length = l) :
    ∀ m, (concatUpTo f m).length = m * l
  | 0 => by simp [concatUpTo]
  | m + 1 => by
    simp only [concatUpTo, List.length_append, length_concatUpTo f l h m, h, Nat.succ_mul]

/-- The encoding has length exactly `inputLength n`. -/
theorem length_encode (n : Nat) (A : Matrix) :
    (encode n (entryBits n) A).length = inputLength n := by
  unfold encode inputLength
  rw [length_concatUpTo _ (n * entryBits n)]
  · rw [Nat.mul_assoc]
  · intro i
    rw [length_concatUpTo _ (entryBits n)]
    intro j
    rw [length_concatUpTo _ 1]
    · simp
    · intro _; rfl

end Transpose.Sanity

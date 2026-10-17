/-!
# Frozen formal statement — DO NOT MODIFY THIS FILE

Linear-time transposition of an n×n matrix with ⌈log₂ n⌉-bit entries on a
deterministic multitape Turing machine.

The goal of the project is a sorry-free, axiom-free (beyond Lean's standard
`propext`, `Classical.choice`, `Quot.sound`) proof of exactly one of

* `Transpose.LinearTimeTransposable`
* `¬ Transpose.LinearTimeTransposable`

stated as `theorem Transpose.answer` in `Transpose/Answer.lean` and checked by
`Verify.lean`.

This file deliberately depends only on Lean core (no Mathlib), and defines its
own list helpers, so that it compiles unchanged across toolchain updates.
-/

namespace Transpose

/-! ## The machine model -/

/-- Head movement. -/
inductive Dir where
  | left
  | stay
  | right
  deriving DecidableEq, Repr

/-- Apply a head movement to a head position. -/
def Dir.shift : Dir → Int → Int
  | .left,  p => p - 1
  | .stay,  p => p
  | .right, p => p + 1

/-- A deterministic multitape Turing machine with:

* a read-only, two-way input tape holding the input word over `{0,1}` in
  cells `0, …, |w|-1`; every other cell reads as `none` (an end marker);
* `k` read/write work tapes, each two-way infinite, over the finite alphabet
  `Fin (g+1)`, where `0` is the blank symbol;
* a write-only, one-way output tape over `{0,1}`: in each step the machine may
  append at most one bit to the output;
* the finite state set `Fin (q+1)`, with initial state `0`.

In each step, the machine reads its state, the input symbol under the input
head, and the `k` work-tape symbols under the work heads. `δ` then either
returns `none`, meaning the machine halts, or returns:
* the new state,
* the input-head move,
* for each work tape, the symbol to write and the head move,
* optionally, one output bit.

Since all of these types are finite, `δ` is a finite transition table. -/
structure TM where
  /-- number of work tapes -/
  k : Nat
  /-- work alphabet is `Fin (g+1)`, blank = `0` -/
  g : Nat
  /-- state set is `Fin (q+1)`, start state = `0` -/
  q : Nat
  /-- transition function; `none` = halt -/
  δ : Fin (q + 1) → Option Bool → (Fin k → Fin (g + 1)) →
      Option (Fin (q + 1) × Dir × (Fin k → Fin (g + 1) × Dir) × Option Bool)

/-- Instantaneous description of a machine. -/
structure Config (M : TM) where
  state   : Fin (M.q + 1)
  inPos   : Int
  work    : Fin M.k → Int → Fin (M.g + 1)
  workPos : Fin M.k → Int
  /-- output written so far, **most recent bit first** -/
  outRev  : List Bool

/-- The `i`-th element of a list, if any. -/
def nth : List Bool → Nat → Option Bool
  | [],      _     => none
  | b :: _,  0     => some b
  | _ :: bs, i + 1 => nth bs i

/-- Symbol under the input head at position `p` (`none` outside the input). -/
def readInput (w : List Bool) (p : Int) : Option Bool :=
  if p < 0 then none else nth w p.toNat

/-- Initial configuration: state `0`, all heads at cell `0`, work tapes blank,
empty output. -/
def init (M : TM) : Config M where
  state   := 0
  inPos   := 0
  work    := fun _ _ => 0
  workPos := fun _ => 0
  outRev  := []

/-- One step on input `w`; `none` if the machine halts in configuration `c`. -/
def step (M : TM) (w : List Bool) (c : Config M) : Option (Config M) :=
  match M.δ c.state (readInput w c.inPos) (fun i => c.work i (c.workPos i)) with
  | none => none
  | some (s, d, acts, o) =>
    some
      { state   := s
        inPos   := d.shift c.inPos
        work    := fun i p => if p = c.workPos i then (acts i).1 else c.work i p
        workPos := fun i => (acts i).2.shift (c.workPos i)
        outRev  := match o with
                   | none   => c.outRev
                   | some b => b :: c.outRev }

/-- Run exactly `n` steps (failing with `none` if the machine halts earlier). -/
def stepN (M : TM) (w : List Bool) : Nat → Config M → Option (Config M)
  | 0,     c => some c
  | n + 1, c =>
    match step M w c with
    | none    => none
    | some c' => stepN M w n c'

/-- On input `w`, `M` halts after at most `t` steps with output exactly `out`. -/
def ComputesWithin (M : TM) (w out : List Bool) (t : Nat) : Prop :=
  ∃ s, s ≤ t ∧ ∃ c, stepN M w s (init M) = some c ∧
    step M w c = none ∧ c.outRev.reverse = out

/-! ## Matrices and their encoding -/

/-- Entry width `b(n) = max(1, ⌈log₂ n⌉)`. For `n ≥ 2` this equals
`⌈log₂ n⌉ = ⌊log₂ (n-1)⌋ + 1`. -/
def entryBits (n : Nat) : Nat := Nat.log2 (n - 1) + 1

/-- `concatUpTo f m = f 0 ++ f 1 ++ ⋯ ++ f (m-1)`. -/
def concatUpTo (f : Nat → List Bool) : Nat → List Bool
  | 0     => []
  | m + 1 => concatUpTo f m ++ f m

/-- A matrix is given by its bits: `A i j t` is bit `t` of entry `(i, j)`.
Only `i, j < n` and `t < b` are ever read. -/
abbrev Matrix := Nat → Nat → Nat → Bool

/-- Row-major encoding of the `n × n` matrix `A` with `b`-bit entries:
`n²` consecutive fixed-width blocks of `b` bits, no delimiters. The order is
entry `(0,0), (0,1), …, (0,n-1), (1,0), …`, and within an entry, bit `0` first. -/
def encode (n b : Nat) (A : Matrix) : List Bool :=
  concatUpTo (fun i => concatUpTo (fun j => concatUpTo (fun t => [A i j t]) b) n) n

/-- The transpose. -/
def transpose (A : Matrix) : Matrix := fun i j t => A j i t

/-- Input length for size `n`: `L(n) = n² · b(n)` (equal to the length of `encode`). -/
def inputLength (n : Nat) : Nat := n * n * entryBits n

/-! ## The statement -/

/-- Machine `M` transposes every `n × n` matrix with `b(n)`-bit entries
(`n ≥ 1`) within `T(L)` steps, where `L = n² b(n)` is the input length. -/
def TransposesWithin (M : TM) (T : Nat → Nat) : Prop :=
  ∀ n, 1 ≤ n → ∀ A : Matrix,
    ComputesWithin M (encode n (entryBits n) A)
      (encode n (entryBits n) (transpose A)) (T (inputLength n))

/-- **Statement (T).** Some deterministic multitape Turing machine transposes
`n × n` matrices with `⌈log₂ n⌉`-bit entries in time `O(L)`. -/
def LinearTimeTransposable : Prop :=
  ∃ (M : TM) (c : Nat), TransposesWithin M (fun L => c * (L + 1))

end Transpose

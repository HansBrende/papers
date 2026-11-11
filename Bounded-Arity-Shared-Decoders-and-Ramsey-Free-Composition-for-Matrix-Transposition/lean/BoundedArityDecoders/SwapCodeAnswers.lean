import SwapRigidity.Flag
import SwapRigidity.ClassUniform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Formal Specifications — Two Bonus Answers to Concrete Questions in Paper 17

Statement-only formal specifications of both bonus results in `README.md` (§II Bonus Answers
and §III.3):

1. **Direct Answer to Paper 17 `Remark 5.6` (*"We have no three-term example for `d ≥ 5`"*)**:
   * `threeTermBlockA`, `threeTermBlockB`: explicit 3-Kronecker-term family
     `K_{3 m} = (sw_3 - Π_3) ⊗ (I_m ⊗ I_m)` on `Fin (3 * m)`.
   * `IsThreeByThreeSymmetricZeroTraceBlocks` & `Bonus1_ThreeTermBlockSwapCodeDimSpec`: over
     **every** field `F` and every `m ≥ 1`, `SwapRigidity.swapCode (threeTermBlockA F m) (threeTermBlockB F m)`
     consists precisely of `3 × 3` block matrices of `m × m` symmetric blocks whose three
     diagonal blocks sum to `0` (`X_{00} + X_{11} + X_{22} = 0`), of exact dimension
     `4 * m * (m + 1)` — strictly exceeding `d * (d + 1) / 2` (`d = 3 m`) at `m = 1, 2, 3, 4`
     (`d = 3: 8 > 6`, `d = 6: 24 > 21`, `d = 9: 48 > 45`, `d = 12: 80 > 78`).
   * `threeTermPaddedA`, `threeTermPaddedB`, `Bonus1_ThreeTermPaddedSevenAndFiveSpec`, &
     `OpenQuestion_ThreeTermDimFiveExceedsPairingSpec`: padded-`6` at `d = 7` achieves
     `finrank = 29 > 28` over every field `F`, padded-`3` at `d = 4` achieves `11 > 10`, and
     padded-`3` at `d = 5` gives `15 = 15` (leaving open whether any 3-term operator at `d = 5`
     exceeds `15`).

2. **Exact Dichotomy on Paper 17 `Problem 9.3` (*Both sides, all scales*)**:
   * `IsAlignedDyadicInterval`, `IsCyclicInterval`, `InAlignedDyadicIntervalRotSpan`, &
     `InMultiscaleIntervalRotSpan`: aligned dyadic intervals and general cyclic intervals of
     length `2^m / 2^(j + 1)` at scales `1 ≤ j + 1 ≤ m` (plus whole-cycle scale `0`).
   * `Bonus2_MultiscaleIntervalBothSidesSpec`: when both `A_a` and `B_a` on `d = 2^m` lie in
     the multi-scale interval-rotation spans (whether aligned dyadic or general cyclic),
     `2 * finrank F (SwapRigidity.swapCode A B) ≤ d^2 + d * min (max 1 (2 * ∑ j, M_A j)) (max 1 (2 * ∑ j, M_B j))`.
   * `Bonus2_MultiscaleFullProfileAttainsFullSwapSpec`: the full aligned dyadic profile
     `M_full j = 2^(j + 1)` (`∑_{j=1}^m 2^j ≥ d` for `m ≥ 1`) reaches full swap dimension `d^2`.
   * `OpenTarget_MultiscalePeriodicWalshSwapCodeSpec` &
     `OpenTarget_MultiscalePeriodicWalshProfileSpec`: the genuinely open all-scale periodic
     Rademacher/Walsh dyadic-mask regime where all `m = log₂ d` scales act simultaneously on both
     sides (each scale-`j` mask having `2^(j + 1)` cyclic boundaries rather than `2`).
-/

namespace BoundedArityDecoders

open Module
open scoped BigOperators

section Bonus1Defs

/-- Ordered pairs `(0, 1)`, `(0, 2)`, `(1, 2)` indexing the 3 Kronecker terms of `sw_3 - Π_3`. -/
def threeTermPair : Fin 3 → Nat × Nat
  | ⟨0, _⟩ => (0, 1)
  | ⟨1, _⟩ => (0, 2)
  | ⟨2, _⟩ => (1, 2)

/-- First Kronecker factors `A_t = (E_{i_t, j_t} - E_{j_t, i_t}) ⊗ I_m` on `Fin (3 * m)` (`m ≥ 1`). -/
def threeTermBlockA (F : Type*) [Ring F] (m : ℕ) [NeZero m] (t : Fin 3) :
    Matrix (Fin (3 * m)) (Fin (3 * m)) F :=
  let (i₀, j₀) := threeTermPair t
  Matrix.of fun r c =>
    if r.val % m = c.val % m then
      if r.val / m = i₀ ∧ c.val / m = j₀ then (1 : F)
      else if r.val / m = j₀ ∧ c.val / m = i₀ then (-1 : F)
      else 0
    else 0

/-- Second Kronecker factors `B_t = (E_{j_t, i_t} - E_{i_t, j_t}) ⊗ I_m = - A_t` on `Fin (3 * m)`. -/
def threeTermBlockB (F : Type*) [Ring F] (m : ℕ) [NeZero m] (t : Fin 3) :
    Matrix (Fin (3 * m)) (Fin (3 * m)) F :=
  - threeTermBlockA F m t

/-- Explicit block-matrix characterization of `ker(sw_{3 m} - K_{3 m})` (`README.md` §II Bonus 1):
when partitioned into a `3 × 3` grid of `m × m` blocks `X_{i, j}` (`i, j ∈ Fin 3`), every block
`X_{i, j}` is symmetric (`(X_{i, j})_{u, v} = (X_{i, j})_{v, u}`) and the three diagonal blocks
have zero sum (`X_{0, 0} + X_{1, 1} + X_{2, 2} = 0`). -/
def IsThreeByThreeSymmetricZeroTraceBlocks (m : ℕ) [NeZero m] {F : Type*} [AddMonoid F]
    (X : Matrix (Fin (3 * m)) (Fin (3 * m)) F) : Prop :=
  let h3m : 0 < 3 * m := Nat.mul_pos (Nat.succ_pos 2) (NeZero.pos m)
  let blkIdx (b : ℕ) (u : Fin m) : Fin (3 * m) := ⟨(b * m + u.val) % (3 * m), Nat.mod_lt _ h3m⟩
  (∀ (i j : Fin 3) (u v : Fin m),
    X (blkIdx i.val u) (blkIdx j.val v) = X (blkIdx i.val v) (blkIdx j.val u)) ∧
  (∀ u v : Fin m,
    X (blkIdx 0 u) (blkIdx 0 v) + X (blkIdx 1 u) (blkIdx 1 v) + X (blkIdx 2 u) (blkIdx 2 v) = 0)

/-- Padded `3 m`-construction embedded into `Fin d`: top-left `(3 m) × (3 m)` carries
`threeTermBlockA F m`, and term `t = 2` carries identity `1` on tail diagonal indices `r ≥ 3 m`. -/
def threeTermPaddedA (F : Type*) [Ring F] (m d : ℕ) [NeZero m] (t : Fin 3) :
    Matrix (Fin d) (Fin d) F :=
  let (i₀, j₀) := threeTermPair t
  Matrix.of fun r c =>
    if r.val < 3 * m ∧ c.val < 3 * m then
      if r.val % m = c.val % m then
        if r.val / m = i₀ ∧ c.val / m = j₀ then (1 : F)
        else if r.val / m = j₀ ∧ c.val / m = i₀ then (-1 : F)
        else 0
      else 0
    else if t.val = 2 ∧ 3 * m ≤ r.val ∧ r.val = c.val then (1 : F)
    else 0

/-- Second Kronecker factors for `threeTermPaddedA`: negated on `< 3 m`, `+1` on tail `r ≥ 3 m`
in term `t = 2`. -/
def threeTermPaddedB (F : Type*) [Ring F] (m d : ℕ) [NeZero m] (t : Fin 3) :
    Matrix (Fin d) (Fin d) F :=
  let (i₀, j₀) := threeTermPair t
  Matrix.of fun r c =>
    if r.val < 3 * m ∧ c.val < 3 * m then
      if r.val % m = c.val % m then
        if r.val / m = j₀ ∧ c.val / m = i₀ then (1 : F)
        else if r.val / m = i₀ ∧ c.val / m = j₀ then (-1 : F)
        else 0
      else 0
    else if t.val = 2 ∧ 3 * m ≤ r.val ∧ r.val = c.val then (1 : F)
    else 0

end Bonus1Defs

section Bonus2Defs

/-- A subset `I : Finset (Fin d)` (`d ≥ 1`) is a cyclic interval of length `len` if
`I = {(start + u) mod d : 0 ≤ u < len}` for some `start : Fin d`. -/
def IsCyclicInterval {d : ℕ} [NeZero d] (len : ℕ) (I : Finset (Fin d)) : Prop :=
  ∃ start : Fin d,
    I = (Finset.range len).image (fun u =>
      ⟨(start.val + u) % d, Nat.mod_lt _ (NeZero.pos d)⟩)

/-- A subset `I : Finset (Fin (2^m))` is an **aligned dyadic interval** at proper scale
`j : Fin m` (corresponding to scale `j' = j + 1 ∈ {1, …, m}`, length `2^m / 2^(j + 1) =
2^(m - 1 - j)`) if `I = [blk * 2^(m - 1 - j), (blk + 1) * 2^(m - 1 - j))` for some
`blk : Fin (2^(j + 1))`. -/
def IsAlignedDyadicInterval {m : ℕ} (j : Fin m) (I : Finset (Fin (2 ^ m))) : Prop :=
  let len := 2 ^ (m - 1 - j.val)
  ∃ blk : Fin (2 ^ (j.val + 1)),
    I = (Finset.range len).image (fun u =>
      ⟨(blk.val * len + u) % (2 ^ m), Nat.mod_lt _ (Nat.two_pow_pos m)⟩)

/-- Matrix `P_I * σ^s` on `Fin d`: cyclic rotation by `s` followed by diagonal mask of `I`. -/
def intervalMaskRotMatrix (F : Type*) [Semiring F] {d : ℕ} [NeZero d]
    (I : Finset (Fin d)) (s : Fin d) : Matrix (Fin d) (Fin d) F :=
  Matrix.of fun r c =>
    if r ∈ I ∧ c.val = (r.val + s.val) % d then (1 : F) else 0

/-- Family `M` lies in the span of **aligned dyadic interval** masks composed with rotations
using at most `profile j` aligned dyadic intervals of length `2^(m - 1 - j)` at each scale
`j : Fin m` (plus full-cycle rotations at scale `0`). -/
def InAlignedDyadicIntervalRotSpan {F : Type*} [Field F] {m : ℕ} {α : Type*}
    (profile : Fin m → ℕ)
    (M : α → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F) : Prop :=
  haveI : NeZero (2 ^ m) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos m)⟩
  ∃ (intervals : ∀ j : Fin m, Fin (profile j) → Finset (Fin (2 ^ m))),
    (∀ (j : Fin m) (i : Fin (profile j)),
      IsAlignedDyadicInterval j (intervals j i)) ∧
    ∀ a : α, M a ∈ Submodule.span F
      ({X | ∃ s : Fin (2 ^ m), X = intervalMaskRotMatrix F Finset.univ s} ∪
       {X | ∃ (j : Fin m) (i : Fin (profile j)) (s : Fin (2 ^ m)),
              X = intervalMaskRotMatrix F (intervals j i) s})

/-- Family `M` lies in the span of multi-scale cyclic-interval masks composed with rotations
using at most `profile j` cyclic intervals of length `2^(m - 1 - j)` at each proper scale
`j : Fin m` (plus full-cycle rotations at scale `0`). -/
def InMultiscaleIntervalRotSpan {F : Type*} [Field F] {m : ℕ} {α : Type*}
    (profile : Fin m → ℕ)
    (M : α → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F) : Prop :=
  haveI : NeZero (2 ^ m) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos m)⟩
  ∃ (intervals : ∀ j : Fin m, Fin (profile j) → Finset (Fin (2 ^ m))),
    (∀ (j : Fin m) (i : Fin (profile j)),
      IsCyclicInterval (2 ^ (m - 1 - j.val)) (intervals j i)) ∧
    ∀ a : α, M a ∈ Submodule.span F
      ({X | ∃ s : Fin (2 ^ m), X = intervalMaskRotMatrix F Finset.univ s} ∪
       {X | ∃ (j : Fin m) (i : Fin (profile j)) (s : Fin (2 ^ m)),
              X = intervalMaskRotMatrix F (intervals j i) s})

/-- Periodic Rademacher/Walsh dyadic digit mask at bit `j : Fin m` and bit value `bit : Bool`
composed with rotation `s` on `Fin (2^m)` (having `2^(j + 1)` cyclic boundaries). -/
def walshDigitMaskRotMatrix (F : Type*) [Semiring F] {m : ℕ}
    (j : Fin m) (bit : Bool) (s : Fin (2 ^ m)) : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F :=
  Matrix.of fun r c =>
    let rBit := ((r.val / (2 ^ (m - 1 - j.val))) % 2 == 1)
    if rBit = bit ∧ c.val = (r.val + s.val) % (2 ^ m) then (1 : F) else 0

/-- A subset `S : Finset (Fin (2^m))` is a **periodic scale-`j` dyadic mask** (`j : Fin m`,
representing scale `j' = j + 1 ∈ {1, …, m}`) if membership in `S` depends only on the block
index `(r / 2^(m - 1 - j)) mod 2` up to cyclic shift — so `S` has period `2^(m - j)` and at
most `2^(j + 1)` cyclic boundaries (`README.md` §II Bonus 2 line 121). -/
def IsPeriodicScaleDyadicMask {m : ℕ} (j : Fin m) (S : Finset (Fin (2 ^ m))) : Prop :=
  let period := 2 ^ (m - j.val)
  let halfPeriod := 2 ^ (m - 1 - j.val)
  ∃ phase : Fin (2 ^ m),
    ∀ r : Fin (2 ^ m),
      r ∈ S ↔ (((r.val + phase.val) % period) < halfPeriod)

/-- Family `M` lies in the span of periodic scale-`j` dyadic masks composed with rotations using
at most `profile j` periodic masks at each scale `j : Fin m` (plus full-cycle rotations). -/
def InMultiscalePeriodicDyadicRotSpan {F : Type*} [Field F] {m : ℕ} {α : Type*}
    (profile : Fin m → ℕ)
    (M : α → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F) : Prop :=
  haveI : NeZero (2 ^ m) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos m)⟩
  ∃ (masks : ∀ j : Fin m, Fin (profile j) → Finset (Fin (2 ^ m))),
    (∀ (j : Fin m) (i : Fin (profile j)),
      IsPeriodicScaleDyadicMask j (masks j i)) ∧
    ∀ a : α, M a ∈ Submodule.span F
      ({X | ∃ s : Fin (2 ^ m), X = intervalMaskRotMatrix F Finset.univ s} ∪
       {X | ∃ (j : Fin m) (i : Fin (profile j)) (s : Fin (2 ^ m)),
              X = intervalMaskRotMatrix F (masks j i) s})

end Bonus2Defs

/-! ### Formal Claim Specifications (No Proofs Yet) -/

/-- **Bonus 1A (`README.md` §II Bonus 1 — Explicit 3-Term Kronecker Family Answering `Remark 5.6`).**
Over **every** field `F` and every `m ≥ 1`:
1. `X ∈ SwapRigidity.swapCode (threeTermBlockA F m) (threeTermBlockB F m)` holds **if and only if**
   `X` satisfies `IsThreeByThreeSymmetricZeroTraceBlocks m X` (every `m × m` block `X_{i, j}` is
   symmetric and `X_{0, 0} + X_{1, 1} + X_{2, 2} = 0`);
2. `finrank F (SwapRigidity.swapCode (threeTermBlockA F m) (threeTermBlockB F m)) = 4 * m * (m + 1)`,
   strictly exceeding the pairing bound `(3 * m) * (3 * m + 1) / 2` for `m ∈ {1, 2, 3, 4}`
   (`d = 3, 6, 9, 12`, giving `8 > 6`, `24 > 21`, `48 > 45`, `80 > 78` in every characteristic). -/
def Bonus1_ThreeTermBlockSwapCodeDimSpec : Prop :=
  (∀ (F : Type*) [Field F] (m : ℕ) [NeZero m],
    (∀ X : Matrix (Fin (3 * m)) (Fin (3 * m)) F,
      X ∈ SwapRigidity.swapCode (threeTermBlockA F m) (threeTermBlockB F m) ↔
        IsThreeByThreeSymmetricZeroTraceBlocks m X) ∧
    finrank F (SwapRigidity.swapCode (threeTermBlockA F m) (threeTermBlockB F m)) =
      4 * m * (m + 1)) ∧
  (∀ m ∈ ({1, 2, 3, 4} : Finset ℕ), (3 * m) * (3 * m + 1) / 2 < 4 * m * (m + 1))

/-- **Bonus 1B (`README.md` §II Bonus 1 — Padded Dimensions `d = 4, 5, 7` Over Every Field).**
Over every field `F`:
* Padded-`6` (`m = 2`) at `d = 7` achieves `finrank = 29 > 28 = 7 * 8 / 2`;
* Padded-`3` (`m = 1`) at `d = 4` achieves `finrank = 11 > 10 = 4 * 5 / 2`;
* Padded-`3` (`m = 1`) at `d = 5` achieves `finrank = 15 = 5 * 6 / 2`. -/
def Bonus1_ThreeTermPaddedSevenAndFiveSpec : Prop :=
  ∀ (F : Type*) [Field F],
    finrank F (SwapRigidity.swapCode (threeTermPaddedA F 2 7) (threeTermPaddedB F 2 7)) = 29 ∧
    finrank F (SwapRigidity.swapCode (threeTermPaddedA F 1 4) (threeTermPaddedB F 1 4)) = 11 ∧
    finrank F (SwapRigidity.swapCode (threeTermPaddedA F 1 5) (threeTermPaddedB F 1 5)) = 15

/-- **Open Question at `d = 5` (`README.md` §II Bonus 1 Line 117 — *"Curiously, `d = 5` remains
untouched at `15 = 15`!"*).**
Whether any 3-Kronecker-term operator on `5 × 5` matrices over any field `F` exceeds the pairing
bound `5 * 6 / 2 = 15`. -/
def OpenQuestion_ThreeTermDimFiveExceedsPairingSpec : Prop :=
  ∃ (F : Type) (_ : Field F) (A B : Fin 3 → Matrix (Fin 5) (Fin 5) F),
    15 < finrank F (SwapRigidity.swapCode A B)

/-- **Bonus 2A (`README.md` §II Bonus 2 — Exact Resolution of Literal `Problem 9.3`).**
Over any field `F`, on `d = 2^m`:
1. Every aligned dyadic interval-rotation family (`InAlignedDyadicIntervalRotSpan`) is a
   multi-scale cyclic-interval family (`InMultiscaleIntervalRotSpan`);
2. Whenever `A` and `B` lie in the multi-scale interval-rotation spans with profiles
   `M_A, M_B : Fin m → ℕ`,
   `2 * finrank F (SwapRigidity.swapCode A B) ≤ d^2 + d * min (max 1 (2 * ∑ j, M_A j)) (max 1 (2 * ∑ j, M_B j))`. -/
def Bonus2_MultiscaleIntervalBothSidesSpec : Prop :=
  ∀ (F : Type*) [Field F] (m : ℕ) (α : Type*) [Fintype α]
    (M_A M_B : Fin m → ℕ)
    (A B : α → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F),
    (InAlignedDyadicIntervalRotSpan M_A A → InMultiscaleIntervalRotSpan M_A A) ∧
    (InMultiscaleIntervalRotSpan M_A A →
      InMultiscaleIntervalRotSpan M_B B →
      2 * finrank F (SwapRigidity.swapCode A B) ≤
        (2 ^ m) ^ 2 +
          (2 ^ m) * min (max 1 (2 * ∑ j : Fin m, M_A j)) (max 1 (2 * ∑ j : Fin m, M_B j)))

/-- **Bonus 2B (`README.md` §II Bonus 2 — Full Aligned Dyadic Profile Attains Full Swap `d^2`).**
Over any field `F` and `d = 2^m`, with the full dyadic profile `M_full j = 2^(j + 1)`
(satisfying `∑_{j : Fin m} 2^(j + 1) ≥ 2^m` for all `m ≥ 1`), there exists a finite family `A, B`
in the **aligned** dyadic interval-rotation span whose swap code has full dimension `(2^m)^2`. -/
def Bonus2_MultiscaleFullProfileAttainsFullSwapSpec : Prop :=
  ∀ (F : Type*) [Field F] (m : ℕ),
    let fullProfile : Fin m → ℕ := fun j => 2 ^ (j.val + 1)
    (1 ≤ m → 2 ^ m ≤ ∑ j : Fin m, fullProfile j) ∧
    ∃ (α : Type) (_ : Fintype α)
      (A B : α → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F),
      InAlignedDyadicIntervalRotSpan fullProfile A ∧
      InAlignedDyadicIntervalRotSpan fullProfile B ∧
      finrank F (SwapRigidity.swapCode A B) = (2 ^ m) ^ 2

/-- **Open Multi-Scale Target — All-Scale Rademacher/Walsh Digit Span (`README.md` §II Bonus 2).**
When **all `m = log₂ d` periodic Rademacher/Walsh digit scales act simultaneously on both sides**
(each scale-`j` mask having `2^(j + 1)` cyclic boundaries rather than `2`, so the joint class
refinement has `2^m = d` singleton atoms and one-sided class bounds are vacuous, yet the per-side
operator span has dimension only `(m + 1) * 2^m ≪ 4^m`), does a uniform constant `c_walsh < 1`
bound `finrank F (SwapRigidity.swapCode A B) ≤ c_walsh * (2^m)^2` for all sufficiently large `m`? -/
def OpenTarget_MultiscalePeriodicWalshSwapCodeSpec : Prop :=
  ∃ (c_walsh : ℝ) (M₀ : ℕ), c_walsh < 1 ∧
    ∀ (F : Type*) [Field F] (m : ℕ) (α : Type*) [Fintype α]
      (A B : α → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F),
      M₀ ≤ m →
      (∀ a, A a ∈ Submodule.span F
        {X | ∃ (j : Fin m) (bit : Bool) (sh : Fin (2 ^ m)),
              X = walshDigitMaskRotMatrix F j bit sh}) →
      (∀ a, B a ∈ Submodule.span F
        {X | ∃ (j : Fin m) (bit : Bool) (sh : Fin (2 ^ m)),
              X = walshDigitMaskRotMatrix F j bit sh}) →
      (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤ c_walsh * (((2 ^ m : ℕ) : ℝ) ^ 2)

/-- **Open Multi-Scale Target — Sublinear Periodic Dyadic Mask Profiles (`README.md` §II Bonus 2).**
More generally, when `A` and `B` lie in `InMultiscalePeriodicDyadicRotSpan M_A` and
`InMultiscalePeriodicDyadicRotSpan M_B` with sublinear total mask count
`min (∑ j, M_A j) (∑ j, M_B j) ≤ δ * 2^m` (where each scale-`j` periodic mask has `2^(j + 1)`
boundaries rather than `2`), is `finrank F (SwapRigidity.swapCode A B) ≤ c_walsh * (2^m)^2`
bounded strictly away from `d^2`? -/
def OpenTarget_MultiscalePeriodicWalshProfileSpec : Prop :=
  ∃ (c_walsh δ : ℝ) (M₀ : ℕ), c_walsh < 1 ∧ 0 < δ ∧
    ∀ (F : Type*) [Field F] (m : ℕ) (α : Type*) [Fintype α]
      (M_A M_B : Fin m → ℕ)
      (A B : α → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F),
      M₀ ≤ m →
      InMultiscalePeriodicDyadicRotSpan M_A A →
      InMultiscalePeriodicDyadicRotSpan M_B B →
      ((min (∑ j : Fin m, M_A j) (∑ j : Fin m, M_B j) : ℕ) : ℝ) ≤ δ * ((2 ^ m : ℕ) : ℝ) →
      (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤ c_walsh * (((2 ^ m : ℕ) : ℝ) ^ 2)

end BoundedArityDecoders

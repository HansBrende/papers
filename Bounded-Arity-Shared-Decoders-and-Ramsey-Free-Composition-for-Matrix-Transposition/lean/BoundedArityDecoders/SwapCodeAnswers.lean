import SwapRigidity.Flag
import SwapRigidity.ClassUniform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Formal Specifications — Two Bonus Answers to Concrete Questions in Paper 17

Statement-only formal specifications of both bonus results in `README.md` (§II Bonus Answers
and §III.3):

1. **Direct Answer to Paper 17 `Remark 4.6` (*"We have no three-term example for `d ≥ 5`"*)**:
   * `threeTermBlockA`, `threeTermBlockB`: explicit 3-Kronecker-term family
     `K_{3 m} = (sw_3 - Π_3) ⊗ (I_m ⊗ I_m)` on `Fin (3 * m)`.
   * `Bonus1_ThreeTermBlockSwapCodeDimSpec`: over **every** field `F` and every `m ≥ 1`,
     `finrank F (SwapRigidity.swapCode (threeTermBlockA F m) (threeTermBlockB F m)) = 4 * m * (m + 1)`,
     strictly exceeding `d * (d + 1) / 2` (`d = 3 m`) at `m = 1, 2, 3, 4`
     (`d = 3: 8 > 6`, `d = 6: 24 > 21`, `d = 9: 48 > 45`, `d = 12: 80 > 78`).
   * `threeTermPaddedSevenA`, `threeTermPaddedSevenB` & `Bonus1_ThreeTermPaddedSevenAndFiveSpec`:
     padded-`6` at `d = 7` achieves `finrank = 29 > 28` over every field `F`, while padded-`3`
     at `d = 4` gives `11 > 10` and at `d = 5` gives `15 = 15`.

2. **Exact Dichotomy on Paper 17 `Problem 9.3` (*Both sides, all scales*)**:
   * `Bonus2_MultiscaleIntervalBothSidesSpec`: when both `A_a` and `B_a` on `d = 2^m` lie in
     the spans of cyclic-interval masks (at most `M_A j` resp. `M_B j` proper dyadic intervals
     at scales `1 ≤ j ≤ m`, plus whole-cycle scale `0`) composed with rotations,
     `2 * finrank F (SwapRigidity.swapCode A B) ≤ d^2 + d * min (max 1 (2 * ∑ j, M_A j)) (max 1 (2 * ∑ j, M_B j))`.
   * `Bonus2_MultiscaleFullProfileAttainsFullSwapSpec`: the folklore full dyadic profile reaches
     full dimension `d^2`.
   * `OpenTarget_MultiscalePeriodicWalshSwapCodeSpec`: the periodic Rademacher/Walsh dyadic-mask
     formulation where each mask at scale `j` has `2^j` boundaries rather than `2`.
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

/-- Matrix `P_I * σ^s` on `Fin d`: cyclic rotation by `s` followed by diagonal mask of `I`. -/
def intervalMaskRotMatrix (F : Type*) [Semiring F] {d : ℕ} [NeZero d]
    (I : Finset (Fin d)) (s : Fin d) : Matrix (Fin d) (Fin d) F :=
  Matrix.of fun r c =>
    if r ∈ I ∧ c.val = (r.val + s.val) % d then (1 : F) else 0

/-- Family of matrices `M : α → Matrix (Fin (2^m)) (Fin (2^m)) F` lies in the span of
multi-scale dyadic interval masks composed with rotations using at most `profile j` intervals
of length `2^m / 2^(j + 1)` at each proper scale `j : Fin m` (plus full-cycle rotations at
scale `0`). -/
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

end Bonus2Defs

/-! ### Formal Claim Specifications (No Proofs Yet) -/

/-- **Bonus 1A (`README.md` §II Bonus 1 — Explicit 3-Term Kronecker Family Answering `Remark 4.6`).**
Over **every** field `F` and every `m ≥ 1`, the 3-term operator `(threeTermBlockA F m, threeTermBlockB F m)`
on `Fin (3 * m)` has exact swap-code dimension `4 * m * (m + 1)` — strictly exceeding the
pairing bound `(3 * m) * (3 * m + 1) / 2` for `m ∈ {1, 2, 3, 4}` (`d = 3, 6, 9, 12`, giving
`8 > 6`, `24 > 21`, `48 > 45`, `80 > 78` in every characteristic). -/
def Bonus1_ThreeTermBlockSwapCodeDimSpec : Prop :=
  (∀ (F : Type*) [Field F] (m : ℕ) [NeZero m],
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

/-- **Bonus 2A (`README.md` §II Bonus 2 — Exact Resolution of Literal `Problem 9.3`).**
Over any field `F`, on `d = 2^m`, if `A` and `B` lie in the multi-scale dyadic interval-rotation
spans with profiles `M_A, M_B : Fin m → ℕ`, then
`2 * finrank F (SwapRigidity.swapCode A B) ≤ d^2 + d * min (max 1 (2 * ∑ j, M_A j)) (max 1 (2 * ∑ j, M_B j))`. -/
def Bonus2_MultiscaleIntervalBothSidesSpec : Prop :=
  ∀ (F : Type*) [Field F] (m : ℕ) (α : Type*) [Fintype α]
    (M_A M_B : Fin m → ℕ)
    (A B : α → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F),
    InMultiscaleIntervalRotSpan M_A A →
    InMultiscaleIntervalRotSpan M_B B →
    2 * finrank F (SwapRigidity.swapCode A B) ≤
      (2 ^ m) ^ 2 +
        (2 ^ m) * min (max 1 (2 * ∑ j : Fin m, M_A j)) (max 1 (2 * ∑ j : Fin m, M_B j))

/-- **Bonus 2B (`README.md` §II Bonus 2 — Full Dyadic Profile Attains Full Swap `d^2`).**
Over any field `F` and `d = 2^m`, with the full dyadic profile `M_full j = 2^(j + 1)`, there
exists a finite family `A, B` in the multi-scale dyadic interval-rotation span whose swap code
has full dimension `(2^m)^2`. -/
def Bonus2_MultiscaleFullProfileAttainsFullSwapSpec : Prop :=
  ∀ (F : Type*) [Field F] (m : ℕ),
    let fullProfile : Fin m → ℕ := fun j => 2 ^ (j.val + 1)
    ∃ (α : Type) (_ : Fintype α)
      (A B : α → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F),
      InMultiscaleIntervalRotSpan fullProfile A ∧
      InMultiscaleIntervalRotSpan fullProfile B ∧
      finrank F (SwapRigidity.swapCode A B) = (2 ^ m) ^ 2

/-- **Open Multi-Scale Target (`README.md` §II Bonus 2 Final Sentence — Periodic Walsh Masks).**
Bounding `finrank F (SwapRigidity.swapCode A B)` when `A_a, B_a` lie in the span of at most
`s` periodic Rademacher/Walsh digit masks `walshDigitMaskRotMatrix` composed with rotations
(where each scale-`j` periodic mask has `2^(j + 1)` boundaries rather than `2`). -/
def OpenTarget_MultiscalePeriodicWalshSwapCodeSpec : Prop :=
  ∀ (s : ℕ), ∃ (c_walsh : ℝ), c_walsh < 1 ∧ ∃ M₀ : ℕ,
    ∀ (F : Type*) [Field F] (m : ℕ) (α : Type*) [Fintype α]
      (scalesA scalesB : Finset (Fin m))
      (A B : α → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F),
      M₀ ≤ m →
      scalesA.card ≤ s →
      scalesB.card ≤ s →
      (∀ a, A a ∈ Submodule.span F
        {X | ∃ j ∈ scalesA, ∃ (bit : Bool) (sh : Fin (2 ^ m)),
              X = walshDigitMaskRotMatrix F j bit sh}) →
      (∀ a, B a ∈ Submodule.span F
        {X | ∃ j ∈ scalesB, ∃ (bit : Bool) (sh : Fin (2 ^ m)),
              X = walshDigitMaskRotMatrix F j bit sh}) →
      (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤ c_walsh * (((2 ^ m : ℕ) : ℝ) ^ 2)

end BoundedArityDecoders

import SwapRigidity.Entry
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness

/-!
# Entry rules with advice, over a finite field

An *advice* is any map `w` from matrices to a finite set `Ω`.  A subspace `𝒳` is a code of the
entry rules `a ω` with advice `w` (`IsEntryRuleCodeWithAdvice`) if, on the matrices of `𝒳` with
`w X = ω`, every entry obeys the entry rule `a ω` up to an offset that may depend on `ω` and on
the entry.  So the value of the advice may select the functionals of all entries and add a
constant to each of them.

* `IsEntryRuleCodeWithAdvice.natCard_fiber_le`: if every rule `a ω` changes, from one row to the
  next, at no more than `E` entries, the matrices of the code that share a value of the advice
  number at most `|F| ^ ((n ^ 2 + n + E) / 2)`.
* `IsEntryRuleCodeWithAdvice.natCard_pow_two_mul_finrank_le`: then
  `|F| ^ (2 * dim 𝒳) ≤ |Ω| ^ 2 * |F| ^ (n ^ 2 + n + E)`.

The counting argument is that of the memo to this paper (its theorem
`IsCodeWithAnyAdvice.natCard_pow_finrank_le` for class-uniform rules); here it is combined with
`IsEntryRuleCode.two_mul_finrank_le_of_changes`.
-/

namespace SwapRigidity

open Module

variable {F : Type*} [Field F] {n : ℕ} {Ω : Type*}

/-- The matrices that satisfy the entry rule `a`: the largest code of the rule. -/
def entryRuleSpace (a : ZMod n → ZMod n → (Matrix (ZMod n) (ZMod n) F →ₗ[F] F)) :
    Submodule F (Matrix (ZMod n) (ZMod n) F) where
  carrier := {Y | ∀ c r, Y c r = a c r (rot c Y)}
  add_mem' {Y Z} hY hZ c r := by
    rw [map_add, map_add, ← hY c r, ← hZ c r]
    rfl
  zero_mem' c r := by
    rw [map_zero, map_zero]
    rfl
  smul_mem' t Y hY c r := by
    rw [map_smul, map_smul, ← hY c r]
    rfl

theorem mem_entryRuleSpace {a : ZMod n → ZMod n → (Matrix (ZMod n) (ZMod n) F →ₗ[F] F)}
    {Y : Matrix (ZMod n) (ZMod n) F} :
    Y ∈ entryRuleSpace a ↔ ∀ c r, Y c r = a c r (rot c Y) :=
  Iff.rfl

/-- The part of any subspace that satisfies an entry rule is a code of that rule. -/
theorem isEntryRuleCode_inf_entryRuleSpace
    (a : ZMod n → ZMod n → (Matrix (ZMod n) (ZMod n) F →ₗ[F] F))
    (𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)) :
    IsEntryRuleCode a (𝒳 ⊓ entryRuleSpace a) :=
  fun _ hY c r => mem_entryRuleSpace.1 hY.2 c r

/-- A subspace `𝒳` is a code of the entry rules `a ω` with advice `w` if there are offsets
`b ω c r` such that every `X ∈ 𝒳` has `X c r = a (w X) c r (rot c X) + b (w X) c r`. -/
def IsEntryRuleCodeWithAdvice
    (a : Ω → ZMod n → ZMod n → (Matrix (ZMod n) (ZMod n) F →ₗ[F] F))
    (w : Matrix (ZMod n) (ZMod n) F → Ω) (𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)) : Prop :=
  ∃ b : Ω → ZMod n → ZMod n → F,
    ∀ X ∈ 𝒳, ∀ c r, X c r = a (w X) c r (rot c X) + b (w X) c r

/-- Over a finite field, a space of matrices has `|F| ^ dim` elements. -/
theorem natCard_submodule_matrix [Finite F] [NeZero n]
    (𝒴 : Submodule F (Matrix (ZMod n) (ZMod n) F)) : Nat.card 𝒴 = Nat.card F ^ finrank F 𝒴 := by
  have := Fintype.ofFinite F
  have := Fintype.ofFinite 𝒴
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := F) (V := 𝒴)]

namespace IsEntryRuleCodeWithAdvice

variable {a : Ω → ZMod n → ZMod n → (Matrix (ZMod n) (ZMod n) F →ₗ[F] F)}
  {w : Matrix (ZMod n) (ZMod n) F → Ω} {𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)}

/-- **The matrices that share a value of the advice.**  Over a finite field, if the rule `a ω`
changes, from one row to the next, only at the pairs of a set of at most `E` elements, then at
most `|F| ^ ((n ^ 2 + n + E) / 2)` matrices of the code have advice `ω`: they lie in a coset of a
code of the rule `a ω`. -/
theorem natCard_fiber_le [Finite F] [NeZero n] (h : IsEntryRuleCodeWithAdvice a w 𝒳) {E : ℕ}
    (ω : Ω) (hE : ∃ B : Finset (ZMod n × ZMod n), B.card ≤ E ∧
      ∀ c r, (c, r) ∉ B → a ω c r = a ω (c + 1) r) :
    Nat.card {X : 𝒳 // w X = ω} ≤ Nat.card F ^ ((n ^ 2 + n + E) / 2) := by
  classical
  obtain ⟨b, hrule⟩ := h
  -- the homogeneous code of the fibre is `𝒳 ⊓ entryRuleSpace (a ω)`
  have hK : finrank F ↥(𝒳 ⊓ entryRuleSpace (a ω)) ≤ (n ^ 2 + n + E) / 2 := by
    obtain ⟨B, hBcard, hB⟩ := hE
    have := (isEntryRuleCode_inf_entryRuleSpace (a ω) 𝒳).two_mul_finrank_le_of_changes hB
    omega
  have hpos : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.2 (Nat.card_pos.ne')
  by_cases hω : ∃ X ∈ 𝒳, w X = ω
  · -- subtracting one matrix of the fibre maps it into the homogeneous code
    obtain ⟨X₀, hX₀, hX₀ω⟩ := hω
    have hinj : Nat.card {X : 𝒳 // w X = ω} ≤ Nat.card ↥(𝒳 ⊓ entryRuleSpace (a ω)) := by
      refine Nat.card_le_card_of_injective
        (fun X : {X : 𝒳 // w X = ω} =>
          (⟨X.1.1 - X₀, ?_⟩ : ↥(𝒳 ⊓ entryRuleSpace (a ω)))) ?_
      · obtain ⟨⟨X, hX⟩, hXω⟩ := X
        simp only at hXω
        show X - X₀ ∈ 𝒳 ⊓ entryRuleSpace (a ω)
        refine ⟨𝒳.sub_mem hX hX₀, mem_entryRuleSpace.2 fun c r => ?_⟩
        have h1 := hrule X hX c r
        have h2 := hrule X₀ hX₀ c r
        rw [hXω] at h1
        rw [hX₀ω] at h2
        rw [map_sub, map_sub, Matrix.sub_apply, h1, h2]
        ring
      · intro X Y hXY
        have := congrArg Subtype.val hXY
        simp only [sub_left_inj] at this
        exact Subtype.ext (Subtype.ext this)
    refine hinj.trans ?_
    rw [natCard_submodule_matrix]
    exact Nat.pow_le_pow_right hpos hK
  · -- an empty fibre
    have hempty : IsEmpty {X : 𝒳 // w X = ω} := ⟨fun X => hω ⟨X.1.1, X.1.2, X.2⟩⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

/-- **Advice and single-entry changes.**  Over a finite field `F`, let `𝒳` be a code of the
entry rules `a ω` with advice `w` taking values in a finite set `Ω`, and suppose that every rule
`a ω` changes, from one row to the next, only at the pairs of a set of at most `E` elements.
Then `|F| ^ (2 * dim 𝒳) ≤ |Ω| ^ 2 * |F| ^ (n ^ 2 + n + E)`.  With `|Ω| = |F| ^ q` this reads
`2 * dim 𝒳 ≤ n ^ 2 + n + E + 2 * q`. -/
theorem natCard_pow_two_mul_finrank_le [Finite F] [NeZero n] [Fintype Ω]
    (h : IsEntryRuleCodeWithAdvice a w 𝒳) {E : ℕ}
    (hE : ∀ ω, ∃ B : Finset (ZMod n × ZMod n), B.card ≤ E ∧
      ∀ c r, (c, r) ∉ B → a ω c r = a ω (c + 1) r) :
    Nat.card F ^ (2 * finrank F 𝒳) ≤ Fintype.card Ω ^ 2 * Nat.card F ^ (n ^ 2 + n + E) := by
  have hcard : Nat.card 𝒳 = ∑ ω, Nat.card {X : 𝒳 // w X = ω} := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv (fun X : 𝒳 => w X.1)).symm
  have hpos : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.2 (Nat.card_pos.ne')
  have hmain : Nat.card F ^ finrank F 𝒳 ≤
      Fintype.card Ω * Nat.card F ^ ((n ^ 2 + n + E) / 2) := by
    rw [← natCard_submodule_matrix, hcard]
    calc ∑ ω, Nat.card {X : 𝒳 // w X = ω}
        ≤ ∑ _ω : Ω, Nat.card F ^ ((n ^ 2 + n + E) / 2) :=
          Finset.sum_le_sum fun ω _ => h.natCard_fiber_le ω (hE ω)
      _ = Fintype.card Ω * Nat.card F ^ ((n ^ 2 + n + E) / 2) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  calc Nat.card F ^ (2 * finrank F 𝒳) = (Nat.card F ^ finrank F 𝒳) ^ 2 := by
        rw [← pow_mul, mul_comm]
    _ ≤ (Fintype.card Ω * Nat.card F ^ ((n ^ 2 + n + E) / 2)) ^ 2 :=
        Nat.pow_le_pow_left hmain 2
    _ = Fintype.card Ω ^ 2 * Nat.card F ^ (2 * ((n ^ 2 + n + E) / 2)) := by
        rw [mul_pow, ← pow_mul, mul_comm ((n ^ 2 + n + E) / 2) 2]
    _ ≤ Fintype.card Ω ^ 2 * Nat.card F ^ (n ^ 2 + n + E) := by
        refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos ?_)
        omega

end IsEntryRuleCodeWithAdvice

end SwapRigidity

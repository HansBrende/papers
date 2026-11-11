import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Dynamics.PeriodicPts.Defs

/-! Frobenius periods of actual elements, identified with the degrees of the
subfields they generate. This reuses Mathlib's automorphism-order theorem. -/

namespace LeanMachine

open Module IntermediateField

variable (F E : Type*) [Field F] [Fintype F] [Field E] [Finite E] [Algebra F E]

theorem frobenius_pow_apply (n : ℕ) (x : E) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ n) x =
      x ^ (Fintype.card F ^ n) := by
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]

theorem frobenius_fixes_iff_degree_dvd (x : E) (n : ℕ) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ n) x = x ↔
      finrank F (adjoin F {x}) ∣ n := by
  let K := adjoin F {x}
  let xK : K := ⟨x, subset_adjoin F {x} (Set.mem_singleton x)⟩
  have heval : ((FiniteField.frobeniusAlgEquivOfAlgebraic F K ^ n) xK : E) =
      (FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ n) x := by
    rw [frobenius_pow_apply, frobenius_pow_apply]
    rfl
  rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F K,
    orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro hx
    apply AlgEquiv.coe_toAlgHom_injective
    apply adjoin_algHom_ext F
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    apply Subtype.ext
    exact heval.trans hx
  · intro h
    have hx := congrArg (fun φ => (φ xK : E)) h
    simpa only [heval, AlgEquiv.one_apply] using hx

theorem frobenius_minimalPeriod (x : E) :
    Function.minimalPeriod (FiniteField.frobeniusAlgEquivOfAlgebraic F E) x =
      finrank F (adjoin F {x}) := by
  apply Nat.dvd_antisymm
  · apply Function.IsPeriodicPt.minimalPeriod_dvd
    simpa only [AlgEquiv.coe_pow, Function.IsPeriodicPt, Function.IsFixedPt] using
      (frobenius_fixes_iff_degree_dvd F E x _).mpr (dvd_refl _)
  · apply (frobenius_fixes_iff_degree_dvd F E x _).mp
    simpa only [AlgEquiv.coe_pow, Function.IsPeriodicPt, Function.IsFixedPt] using
      Function.isPeriodicPt_minimalPeriod (FiniteField.frobeniusAlgEquivOfAlgebraic F E) x

theorem frobenius_powers_equal_iff (x : E) (m n : ℕ) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ m) x =
      (FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ n) x ↔
        m % finrank F (adjoin F {x}) = n % finrank F (adjoin F {x}) := by
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic F E
  have hp : 0 < Function.minimalPeriod φ x := by
    rw [frobenius_minimalPeriod]
    exact Module.finrank_pos
  have he := Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
    (f := φ) (x := x) (Nat.mod_lt m hp) (Nat.mod_lt n hp)
  rw [Function.iterate_mod_minimalPeriod_eq, Function.iterate_mod_minimalPeriod_eq,
    frobenius_minimalPeriod] at he
  simpa only [AlgEquiv.coe_pow] using he

/-- Counting all receiver phases over a full extension degree does not count
duplicate conjugates: their exact number is the generated-field degree. -/
theorem frobenius_conjugates_card (x : E) (d : ℕ)
    (hd : finrank F (adjoin F {x}) ≤ d) :
    Nat.card (Set.range (fun i : Fin d =>
      (FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ i.val) x)) =
        finrank F (adjoin F {x}) := by
  let h := finrank F (adjoin F {x})
  have hp : 0 < h := Module.finrank_pos
  let g (i : Fin h) := (FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ i.val) x
  have hi : Function.Injective g := by
    intro i j hij
    apply Fin.ext
    have he := (frobenius_powers_equal_iff F E x i j).mp hij
    change i.val % h = j.val % h at he
    simpa only [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] using he
  have hr : Set.range (fun i : Fin d =>
      (FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ i.val) x) = Set.range g := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨⟨i.val % h, Nat.mod_lt _ hp⟩, ?_⟩
      apply (frobenius_powers_equal_iff F E x _ _).mpr
      exact Nat.mod_mod _ _
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i, i.2.trans_le hd⟩, rfl⟩
  rw [hr, ← Nat.card_congr (Equiv.ofInjective g hi)]
  exact Nat.card_fin h

end LeanMachine

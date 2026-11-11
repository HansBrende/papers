import SharedDecoders.CompositionMultipliers
import LeanMachine.FiniteFieldOrbit

/-! Actual multiplier getters, Frobenius residue classes and their degrees.
The coefficient functional can be any nonzero linear functional, in particular
coordinate zero in the reversed normal basis used by the manuscript. -/

namespace SharedDecoders

open Module IntermediateField

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Finite E] [Algebra F E]

def multiplierCoefficient (lam : E) : E := lam / lam ^ Fintype.card F

/-- Undo the received phase, perform the complete scalar multiplication, and
read the demanded coordinate in its phase-zero chart. -/
noncomputable def fieldMultiplierGetter (ℓ : E →ₗ[F] F) (lam : E) (c : ℕ) (x : E) : F :=
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic F E
  ℓ ((φ ^ c) (lam * (φ ^ c).symm x))

theorem fieldMultiplierGetter_eq (ℓ : E →ₗ[F] F) (lam : E) (c : ℕ) (x : E) :
    fieldMultiplierGetter ℓ lam c x =
      ℓ ((FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ c) lam * x) := by
  simp only [fieldMultiplierGetter, map_mul, AlgEquiv.apply_symm_apply]

omit [Fintype F] [Finite E] in
theorem scalar_getters_injective (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0) :
    Function.Injective (fun a : E => fun x : E => ℓ (a * x)) := by
  intro a b hab
  by_contra hne
  apply hℓ
  apply LinearMap.ext
  intro x
  have hv := congrFun hab ((a - b)⁻¹ * x)
  dsimp only at hv
  have hz : ℓ ((a - b) * ((a - b)⁻¹ * x)) = 0 := by
    rw [sub_mul, map_sub, hv, sub_self]
  simpa only [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hne), one_mul,
    LinearMap.zero_apply] using hz

theorem multiplier_getters_equal_iff (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0)
    (lam : E) (c e : ℕ) :
    (fun x : E => ℓ ((FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ c) lam * x)) =
      (fun x : E => ℓ ((FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ e) lam * x)) ↔
        c % finrank F (adjoin F {lam}) = e % finrank F (adjoin F {lam}) := by
  rw [(scalar_getters_injective ℓ hℓ).eq_iff]
  exact LeanMachine.frobenius_powers_equal_iff F E lam c e

theorem multiplier_getters_card (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0)
    (lam : E) (d : ℕ) (hd : finrank F (adjoin F {lam}) ≤ d) :
    Nat.card (Set.range (fun c : Fin d => fun x : E =>
      ℓ ((FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ c.val) lam * x))) =
        finrank F (adjoin F {lam}) := by
  let g (c : Fin d) := (FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ c.val) lam
  let f (a : E) (x : E) := ℓ (a * x)
  change (Set.range (f ∘ g)).ncard = _
  rw [Set.range_comp, Set.ncard_image_of_injective _ (scalar_getters_injective ℓ hℓ)]
  exact LeanMachine.frobenius_conjugates_card F E lam d hd

theorem actual_multiplier_getters_card (ℓ : E →ₗ[F] F) (hℓ : ℓ ≠ 0)
    (lam : E) (d : ℕ) (hd : finrank F (adjoin F {lam}) ≤ d) :
    Nat.card (Set.range (fun c : Fin d => fieldMultiplierGetter ℓ lam c.val)) =
      finrank F (adjoin F {lam}) := by
  simpa only [funext (fieldMultiplierGetter_eq ℓ lam _)] using
    multiplier_getters_card ℓ hℓ lam d hd

omit [Finite E] in
theorem multiplier_coefficient_mem (lam : E) : multiplierCoefficient (F := F) lam ∈ adjoin F {lam} := by
  have hx : lam ∈ adjoin F {lam} := subset_adjoin F {lam} (Set.mem_singleton lam)
  exact (adjoin F {lam}).div_mem hx
    ((adjoin F {lam}).toSubfield.pow_mem hx (Fintype.card F))

theorem multiplier_degree_le (lam : E) :
    finrank F (adjoin F {multiplierCoefficient (F := F) lam}) ≤ finrank F (adjoin F {lam}) := by
  apply IntermediateField.finrank_le_of_le_right
  apply adjoin_le_iff.mpr
  exact Set.singleton_subset_iff.mpr (multiplier_coefficient_mem lam)

omit [Finite E] in
theorem multiplier_binary_degree_eq (hF : Fintype.card F = 2) (lam : E) :
    finrank F (adjoin F {multiplierCoefficient (F := F) lam}) = finrank F (adjoin F {lam}) := by
  have hκ : multiplierCoefficient (F := F) lam = lam⁻¹ := by
    simp [multiplierCoefficient, hF, pow_two]
  have hfield : adjoin F {lam⁻¹} = adjoin F {lam} := by
    apply le_antisymm
    · apply adjoin_le_iff.mpr
      exact Set.singleton_subset_iff.mpr
        ((adjoin F {lam}).inv_mem (subset_adjoin F {lam} (Set.mem_singleton lam)))
    · apply adjoin_le_iff.mpr
      apply Set.singleton_subset_iff.mpr
      have hh := (adjoin F {lam⁻¹}).inv_mem
        (subset_adjoin F {lam⁻¹} (Set.mem_singleton lam⁻¹))
      rw [inv_inv] at hh
      exact hh
  rw [hκ, hfield]

end SharedDecoders

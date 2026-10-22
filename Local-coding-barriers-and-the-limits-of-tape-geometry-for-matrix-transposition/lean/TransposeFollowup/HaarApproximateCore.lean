import TransposeFollowup.FiniteTranslateOverlap
import Mathlib.Combinatorics.Additive.ApproximateSubgroup

/-! Finite packing upgrades a symmetric core to an approximate group.
We reuse mathlib's predicate and retain the stronger symmetric witness
inside the square required by Tao's definition. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

theorem symmetric_cube_finite_cover {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (σ : Measure G) [Measure.IsMulLeftInvariant σ] {T : Set G}
    (hT : MeasurableSet T) (hT1 : 1 ∈ T) (hTs : T⁻¹ = T)
    (hT0 : 0 < σ T) (hTt : σ T < ⊤) {R : ℝ≥0∞} (hRt : R ≠ ⊤)
    (h7 : σ (T ^ 7) ≤ R * σ T) :
    ∃ Y : Finset G, (Y : Set G) ⊆ (T ^ 3) ^ 2 ∧ (Y : Set G)⁻¹ = (Y : Set G) ∧
      (Y.card : ℝ≥0∞) ≤ 2 * R ∧ (T ^ 3) ^ 2 ⊆ (Y : Set G) * T ^ 3 ∧
      IsApproximateSubgroup (2 * R).toReal (T ^ 3) := by
  obtain ⟨X, hX, hXcard, hcover⟩ := exists_finite_haar_translate_cover σ hT hT0 hTt hRt
    (show σ (T ^ 6 * T) ≤ R * σ T by simpa only [← pow_succ] using h7)
  let Y := X ∪ X⁻¹
  have hYsym : (Y : Set G)⁻¹ = (Y : Set G) := by
    simp only [Y, Finset.coe_union, Finset.coe_inv, Set.union_inv, inv_inv, Set.union_comm]
  have h6 : (T ^ 6)⁻¹ = T ^ 6 := by rw [← inv_pow, hTs]
  have hXi : ((X⁻¹ : Finset G) : Set G) ⊆ T ^ 6 := by
    intro x hx
    have hh : x ∈ ((X : Set G)⁻¹) := by simpa only [Finset.coe_inv] using hx
    have hh' := (Set.inv_subset_inv.mpr hX) hh
    simpa only [h6] using hh'
  have hY6 : (Y : Set G) ⊆ T ^ 6 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hX hx
    · exact hXi hx
  have hU2 : (T ^ 3) ^ 2 = T ^ 6 := by rw [← pow_mul]
  have hYcard : (Y.card : ℝ≥0∞) ≤ 2 * R := by
    calc
      (Y.card : ℝ≥0∞) ≤ (X.card : ℝ≥0∞) + X.card := by
        exact_mod_cast (Finset.card_union_le X X⁻¹).trans_eq (by rw [Finset.card_inv])
      _ ≤ R + R := add_le_add hXcard hXcard
      _ = _ := by ring
  have hcov : (T ^ 3) ^ 2 ⊆ (Y : Set G) * T ^ 3 := by
    rw [hU2]
    calc
      T ^ 6 ⊆ (X : Set G) * T * T⁻¹ := hcover
      _ = (X : Set G) * T ^ 2 := by rw [hTs, mul_assoc, pow_two]
      _ ⊆ (Y : Set G) * T ^ 3 := Set.mul_subset_mul
        (fun _ hx => Finset.mem_union_left _ hx) (Set.pow_subset_pow_right hT1 (by decide : 2 ≤ 3))
  refine ⟨Y, hU2.symm ▸ hY6, hYsym, hYcard, hcov, ?_⟩
  refine ⟨Set.one_mem_pow hT1, by rw [← inv_pow, hTs], Y, ?_, ?_⟩
  · simpa only [ENNReal.toReal_natCast] using
      (ENNReal.toReal_le_toReal (by finiteness) (by finiteness : 2 * R ≠ ⊤)).mpr hYcard
  · simpa only [smul_eq_mul] using hcov

end TransposeFollowup

import TransposeFollowup.MobiusNearIdentityLocalization
import TransposeFollowup.FiniteTranslateOverlap

/-! Localization retains actual probability mass, not just Haar volume.
The argument works for any measure, by the existing finite-cover maximum. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace Group]

theorem exists_near_identity_translate_mass (σ : Measure Group) {U : Set Group} {Q α : ℝ}
    (hU : U.Nonempty) (hQ : 1 ≤ Q) (hα : 0 < α) (hαone : α ≤ 1)
    (hUb : U ⊆ matrixEntryBox Q) (hUi : U⁻¹ = U) (x : Group) :
    ∃ z ∈ U, σ (x • U) ≤ ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4) *
      σ ((x * z) • (U ^ 2 ∩ mobiusIdentityBall α)) := by
  obtain ⟨Z, hZU, hZcard, hcover⟩ := exists_near_identity_translate_cover hQ hα hαone hUb hUi
  let F := Z.image (x * ·)
  have hcover' : x • U ⊆ (F : Set Group) * (U ^ 2 ∩ mobiusIdentityBall α) := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hy
    obtain ⟨z, hz, a, ha, he⟩ := Set.mem_mul.mp (hcover hu)
    refine Set.mem_mul.mpr ⟨x * z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, a, ha, ?_⟩
    change (x * z) * a = x * u
    rw [mul_assoc, he]
  have hnonempty : (x • U).Nonempty := by
    obtain ⟨u, hu⟩ := hU
    exact ⟨x * u, Set.smul_mem_smul_set hu⟩
  obtain ⟨y, hy, hmass⟩ := exists_large_overlap_of_finite_translate_cover σ
    hnonempty (Set.subset_univ _) F hcover'
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  have hcard : (F.card : ℝ≥0∞) ≤ ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4) := by
    have hh : (F.card : ℝ≥0∞) ≤ (Z.card : ℝ≥0∞) := by exact_mod_cast Finset.card_image_le
    exact hh.trans hZcard
  refine ⟨z, hZU hz, ?_⟩
  have hm : σ (x • U) ≤ (F.card : ℝ≥0∞) * σ ((x * z) • (U ^ 2 ∩ mobiusIdentityBall α)) := by
    simpa only [Set.univ_inter] using hmass
  exact hm.trans (mul_le_mul' hcard le_rfl)

end TransposeFollowup.RealMobius

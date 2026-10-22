import TransposeFollowup.HaarFinitePacking
import Mathlib.MeasureTheory.Group.Convolution

/-! Haar smoothing expresses set probability as an average of local
overlap volumes. Positive probability therefore yields a local witness. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

theorem haar_smoothing_apply (σ ν : Measure G) [SFinite σ] [Measure.IsMulLeftInvariant σ]
    {S Z : Set G} (hS0 : 0 < σ S) (hZ : MeasurableSet Z) :
    (ν ∗ₘ ((σ S)⁻¹ • σ.restrict S)) Z =
      (σ S)⁻¹ * ∫⁻ g, σ (Z ∩ g • S) ∂ν := by
  rw [Measure.mconv, Measure.map_apply measurable_mul hZ,
    Measure.prod_apply (hZ.preimage measurable_mul)]
  have hinner (g : G) : ((σ S)⁻¹ • σ.restrict S) {s | g * s ∈ Z} =
      (σ S)⁻¹ * σ (Z ∩ g • S) := by
    have hm : MeasurableSet {s : G | g * s ∈ Z} := hZ.preimage (by fun_prop)
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hm]
    congr 1
    have he : {s | g * s ∈ Z} ∩ S = (fun s => g * s) ⁻¹' (Z ∩ g • S) := by
      ext s
      constructor
      · intro hs
        exact ⟨hs.1, Set.mem_smul_set.mpr ⟨s, hs.2, rfl⟩⟩
      · intro hs
        obtain ⟨t, ht, heq⟩ := Set.mem_smul_set.mp hs.2
        change g * t = g * s at heq
        exact ⟨hs.1, mul_left_cancel heq ▸ ht⟩
    rw [he, measure_preimage_mul]
  calc
    _ = ∫⁻ g, (σ S)⁻¹ * σ (Z ∩ g • S) ∂ν := lintegral_congr hinner
    _ = _ := lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hS0.ne')

theorem exists_local_haar_overlap_of_smoothing (σ ν : Measure G) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [IsProbabilityMeasure ν]
    {S Z : Set G} (hS0 : 0 < σ S) (hSt : σ S < ⊤) (hZ : MeasurableSet Z)
    {p : ℝ≥0∞} (hp0 : 0 < p) (hpt : p ≠ ⊤)
    (hp : p ≤ (ν ∗ₘ ((σ S)⁻¹ • σ.restrict S)) Z) :
    ∃ g : G, p * σ S ≤ 2 * σ (Z ∩ g • S) := by
  have havg : σ S * (ν ∗ₘ ((σ S)⁻¹ • σ.restrict S)) Z =
      ∫⁻ g, σ (Z ∩ g • S) ∂ν := by
    rw [haar_smoothing_apply σ ν hS0 hZ, ← mul_assoc,
      ENNReal.mul_inv_cancel hS0.ne' hSt.ne, one_mul]
  by_contra hn
  push Not at hn
  have hh : (2 : ℝ≥0∞) * (p * σ S) ≤ 1 * (p * σ S) := by
    calc
      2 * (p * σ S) = 2 * (σ S * p) := by ring
      _ ≤ 2 * (σ S * (ν ∗ₘ ((σ S)⁻¹ • σ.restrict S)) Z) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hp)
      _ = 2 * ∫⁻ g, σ (Z ∩ g • S) ∂ν := by rw [havg]
      _ = ∫⁻ g, 2 * σ (Z ∩ g • S) ∂ν := (lintegral_const_mul' _ _ (by norm_num)).symm
      _ ≤ ∫⁻ _g, p * σ S ∂ν := lintegral_mono (fun g => (hn g).le)
      _ = 1 * (p * σ S) := by simp
  have htwo := (ENNReal.mul_le_mul_iff_left (mul_ne_zero hp0.ne' hS0.ne') (by finiteness)).mp hh
  norm_num at htwo

end TransposeFollowup

import TransposeFollowup.RationalWalkIsolation
import TransposeFollowup.GeneratorWalkFiniteSupport
import TransposeFollowup.GeneratorWalkAtoms
import TransposeFollowup.ConvolutionTranslateMass

/-! Extract actual short free words from translated smoothed-walk mass,
retaining their denominator and one common right-smoothing element. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory Set RealMobius
open scoped ENNReal NNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem exists_short_words_of_smoothed_walk_mass {m D : ℕ} (g : Fin m → Group)
    (hm : 0 < m) (hg : ∀ i, HasDenominator D (g i))
    (hfree : Function.Injective (FreeGroup.lift (realEmbedding ∘ g)))
    {k : ℝ} (hk : 1 ≤ k) (hcard : k ^ 2 ≤ 2 * m) (t : ℕ)
    {η : ℝ} (hη : 0 < η) {A : Set RealMobius.Group} (hA : MeasurableSet A)
    (w : RealMobius.Group) {p : ℝ≥0∞} (hp : 0 < p) (hpt : p ≠ ⊤)
    (hmass : p ≤ (generatorWalkMeasure (realEmbedding ∘ g) t ∗ₘ mobiusHaarKernel η) (w • A)) :
    ∃ u ∈ mobiusIdentityBall η, ∃ F : Finset (FreeGroup (Fin m)), F.Nonempty ∧
      (∀ v ∈ F, FreeGroup.norm v ≤ t ∧
        FreeGroup.lift (realEmbedding ∘ g) v ∈ denominatorCarrier (D ^ t) ∧
        w⁻¹ * FreeGroup.lift (realEmbedding ∘ g) v * u ∈ A) ∧
      p ≤ 2 * (F.card : ℝ≥0∞) * ENNReal.ofReal ((2 / k) ^ t) := by
  let G := realEmbedding ∘ g
  let μ := generatorWalkMeasure G t
  have : IsProbabilityMeasure μ := generatorWalkMeasure_probability G hm t
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  obtain ⟨u, hu, hslice⟩ := exists_right_slice_mass_of_mconv μ (mobiusHaarKernel η)
    (hA.const_smul w) (mobiusHaarKernel_ae_mem η) hp hpt hmass
  obtain ⟨E, hEn, hE⟩ := generatorWalkMeasure_word_support G hm t
  have hden := generatorWalkMeasure_ae_denominatorCarrier g hm hg t
  let S := (· * u) ⁻¹' (w • A)
  let F := E.filter (fun v => FreeGroup.lift G v ∈ denominatorCarrier (D ^ t) ∧
    FreeGroup.lift G v ∈ S)
  have hF : ∀ v ∈ F, FreeGroup.norm v ≤ t ∧
      FreeGroup.lift G v ∈ denominatorCarrier (D ^ t) ∧ FreeGroup.lift G v ∈ S := by
    intro v hv
    have he := Finset.mem_filter.mp hv
    exact ⟨hEn v he.1, he.2⟩
  have hmF : μ (F.image (FreeGroup.lift G) : Set RealMobius.Group) = μ S := by
    apply measure_congr
    filter_upwards [hE, hden] with a ha hd
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    apply propext
    change FreeGroup.lift G v ∈ F.image (FreeGroup.lift G) ↔ FreeGroup.lift G v ∈ S
    constructor
    · intro hv'
      obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hv'
      exact he ▸ (hF z hz).2.2
    · intro hs
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hd, hs⟩, rfl⟩
  have hfreeG : Function.Injective (FreeGroup.lift G) := hfree
  have hcount : μ (F.image (FreeGroup.lift G) : Set RealMobius.Group) ≤
      (F.card : ℝ≥0∞) * ENNReal.ofReal ((2 / k) ^ t) := by
    let H := F.image (FreeGroup.lift G)
    calc
      _ ≤ ∑ a ∈ H, μ {a} := by
        have he : (H : Set RealMobius.Group) = ⋃ a ∈ H, ({a} : Set RealMobius.Group) := by
          ext a
          simp
        rw [he]
        exact measure_biUnion_finset_le H (fun a => ({a} : Set RealMobius.Group))
      _ ≤ ∑ _a ∈ H, ENNReal.ofReal ((2 / k) ^ t) := Finset.sum_le_sum
        (fun a _ => generatorWalkMeasure_atom_le G hm hfree hk hcard t a)
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, H, Finset.card_image_of_injective F hfreeG]
  have hbound : p ≤ 2 * (F.card : ℝ≥0∞) * ENNReal.ofReal ((2 / k) ^ t) := by
    calc
      p ≤ 2 * μ S := hslice
      _ = 2 * μ (F.image (FreeGroup.lift G) : Set RealMobius.Group) := by rw [hmF]
      _ ≤ 2 * ((F.card : ℝ≥0∞) * ENNReal.ofReal ((2 / k) ^ t)) := mul_le_mul' le_rfl hcount
      _ = _ := by ring
  refine ⟨u, hu, F, ?_, ?_, hbound⟩
  · by_contra he
    have hz : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [hz, Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul] at hbound
    exact (not_le_of_gt hp) hbound
  · intro v hv
    refine ⟨(hF v hv).1, (hF v hv).2.1, ?_⟩
    obtain ⟨z, hz, he⟩ := (hF v hv).2.2
    have hh : w⁻¹ * FreeGroup.lift G v * u = z := by
      change w * z = FreeGroup.lift G v * u at he
      rw [mul_assoc, ← he, inv_mul_cancel_left]
    exact hh.symm ▸ hz

end TransposeFollowup.RationalFreePair

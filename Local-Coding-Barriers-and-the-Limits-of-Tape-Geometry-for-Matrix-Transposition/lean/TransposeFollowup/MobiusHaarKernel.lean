import TransposeFollowup.MobiusMatrixGeometryCore
import TransposeFollowup.GeneratorConvolutionWalk
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Order.Compact

/-! A concrete Haar smoothing kernel. The radius is the ordinary Frobenius
radius: the sum of four squared entry errors is less than the radius squared.
No small-ball volume asymptotic or flattening estimate is asserted here. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap
open scoped ENNReal
set_option autoImplicit false

instance instGroupLocallyCompactSpace : LocallyCompactSpace Group := by
  have : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  exact (Matrix.SpecialLinearGroup.isClosedEmbedding_val (n := Fin 2) (R := ℝ)).locallyCompactSpace

theorem mobiusIdentityDistanceSq_continuous : Continuous mobiusIdentityDistanceSq := by
  unfold mobiusIdentityDistanceSq
  fun_prop

theorem mobiusIdentityBall_isOpen (η : ℝ) : IsOpen (mobiusIdentityBall η) :=
  isOpen_lt mobiusIdentityDistanceSq_continuous continuous_const

theorem one_mem_mobiusIdentityBall {η : ℝ} (hη : 0 < η) : (1 : Group) ∈ mobiusIdentityBall η := by
  simpa [mobiusIdentityBall, mobiusIdentityDistanceSq] using sq_pos_of_pos hη

theorem mobiusIdentityBall_subset_compact_box {η : ℝ} (hη : 0 < η) :
    ∃ K : Set Group, IsCompact K ∧ mobiusIdentityBall η ⊆ K := by
  let lo : Fin 2 → Fin 2 → ℝ := fun i k => (1 : Matrix (Fin 2) (Fin 2) ℝ) i k - η
  let hi : Fin 2 → Fin 2 → ℝ := fun i k => (1 : Matrix (Fin 2) (Fin 2) ℝ) i k + η
  have hc : IsCompact (Icc lo hi) :=
    @isCompact_Icc (Fin 2 → Fin 2 → ℝ) _ _ _ lo hi
  refine ⟨(fun g : Group => fun i k : Fin 2 => g i k) ⁻¹' Icc lo hi,
    (Matrix.SpecialLinearGroup.isClosedEmbedding_val (n := Fin 2) (R := ℝ)).isCompact_preimage hc, ?_⟩
  intro g hg
  obtain ⟨h00, h01, h10, h11⟩ := mobiusIdentityBall_entry_bounds hη hg
  have hentries : ∀ i k : Fin 2, |g i k - (1 : Matrix (Fin 2) (Fin 2) ℝ) i k| < η := by
    intro i k
    fin_cases i <;> fin_cases k <;> simpa using (by assumption)
  constructor
  · intro i k
    have h := (abs_lt.mp (hentries i k)).1
    change (1 : Matrix (Fin 2) (Fin 2) ℝ) i k - η ≤ g i k
    linarith
  · intro i k
    have h := (abs_lt.mp (hentries i k)).2
    change g i k ≤ (1 : Matrix (Fin 2) (Fin 2) ℝ) i k + η
    linarith

variable [MeasurableSpace Group] [BorelSpace Group]

theorem mobiusIdentityBall_haar_pos {η : ℝ} (hη : 0 < η) :
    0 < (Measure.haar : Measure Group) (mobiusIdentityBall η) :=
  (mobiusIdentityBall_isOpen η).measure_pos Measure.haar ⟨1, one_mem_mobiusIdentityBall hη⟩

theorem mobiusIdentityBall_haar_lt_top {η : ℝ} (hη : 0 < η) :
    (Measure.haar : Measure Group) (mobiusIdentityBall η) < ∞ := by
  obtain ⟨K, hK, hsub⟩ := mobiusIdentityBall_subset_compact_box hη
  exact (measure_mono hsub).trans_lt hK.measure_lt_top

noncomputable def mobiusHaarKernel (η : ℝ) : Measure Group :=
  ((Measure.haar : Measure Group) (mobiusIdentityBall η))⁻¹ •
    (Measure.haar : Measure Group).restrict (mobiusIdentityBall η)

theorem mobiusHaarKernel_probability {η : ℝ} (hη : 0 < η) :
    IsProbabilityMeasure (mobiusHaarKernel η) := by
  constructor
  rw [mobiusHaarKernel, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (mobiusIdentityBall_haar_pos hη).ne'
    (mobiusIdentityBall_haar_lt_top hη).ne

theorem mobiusHaarKernel_ae_mem (η : ℝ) :
    ∀ᵐ g ∂mobiusHaarKernel η, g ∈ mobiusIdentityBall η :=
  Measure.ae_smul_measure (ae_restrict_mem (mobiusIdentityBall_isOpen η).measurableSet) _

theorem mobiusHaarKernel_ae_entry_bounds {η : ℝ} (hη : 0 < η) :
    ∀ᵐ g ∂mobiusHaarKernel η, |g 0 0 - 1| ≤ η ∧ |g 0 1| ≤ η ∧ |g 1 0| ≤ η :=
  (mobiusHaarKernel_ae_mem η).mono fun _ hg => by
    obtain ⟨h00, h01, h10, _⟩ := mobiusIdentityBall_entry_bounds hη hg
    exact ⟨h00.le, h01.le, h10.le⟩

theorem mobiusHaarKernel_eq_withDensity (η : ℝ) :
    mobiusHaarKernel η = (Measure.haar : Measure Group).withDensity
      ((mobiusIdentityBall η).indicator (fun _ =>
        ((Measure.haar : Measure Group) (mobiusIdentityBall η))⁻¹)) := by
  rw [withDensity_indicator (mobiusIdentityBall_isOpen η).measurableSet,
    withDensity_const]
  rfl

theorem generatorWalk_haar_smoothed_dyadic_norm_lower {c : ℕ} (G : Fin c → Group) (hc : 0 < c)
    (j : ℕ) (u : 𝓢(ℝ, ℂ)) (hu : ‖u.toLp 2 volume‖ = 1) {R r η : ℝ}
    (hr : 0 ≤ r) (hlarge : r ≤ ‖complexAverage G (u.toLp 2 volume)‖)
    (hR : schwartzDyadicRegularityCost j u ≤ R) (hηpos : 0 < η) (hη : η ≤ 1 / 2)
    (m : ℕ) (he : 29 * (2 : ℝ) ^ j * Real.sqrt R * η ≤ r ^ (2 ^ m) / 2) :
    r ^ (2 ^ m) / 2 ≤
      ‖groupActionAverage (generatorWalkMeasure G (2 ^ m) ∗ₘ mobiusHaarKernel η)
        (u.toLp 2 volume)‖ := by
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hηpos
  exact generatorWalk_smoothed_dyadic_norm_lower G hc _ j u hu hr hlarge hR hη
    (mobiusHaarKernel_ae_entry_bounds hηpos) m he

end TransposeFollowup.RealMobius

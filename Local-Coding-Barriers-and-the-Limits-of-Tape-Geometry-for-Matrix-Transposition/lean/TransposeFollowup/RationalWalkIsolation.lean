import TransposeFollowup.RationalWordArithmetic
import TransposeFollowup.MobiusWalkEntrySupport

/-! Actual rational-walk support and uniqueness of an endpoint inside a
sufficiently small right-smoothing ball. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory Set
set_option autoImplicit false

theorem identityBall_entry_error {η : ℝ} (hη : 0 < η) {x : RealMobius.Group}
    (hx : x ∈ RealMobius.mobiusIdentityBall η) :
    ∀ i j, |x i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| < η := by
  obtain ⟨h00, h01, h10, h11⟩ := RealMobius.mobiusIdentityBall_entry_bounds hη hx
  intro i j
  fin_cases i <;> fin_cases j <;> simpa using (by assumption)

theorem identityBall_mul_inv_entry_error {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    {u v : RealMobius.Group} (hu : u ∈ RealMobius.mobiusIdentityBall η)
    (hv : v ∈ RealMobius.mobiusIdentityBall η) :
    ∀ i j, |(u * v⁻¹) i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 8 * η := by
  have hui : u⁻¹ ∈ RealMobius.mobiusIdentityBall η := by
    change RealMobius.mobiusIdentityDistanceSq u⁻¹ < η ^ 2
    rw [real_identityDistanceSq_inv]
    exact hu
  have hvi : v⁻¹ ∈ RealMobius.mobiusIdentityBall η := by
    change RealMobius.mobiusIdentityDistanceSq v⁻¹ < η ^ 2
    rw [real_identityDistanceSq_inv]
    exact hv
  have hb : ∀ i j, |(u⁻¹)⁻¹ i j| ≤ 2 := by
    intro i j
    simpa only [inv_inv] using RealMobius.mobiusIdentityBall_subset_entryBox_two hη hη1 hu i j
  have hc : ∀ i j, |v⁻¹ i j - u⁻¹ i j| ≤ 2 * η := by
    intro i j
    have hvj := identityBall_entry_error hη hvi i j
    have huj := identityBall_entry_error hη hui i j
    have ht := abs_sub_le (v⁻¹ i j) ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j) (u⁻¹ i j)
    rw [abs_sub_comm ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)] at ht
    linarith
  simpa only [inv_inv, show (2 : ℝ) * 2 * (2 * η) = 8 * η by ring] using
    real_inv_mul_entry_error hb hc

theorem denominatorCarrier_smoothing_unique {D : ℕ} (hD : 0 < D)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hscale : 8 * η < 1 / (D : ℝ) ^ 2)
    {a b x : RealMobius.Group} (ha : a ∈ denominatorCarrier D)
    (hb : b ∈ denominatorCarrier D)
    (hax : a⁻¹ * x ∈ RealMobius.mobiusIdentityBall η)
    (hbx : b⁻¹ * x ∈ RealMobius.mobiusIdentityBall η) : a = b := by
  by_contra hab
  have hab' : a⁻¹ * b ≠ 1 := by
    intro he
    apply hab
    have h := congrArg (fun z => a * z) he
    simpa using h.symm
  have hr := denominatorCarrier_mul (denominatorCarrier_inv ha) hb
  obtain ⟨i, j, hsep⟩ := denominatorCarrier_separated (Nat.mul_pos hD hD) hr
    (denominatorCarrier_one (D * D)) hab'
  have hnear := identityBall_mul_inv_entry_error hη hη1 hax hbx i j
  have he : (a⁻¹ * x) * (b⁻¹ * x)⁻¹ = a⁻¹ * b := by group
  rw [he] at hnear
  have hsep' : 1 / (D : ℝ) ^ 2 ≤ |(a⁻¹ * b) i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| := by
    change 1 / (D : ℝ) ^ 2 ≤ |(a⁻¹ * b) i j - (1 : RealMobius.Group) i j|
    simpa only [Nat.cast_mul, pow_two] using hsep
  linarith

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem mconv_ae_denominatorCarrier (μ ν : Measure RealMobius.Group) [SFinite ν]
    {D E : ℕ} (hμ : ∀ᵐ g ∂μ, g ∈ denominatorCarrier D)
    (hν : ∀ᵐ g ∂ν, g ∈ denominatorCarrier E) :
    ∀ᵐ g ∂μ ∗ₘ ν, g ∈ denominatorCarrier (D * E) := by
  have hs := denominatorCarrier_measurableSet (D * E)
  rw [Measure.mconv]
  apply (ae_map_iff (p := fun g => g ∈ denominatorCarrier (D * E))
    measurable_mul.aemeasurable hs).mpr
  apply (Measure.ae_prod_iff_ae_ae (hs.preimage measurable_mul)).mpr
  filter_upwards [hμ] with g hg
  exact hν.mono (fun h hh => denominatorCarrier_mul hg hh)

theorem symmetricGeneratorMeasure_ae_denominatorCarrier {m D : ℕ} (g : Fin m → Group)
    (hg : ∀ i, HasDenominator D (g i)) :
    ∀ᵐ a ∂ RealMobius.symmetricGeneratorMeasure (realEmbedding ∘ g), a ∈ denominatorCarrier D := by
  unfold RealMobius.symmetricGeneratorMeasure
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro i _
  rw [ae_add_measure_iff]
  have hi : (realEmbedding ∘ g) i ∈ denominatorCarrier D := ⟨g i, hg i, rfl⟩
  exact ⟨(ae_dirac_iff (denominatorCarrier_measurableSet D)).mpr hi,
    (ae_dirac_iff (denominatorCarrier_measurableSet D)).mpr (denominatorCarrier_inv hi)⟩

theorem generatorWalkMeasure_ae_denominatorCarrier {m D : ℕ} (g : Fin m → Group) (hm : 0 < m)
    (hg : ∀ i, HasDenominator D (g i)) (n : ℕ) :
    ∀ᵐ a ∂ RealMobius.generatorWalkMeasure (realEmbedding ∘ g) n, a ∈ denominatorCarrier (D ^ n) := by
  induction n with
  | zero =>
    simp only [RealMobius.generatorWalkMeasure, pow_zero]
    exact (ae_dirac_iff (denominatorCarrier_measurableSet 1)).mpr (denominatorCarrier_one 1)
  | succ n ih =>
    have : IsProbabilityMeasure (RealMobius.generatorWalkMeasure (realEmbedding ∘ g) n) :=
      RealMobius.generatorWalkMeasure_probability _ hm n
    have h := mconv_ae_denominatorCarrier
      (RealMobius.symmetricGeneratorMeasure (realEmbedding ∘ g))
      (RealMobius.generatorWalkMeasure (realEmbedding ∘ g) n)
      (symmetricGeneratorMeasure_ae_denominatorCarrier g hg) ih
    simpa only [RealMobius.generatorWalkMeasure, pow_succ'] using h

end TransposeFollowup.RationalFreePair

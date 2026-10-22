import TransposeFollowup.AutocorrelationIterates

/-! Existing autocorrelation maximum and probability bounds imply
monotone energy. A finite descent argument then turns contraction above
a threshold into a bound at a fixed, scale-independent iterate. -/
namespace TransposeFollowup
open Classical MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem antitone_energy_threshold_descent {V : ℕ → ℝ≥0∞} {q B C : ℝ≥0∞} {k : ℕ}
    (hmono : Antitone V) (hzero : V 0 ≤ C) (hterminal : q^k*C ≤ B)
    (hdrop : ∀ i : ℕ, i < k → B ≤ V i → V (i+1) ≤ q*V i) : V k ≤ B := by
  by_contra hfail
  have hhigh : B < V k := lt_of_not_ge hfail
  have hbound (i : ℕ) (hi : i ≤ k) : V i ≤ q^i*C := by
    induction i with
    | zero => simpa only [pow_zero, one_mul] using hzero
    | succ i ih =>
      have hik : i < k := by omega
      calc
        V (i+1) ≤ q*V i := hdrop i hik (hhigh.le.trans (hmono hik.le))
        _ ≤ q*(q^i*C) := by gcongr; exact ih hik.le
        _ = q^(i+1)*C := by rw [pow_succ]; ac_rfl
  exact (not_lt_of_ge ((hbound k le_rfl).trans hterminal)) hhigh

end TransposeFollowup

namespace TransposeFollowup.RealMobius
open Classical MeasureTheory
open scoped ENNReal
set_option autoImplicit false
variable [MeasurableSpace Group] [BorelSpace Group]

theorem smoothedAutocorrelationIterate_succ_le_energy (μ : Measure Group) [SFinite μ]
    (η : ℝ) (i : ℕ) (x : Group) :
    smoothedAutocorrelationIterate μ η (i+1) x ≤
      ∫⁻ y, smoothedAutocorrelationIterate μ η i y^2 ∂(Measure.haar : Measure Group) := by
  rw [← smoothedAutocorrelationIterate_energy]
  exact autocorrelationDensity_le_one Measure.haar (smoothedAutocorrelationIterate_measurable μ η i) x

theorem smoothedAutocorrelationIterate_energy_antitone (μ : Measure Group) [IsProbabilityMeasure μ]
    {η : ℝ} (hη : 0 < η) :
    Antitone (fun i : ℕ => ∫⁻ y, smoothedAutocorrelationIterate μ η i y^2 ∂(Measure.haar : Measure Group)) := by
  apply antitone_nat_of_succ_le
  intro i
  rw [← smoothedAutocorrelationIterate_energy μ η (i+1)]
  have := smoothedAutocorrelationIterate_probability μ hη (i+1)
  have : IsProbabilityMeasure ((Measure.haar.withDensity (smoothedAutocorrelationIterate μ η (i+1))).inv) :=
    inv_measure_probability _
  exact leftConvolutionDensity_le _ (smoothedAutocorrelationIterate_succ_le_energy μ η i) 1

end TransposeFollowup.RealMobius

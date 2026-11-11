import SharedDecoders.CapacityMaskRunProbability
import SharedDecoders.CapacityMaskIsolationProbability
import SharedDecoders.CapacityMaskConditioning

/-! # Exact logarithmic deviations, conditioning, and numerical floors -/

namespace SharedDecoders.CapacityMaskProbability

open scoped BigOperators

noncomputable def logDeviation (a : ℝ) (d : ℕ) : ℝ := Real.sqrt (a*Real.log d/d)

theorem logDeviation_nonneg (a : ℝ) (d : ℕ) : 0≤logDeviation a d := Real.sqrt_nonneg _

theorem logDeviation_sq (a : ℝ) (ha : 0≤a) (d : ℕ) (hd : 1≤d) :
    logDeviation a d^2=a*Real.log d/d := by
  apply Real.sq_sqrt
  have hh : (0 : ℝ)≤Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  positivity

theorem logarithmic_union_failure (d : ℕ) (hd : 1<d) :
    ((d : ℝ)-1)*Real.exp (-3*Real.log d)<1/(d : ℝ)^2 := by
  have hp : (0 : ℝ)<d := by exact_mod_cast (by omega : 0<d)
  have he : Real.exp (-3*Real.log d)=1/(d : ℝ)^3 := by
    rw [show (-3 : ℝ)*Real.log d=-(3*Real.log d) by ring,Real.exp_neg]
    rw [show (3 : ℝ)*Real.log d=(3 : ℕ)*Real.log d by norm_num,Real.exp_nat_mul,
      Real.exp_log hp]
    simp only [one_div]
  rw [he]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ)<(d : ℝ)^2)).mpr
  field_simp
  nlinarith

variable {d : ℕ} [NeZero d]

theorem comparison_log_failure (hd : 1<d) :
    ((d : ℝ)-1)*Real.exp (-(logDeviation 6 d)^2*d/2)<1/(d : ℝ)^2 := by
  rw [logDeviation_sq 6 (by norm_num) d (by omega)]
  have he : -(6*Real.log d/d)*d/2 = -3*Real.log d := by
    have hd0 : (d : ℝ)≠0 := by exact_mod_cast NeZero.ne d
    field_simp
    ring
  rw [he]
  exact logarithmic_union_failure d hd

theorem isolation_log_failure (hd : 1<d) :
    ((d : ℝ)-1)*Real.exp (-2*(logDeviation (27/2) d)^2*d/9)<1/(d : ℝ)^2 := by
  rw [logDeviation_sq (27/2) (by norm_num) d (by omega)]
  have he : -2*((27/2)*Real.log d/d)*d/9 = -3*Real.log d := by
    have hd0 : (d : ℝ)≠0 := by exact_mod_cast NeZero.ne d
    field_simp
    ring
  rw [he]
  exact logarithmic_union_failure d hd

theorem change_bad_log_probability (hd : 1<d) :
    prob (fun p : ZMod d → Bool => ¬ChangeGood (logDeviation 6 d) p)<1/(d : ℝ)^2 :=
  (change_bad_probability _ (logDeviation_nonneg _ _)).trans_lt (comparison_log_failure hd)

theorem equality_bad_log_probability {κ : Type*} [Fintype κ] [Nonempty κ] (hd : 1<d) :
    prob (fun p : ZMod d → κ => ¬EqualityGood (logDeviation 6 d) p)<1/(d : ℝ)^2 :=
  (equality_bad_probability _ (logDeviation_nonneg _ _)).trans_lt (comparison_log_failure hd)

theorem isolation_bad_log_probability (hd : 1<d) :
    prob (fun p : ZMod d → Bool => ¬IsolationGood (logDeviation (27/2) d) p)<1/(d : ℝ)^2 :=
  (isolation_bad_probability _ (logDeviation_nonneg _ _)).trans_lt (isolation_log_failure hd)

theorem binary_allLabels_positive (hd : 1<d) : 0<prob (AllLabels (I := ZMod d) (κ := Bool)) := by
  rw [binary_allLabels_probability]
  have hp : (2 : ℝ)<(2 : ℝ)^d := by
    simpa only [pow_one] using (pow_lt_pow_right₀ (by norm_num : (1 : ℝ)<2) hd)
  have hdiv : 2/(2 : ℝ)^d<1 := (div_lt_one (by positivity)).mpr hp
  linarith

theorem binary_conditioning_bound (hd : 1<d) (P : (ZMod d → Bool) → Prop)
    {a : ℝ} (hP : prob P≤a) : condProb P AllLabels≤a/(1-2/(2 : ℝ)^d) := by
  have hp := binary_allLabels_positive hd
  rw [binary_allLabels_probability] at hp
  exact condProb_le P AllLabels hP (by rw [binary_allLabels_probability]) hp

/-- The stated random-source event under the uniform nonconstant binary law. -/
theorem spectrum_conditioned_probability (hd : 13<d) (ε : ℝ) (hε : 0≤ε) :
    condProb (fun p : ZMod d → Bool => ¬SpectrumGood ε p) AllLabels ≤
      Real.exp (-128*ε^2*d/529)/(1-2/(2 : ℝ)^d) :=
  binary_conditioning_bound (by omega) _ (spectrum_bad_probability hd ε hε)

/-- Final integer flooring loses strictly less than one ambient dimension. -/
theorem floor_normalized_lower (x c N : ℝ) (hN : 0<N) (hx : c*N≤x) :
    c-1/N < (⌊x⌋ : ℝ)/N := by
  have hf : x-1<(⌊x⌋ : ℝ) := Int.sub_one_lt_floor x
  apply (lt_div_iff₀ hN).mpr
  have hN0 := ne_of_gt hN
  field_simp
  nlinarith

/-- Arbitrary mixtures with nonnegative weights preserve the same numerical floor. -/
theorem weighted_floor {J : Type*} [Fintype J] (x w : J → ℝ) (c : ℝ)
    (hw : ∀ j, 0≤w j) (hs : ∑ j, w j=1) (hx : ∀ j, c≤x j) :
    c≤∑ j, w j*x j := by
  calc
    c = ∑ j, w j*c := by rw [← Finset.sum_mul,hs,one_mul]
    _ ≤ ∑ j, w j*x j := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hx j) (hw j))

/-- Pointwise limiting certificates preserve a common numerical lower bound. -/
theorem limit_floor {J : Type*} {l : Filter J} [l.NeBot] (x : J → ℝ) (c L : ℝ)
    (hx : ∀ j, c≤x j) (hlim : Filter.Tendsto x l (nhds L)) : c≤L :=
  ge_of_tendsto hlim (Filter.Eventually.of_forall hx)

end SharedDecoders.CapacityMaskProbability

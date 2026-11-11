import SharedDecoders.CapacityRetentionStabilityData
import Mathlib.Topology.Algebra.Order.Field

/-! Uniform symmetric-retention stability for actual shared-code families. -/

namespace SharedDecoders.RetentionAverage

open Filter
open scoped Topology

theorem gcdCost_tendsto (S : ℕ → Sample) (hd : Tendsto (fun n => (S n).d) atTop atTop) :
    Tendsto (fun n => (S n).gcdCost) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => (S n).gcdCost_nonneg)
    (g := fun n => (Real.sqrt ((S n).d : ℝ))⁻¹)
  · intro n
    have hd' : (0 : ℝ) < (S n).d := by exact_mod_cast NeZero.pos (S n).d
    have hh := meanGcd_le (d := (S n).d)
    have hb : (S n).gcdCost ≤ Real.sqrt ((S n).d : ℝ)/(S n).d := by
      apply (div_le_div_iff₀ (by positivity) hd').mpr
      nlinarith only [hh,hd']
    simpa only [Real.sqrt_div_self] using hb
  · exact tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hd))

/-- Growing class counts are allowed. The only assumptions, besides actual
shared decoding, are the two stated vanishing weighted losses. -/
theorem stability (S : ℕ → Sample)
    (hd : Tendsto (fun n => (S n).d) atTop atTop)
    (hl : Tendsto (fun n => (S n).classes*(S n).loss) atTop (𝓝 0))
    (hg : Tendsto (fun n => (S n).classes*(S n).gcdCost) atTop (𝓝 0))
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n in atTop, (S n).rate ≤ 1/2+eps := by
  let t : ℝ := max 1 (4/eps)
  have ht : 1 ≤ t := le_max_left _ _
  have ht0 : 0 < t := by linarith
  have htail : 2/t^2 ≤ eps/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hbig : 4 ≤ t*eps := (div_le_iff₀ heps).mp (le_max_right _ _)
    have hsq : t ≤ t^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hsq heps.le
    nlinarith only [hbig,hh]
  have hdim : Tendsto (fun n => 1/(2*((S n).d : ℝ))) atTop (𝓝 0) := by
    have hh := (tendsto_const_div_atTop_nhds_zero_nat (1/2 : ℝ)).comp hd
    convert hh using 1
    funext n
    simp only [Function.comp_apply]
    field_simp
  have hw : Tendsto (fun n => (S n).classes*((S n).loss+(S n).gcdCost))
      atTop (𝓝 0) := by
    simpa only [mul_add,add_zero] using hl.add hg
  have he : Tendsto (fun n => 1/(2*((S n).d : ℝ))+
      4*t*((S n).classes*((S n).loss+(S n).gcdCost))) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using hdim.add (tendsto_const_nhds.mul hw)
  filter_upwards [he.eventually_lt_const (show (0 : ℝ) < eps/2 by positivity)] with n hn
  have hh := (S n).tradeoff t ht
  linarith

/-- In particular, a uniformly bounded number of classes and sublinear
missing symmetric dimension force asymptotic rate at most one half. -/
theorem stability_bounded_classes (S : ℕ → Sample)
    (hd : Tendsto (fun n => (S n).d) atTop atTop)
    {M : ℝ} (hM : ∀ n, (S n).classes ≤ M)
    (hl : Tendsto (fun n => (S n).loss) atTop (𝓝 0))
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n in atTop, (S n).rate ≤ 1/2+eps := by
  apply stability S hd (hl := ?_) (hg := ?_) heps
  · apply squeeze_zero (fun n => mul_nonneg (by linarith [(S n).classes_ge_one])
      (S n).loss_bounds.1) (fun n => mul_le_mul_of_nonneg_right (hM n) (S n).loss_bounds.1)
    simpa only [mul_zero] using tendsto_const_nhds.mul hl
  · apply squeeze_zero (fun n => mul_nonneg (by linarith [(S n).classes_ge_one])
      (S n).gcdCost_nonneg) (fun n => mul_le_mul_of_nonneg_right (hM n) (S n).gcdCost_nonneg)
    simpa only [mul_zero] using tendsto_const_nhds.mul (gcdCost_tendsto S hd)

/-- The exact lower-limit inequality for each fixed number of sampled shifts. -/
theorem liminf_rate_le (S : ℕ → Sample)
    (hd : Tendsto (fun n => (S n).d) atTop atTop)
    {M : ℝ} (hM : ∀ n, (S n).classes ≤ M) (k : ℕ) :
    liminf (fun n => (S n).rate) atTop ≤
      1/2+2*M^2/(k+2)^2+(2*(k : ℝ)-1)*liminf (fun n => (S n).loss) atTop := by
  have hdim : Tendsto (fun n => 1/(2*((S n).d : ℝ))) atTop (𝓝 0) := by
    have hh := (tendsto_const_div_atTop_nhds_zero_nat (1/2 : ℝ)).comp hd
    convert hh using 1
    funext n
    simp only [Function.comp_apply]
    field_simp
  have he : Tendsto (fun n => 1/(2*((S n).d : ℝ))+(k : ℝ)*(S n).gcdCost)
      atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using hdim.add (tendsto_const_nhds.mul (gcdCost_tendsto S hd))
  apply LeanMachine.BoundedLiminf.affine_upper (fun n => (S n).rate_bounds.1)
    (fun n => (S n).loss_bounds) he
  intro n
  have hh := (S n).normalized k
  have hm2 := pow_le_pow_left₀ (show 0 ≤ (S n).classes by linarith [(S n).classes_ge_one]) (hM n) 2
  have ht := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm2 (by norm_num : (0 : ℝ) ≤ 2))
    (show 0 ≤ ((k : ℝ)+2)^2 by positivity)
  linarith

/-- A fixed positive gain above one half forces the displayed fixed positive
loss of the symmetric source, uniformly over fields and lane dimensions. -/
theorem fixed_gain_requires_loss (S : ℕ → Sample)
    (hd : Tendsto (fun n => (S n).d) atTop atTop)
    {M : ℝ} (hM : ∀ n, (S n).classes ≤ M)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1/2)
    (hrate : 1/2+eps ≤ liminf (fun n => (S n).rate) atTop) :
    eps*Real.sqrt eps/(12*M) ≤ liminf (fun n => (S n).loss) atTop := by
  let k : ℕ := ⌈2*M/Real.sqrt eps⌉₊
  let L : ℝ := liminf (fun n => (S n).loss) atTop
  have hM1 : 1 ≤ M := le_trans (S 0).classes_ge_one (hM 0)
  have hs : 0 < Real.sqrt eps := Real.sqrt_pos.mpr heps
  have hs2 : (Real.sqrt eps)^2=eps := Real.sq_sqrt heps.le
  have hs1 : Real.sqrt eps ≤ 1 := by nlinarith
  have hklo : 2*M ≤ (k : ℝ)*Real.sqrt eps :=
    (div_le_iff₀ hs).mp (Nat.le_ceil _)
  have hkhi : (k : ℝ)*Real.sqrt eps ≤ 3*M := by
    have hc : (k : ℝ) < 2*M/Real.sqrt eps+1 := Nat.ceil_lt_add_one (by positivity)
    have hm := mul_lt_mul_of_pos_right hc hs
    have he : (2*M/Real.sqrt eps+1)*Real.sqrt eps=2*M+Real.sqrt eps := by field_simp
    rw [he] at hm
    linarith
  have htail : 2*M^2/((k : ℝ)+2)^2 ≤ eps/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hsq := pow_le_pow_left₀ (show 0 ≤ 2*M by positivity) hklo 2
    have hn : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    nlinarith only [hsq,hs2,hn,heps]
  have hl0 : 0 ≤ L := (LeanMachine.BoundedLiminf.bounds (fun n => (S n).loss_bounds)).1
  have hb := liminf_rate_le S hd hM k
  have hlin : eps ≤ 4*(k : ℝ)*L := by
    change _ ≤ 1/2+_+(2*(k : ℝ)-1)*L at hb
    nlinarith only [hb,hrate,htail,hl0]
  have hmul := mul_le_mul_of_nonneg_right hlin hs.le
  have htop := mul_le_mul_of_nonneg_right hkhi (show 0 ≤ 4*L by positivity)
  apply (div_le_iff₀ (by positivity : 0 < 12*M)).mpr
  change eps*Real.sqrt eps ≤ L*(12*M)
  nlinarith only [hmul,htop]

end SharedDecoders.RetentionAverage

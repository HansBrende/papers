import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Real.Sqrt

/-!
# The fluid charging rule

The deterministic analytic part of the charging rule behind the lift selections of low
degeneracy (Theorem D). Put `τ = 2 - √3 ≈ 0.268`, so that `(1 - τ)^2 = 2τ` (`one_sub_tau_sq`).
An edge whose larger label is `y ∈ (0, 1]` distributes one unit of charge over its three
options:

* `a1 y = min 1 (τ / y)` goes to the lift `(y, 1)` of its larger endpoint;
* `a0 y = (1 - τ / y)₊ · (y - τ) / (2y)` goes to the lift `(y, 0)`;
* `b0 y = (1 - τ / y)₊ · (y + τ) / (2y)` goes to the lift `(x, 0)` of its smaller endpoint.

The three charges are nonnegative and sum to `1` (`charges_nonneg`, `charges_sum`).

A vertex with label `u` receives from a neighbour with label `s` the charge `f1 u s` at its
lift `1` and `f0 u s` at its lift `0`. If the neighbour's label is uniform on `[0, 1]`, the
expected charges are `min u τ` and `τ` (`integral_f1`, `integral_f0`); the second identity holds
for every `u ∈ (0, 1]` and is the reason for the choice of `τ`. The file also proves the
pointwise ranges (`f1` takes values in `[0, 1]` and `f0` in `[0, 1/2]`) and the variance bounds
`≤ τ (1 - τ)` (`integral_f1_sq_sub_le`, `integral_f0_sq_sub_le`) that are the inputs of
Bernstein's inequality. Bernstein's inequality itself and the union bound are not formalized.

`AboveHalfRate.LiftSelection` turns the rule into a fractional assignment of the edges of a graph
to their options (`fluidCharge`); its load on the lift `(v, b)` is the sum of `f1` or `f0` over
the neighbours of `v`, and `exists_liftSelection_of_fluid` rounds it to a lift selection of low
degeneracy.

Expected values are interval integrals `∫ s in (0:ℝ)..1, _` against Lebesgue measure.
-/

namespace AboveHalf

namespace Fluid

open MeasureTheory Set intervalIntegral
open scoped Interval

set_option autoImplicit false

/-! ### The threshold `τ` -/

/-- The threshold `τ = 2 - √3 ≈ 0.268`. -/
noncomputable def tau : ℝ := 2 - Real.sqrt 3

private lemma sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- `τ = 2 - √3` is a root of `t^2 - 4t + 1`. -/
theorem tau_sq_sub : tau ^ 2 - 4 * tau + 1 = 0 := by
  unfold tau
  linear_combination sqrt_three_sq

/-- The defining identity of the threshold: `(1 - τ)^2 = 2τ`. -/
theorem one_sub_tau_sq : (1 - tau) ^ 2 = 2 * tau := by
  linear_combination tau_sq_sub

/-- `τ > 0`. -/
theorem tau_pos : 0 < tau := by
  unfold tau
  nlinarith [Real.sqrt_nonneg 3, sqrt_three_sq]

/-- `τ < 1/2`. -/
theorem tau_lt_half : tau < 1 / 2 := by
  unfold tau
  nlinarith [Real.sqrt_nonneg 3, sqrt_three_sq]

/-- `τ < 1`. -/
theorem tau_lt_one : tau < 1 := tau_lt_half.trans (by norm_num)

/-! ### The three charges of an edge -/

/-- The charge that an edge with larger label `y` sends to the lift `(y, 1)`. -/
noncomputable def a1 (y : ℝ) : ℝ := min 1 (tau / y)

/-- The charge that an edge with larger label `y` sends to the lift `(y, 0)`. -/
noncomputable def a0 (y : ℝ) : ℝ := max 0 (1 - tau / y) * ((y - tau) / (2 * y))

/-- The charge that an edge with larger label `y` sends to the lift `(x, 0)` of its smaller
endpoint `x`. -/
noncomputable def b0 (y : ℝ) : ℝ := max 0 (1 - tau / y) * ((y + tau) / (2 * y))

private lemma posPart_of_le {y : ℝ} (hy : 0 < y) (h : y ≤ tau) :
    max 0 (1 - tau / y) = 0 := by
  have : 1 ≤ tau / y := (one_le_div hy).2 h
  exact max_eq_left (by linarith)

private lemma posPart_of_ge {y : ℝ} (hy : 0 < y) (h : tau ≤ y) :
    max 0 (1 - tau / y) = 1 - tau / y := by
  have : tau / y ≤ 1 := (div_le_one hy).2 h
  exact max_eq_right (by linarith)

/-- For `0 < y ≤ τ` the whole charge goes to `(y, 1)`. -/
theorem a1_of_le {y : ℝ} (hy : 0 < y) (h : y ≤ tau) : a1 y = 1 :=
  min_eq_left ((one_le_div hy).2 h)

/-- For `y ≥ τ` the lift `(y, 1)` receives `τ / y`. -/
theorem a1_of_ge {y : ℝ} (hy : 0 < y) (h : tau ≤ y) : a1 y = tau / y :=
  min_eq_right ((div_le_one hy).2 h)

/-- For `0 < y ≤ τ` the lift `(y, 0)` receives nothing. -/
theorem a0_of_le {y : ℝ} (hy : 0 < y) (h : y ≤ tau) : a0 y = 0 := by
  rw [a0, posPart_of_le hy h, zero_mul]

/-- For `y ≥ τ` the lift `(y, 0)` receives `(y - τ)^2 / (2 y^2)`. -/
theorem a0_of_ge {y : ℝ} (hy : 0 < y) (h : tau ≤ y) : a0 y = (y - tau) ^ 2 / (2 * y ^ 2) := by
  rw [a0, posPart_of_ge hy h]
  field_simp

/-- For `0 < y ≤ τ` the lift `(x, 0)` receives nothing. -/
theorem b0_of_le {y : ℝ} (hy : 0 < y) (h : y ≤ tau) : b0 y = 0 := by
  rw [b0, posPart_of_le hy h, zero_mul]

/-- For `y ≥ τ` the lift `(x, 0)` receives `1/2 - τ^2 / (2 y^2)`. -/
theorem b0_of_ge {y : ℝ} (hy : 0 < y) (h : tau ≤ y) : b0 y = 1 / 2 - tau ^ 2 / (2 * y ^ 2) := by
  rw [b0, posPart_of_ge hy h]
  field_simp
  ring

theorem a1_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ a1 y :=
  le_min zero_le_one (div_nonneg tau_pos.le hy.le)

theorem a0_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ a0 y := by
  rcases le_total y tau with h | h
  · rw [a0_of_le hy h]
  · rw [a0_of_ge hy h]
    positivity

theorem b0_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ b0 y :=
  mul_nonneg (le_max_left _ _) (div_nonneg (by linarith [tau_pos]) (by linarith))

/-- The three charges are nonnegative. -/
theorem charges_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ a1 y ∧ 0 ≤ a0 y ∧ 0 ≤ b0 y :=
  ⟨a1_nonneg hy, a0_nonneg hy, b0_nonneg hy⟩

/-- Every edge distributes exactly one unit of charge. -/
theorem charges_sum {y : ℝ} (hy : 0 < y) : a1 y + a0 y + b0 y = 1 := by
  rcases le_total y tau with h | h
  · rw [a1_of_le hy h, a0_of_le hy h, b0_of_le hy h]
    ring
  · rw [a1_of_ge hy h, a0_of_ge hy h, b0_of_ge hy h]
    field_simp
    ring

/-- `a1 y ≤ 1`. -/
theorem a1_le_one (y : ℝ) : a1 y ≤ 1 := min_le_left _ _

/-- `a0 y ≤ 1/2` for `y > 0`. -/
theorem a0_le_half {y : ℝ} (hy : 0 < y) : a0 y ≤ 1 / 2 := by
  rcases le_total y tau with h | h
  · rw [a0_of_le hy h]
    norm_num
  · rw [a0_of_ge hy h, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg tau_pos.le (by linarith : (0 : ℝ) ≤ 2 * y - tau)]

/-- `b0 y ≤ 1/2` for `y > 0`. -/
theorem b0_le_half {y : ℝ} (hy : 0 < y) : b0 y ≤ 1 / 2 := by
  rcases le_total y tau with h | h
  · rw [b0_of_le hy h]
    norm_num
  · rw [b0_of_ge hy h]
    have : 0 ≤ tau ^ 2 / (2 * y ^ 2) := by positivity
    linarith

/-! ### The charges received by a vertex -/

/-- The charge received by the lift `1` of a vertex with label `u` from a neighbour with
label `s`: the neighbour must be the smaller endpoint. -/
noncomputable def f1 (u s : ℝ) : ℝ := if s < u then a1 u else 0

/-- The charge received by the lift `0` of a vertex with label `u` from a neighbour with
label `s`: `a0 u` if the vertex is the larger endpoint, `b0 s` if it is the smaller one. -/
noncomputable def f0 (u s : ℝ) : ℝ := if s < u then a0 u else if u < s then b0 s else 0

/-- The charge at the lift `1` is nonnegative. -/
theorem f1_nonneg {u : ℝ} (hu : 0 < u) (s : ℝ) : 0 ≤ f1 u s := by
  unfold f1
  split_ifs
  · exact a1_nonneg hu
  · exact le_rfl

/-- The charge at the lift `1` is at most `1`. -/
theorem f1_le_one (u s : ℝ) : f1 u s ≤ 1 := by
  unfold f1
  split_ifs
  · exact a1_le_one u
  · exact zero_le_one

/-- The charge at the lift `0` is nonnegative. -/
theorem f0_nonneg {u : ℝ} (hu : 0 < u) (s : ℝ) : 0 ≤ f0 u s := by
  unfold f0
  split_ifs with h1 h2
  · exact a0_nonneg hu
  · exact b0_nonneg (hu.trans h2)
  · exact le_rfl

/-- The charge at the lift `0` is at most `1/2`, for every neighbour label `s`. -/
theorem f0_le_half {u : ℝ} (hu : 0 < u) (s : ℝ) : f0 u s ≤ 1 / 2 := by
  unfold f0
  split_ifs with h1 h2
  · exact a0_le_half hu
  · exact b0_le_half (hu.trans h2)
  · norm_num

/-- One-sided range of the centred charge at the lift `1` (an input of Bernstein's
inequality). -/
theorem f1_sub_le_one {u : ℝ} (hu : 0 < u) (s : ℝ) : f1 u s - min u tau ≤ 1 := by
  have := f1_le_one u s
  have : 0 ≤ min u tau := le_min hu.le tau_pos.le
  linarith

/-- One-sided range of the centred charge at the lift `0` (an input of Bernstein's
inequality). -/
theorem f0_sub_le_one {u : ℝ} (hu : 0 < u) (s : ℝ) : f0 u s - tau ≤ 1 := by
  have := f0_le_half hu s
  linarith [tau_pos]

/-! ### Integrability -/

private lemma measurable_b0 : Measurable b0 := by
  unfold b0
  fun_prop

/-- `s ↦ f1 u s` is measurable. -/
theorem measurable_f1 (u : ℝ) : Measurable (f1 u) := by
  unfold f1
  exact Measurable.ite measurableSet_Iio measurable_const measurable_const

/-- `s ↦ f0 u s` is measurable. -/
theorem measurable_f0 (u : ℝ) : Measurable (f0 u) := by
  unfold f0
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_b0 measurable_const)

/-- A measurable function bounded on `Ι a b` is interval integrable on `[a, b]`. -/
private lemma intervalIntegrable_of_abs_le {g : ℝ → ℝ} (hg : Measurable g) {C a b : ℝ}
    (hC : ∀ s ∈ Ι a b, |g s| ≤ C) : IntervalIntegrable g volume a b := by
  refine (intervalIntegrable_const (c := C)).mono_fun' hg.aestronglyMeasurable ?_
  have : ∀ᵐ s ∂volume, s ∈ Ι a b → ‖g s‖ ≤ C :=
    Filter.Eventually.of_forall fun s hs => by simpa [Real.norm_eq_abs] using hC s hs
  exact (ae_restrict_iff' measurableSet_uIoc).2 this

/-- `s ↦ f1 u s` is interval integrable on every interval. -/
theorem f1_intervalIntegrable {u : ℝ} (hu : 0 < u) (a b : ℝ) :
    IntervalIntegrable (f1 u) volume a b :=
  intervalIntegrable_of_abs_le (measurable_f1 u) (C := 1) fun s _ => by
    rw [abs_of_nonneg (f1_nonneg hu s)]
    exact f1_le_one u s

/-- `s ↦ f0 u s` is interval integrable on every interval. -/
theorem f0_intervalIntegrable {u : ℝ} (hu : 0 < u) (a b : ℝ) :
    IntervalIntegrable (f0 u) volume a b :=
  intervalIntegrable_of_abs_le (measurable_f0 u) (C := 1 / 2) fun s _ => by
    rw [abs_of_nonneg (f0_nonneg hu s)]
    exact f0_le_half hu s

private lemma b0_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable b0 volume a b := by
  refine intervalIntegrable_of_abs_le measurable_b0 (C := 1 / 2) fun s hs => ?_
  have hs0 : 0 < s := by
    rcases hs with ⟨h1, -⟩
    exact (lt_min ha hb).trans h1
  rw [abs_of_nonneg (b0_nonneg hs0)]
  exact b0_le_half hs0

/-! ### Expected charges -/

/-- The integral over `[0, 1]` of a function that equals the constant `c` below `u` and
`g` above `u`. -/
private lemma integral_step {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {F g : ℝ → ℝ} (c : ℝ)
    (hF : ∀ a b, IntervalIntegrable F volume a b)
    (hlo : ∀ s, s < u → F s = c) (hhi : ∀ s, u < s → F s = g s) :
    ∫ s in (0 : ℝ)..1, F s = u * c + ∫ s in u..1, g s := by
  rw [← integral_add_adjacent_intervals (hF 0 u) (hF u 1)]
  congr 1
  · rw [integral_congr_Ioo_of_le hu0 (g := fun _ => c) (fun s hs => hlo s hs.2),
      intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  · exact integral_congr_Ioo_of_le hu1 fun s hs => hhi s hs.1

/-- On `[τ, ∞)` the charge `b0` has the antiderivative `s / 2 + τ^2 / (2s)`. -/
private lemma integral_b0 {a b : ℝ} (ha : tau ≤ a) (hab : a ≤ b) :
    ∫ s in a..b, b0 s = (b / 2 + tau ^ 2 / 2 * b⁻¹) - (a / 2 + tau ^ 2 / 2 * a⁻¹) := by
  have ha0 : 0 < a := tau_pos.trans_le ha
  have hmem : ∀ s ∈ uIcc a b, tau ≤ s ∧ 0 < s := fun s hs => by
    rw [uIcc_of_le hab] at hs
    exact ⟨ha.trans hs.1, ha0.trans_le hs.1⟩
  rw [integral_congr (g := fun s => 1 / 2 - tau ^ 2 / (2 * s ^ 2))
    fun s hs => b0_of_ge (hmem s hs).2 (hmem s hs).1]
  have hderiv : ∀ s ∈ uIcc a b, HasDerivAt (fun x : ℝ => x / 2 + tau ^ 2 / 2 * x⁻¹)
      (1 / 2 - tau ^ 2 / (2 * s ^ 2)) s := by
    intro s hs
    have hs0 : s ≠ 0 := (hmem s hs).2.ne'
    refine (((hasDerivAt_id' s).div_const 2).add
      ((hasDerivAt_inv hs0).const_mul (tau ^ 2 / 2))).congr_deriv ?_
    field_simp
    ring
  refine integral_eq_sub_of_hasDerivAt hderiv ?_
  refine ContinuousOn.intervalIntegrable ?_
  refine continuousOn_const.sub (continuousOn_const.div (by fun_prop) fun s hs => ?_)
  have := (hmem s hs).2
  positivity

/-- **Expected charge at the lift `1`.** For a vertex with label `u ∈ (0, 1]` and a neighbour
with a uniform label, the expected charge received by the lift `1` is `min u τ`. -/
theorem integral_f1 {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    ∫ s in (0 : ℝ)..1, f1 u s = min u tau := by
  rw [integral_step hu.le hu1 (g := fun _ => 0) (a1 u) (f1_intervalIntegrable hu)
    (fun s hs => by simp [f1, hs]) (fun s hs => by simp [f1, not_lt.2 hs.le]),
    intervalIntegral.integral_zero, add_zero, a1, mul_min_of_nonneg _ _ hu.le, mul_one,
    mul_div_cancel₀ _ hu.ne']

/-- **Expected charge at the lift `0`.** For a vertex with label `u ∈ (0, 1]` and a neighbour
with a uniform label, the expected charge received by the lift `0` is exactly `τ`. -/
theorem integral_f0 {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    ∫ s in (0 : ℝ)..1, f0 u s = tau := by
  rw [integral_step hu.le hu1 (g := b0) (a0 u) (f0_intervalIntegrable hu)
    (fun s hs => by simp [f0, hs])
    (fun s hs => by simp [f0, not_lt.2 hs.le, hs])]
  have hτ := one_sub_tau_sq
  have hτ0 := tau_pos.ne'
  rcases le_total u tau with h | h
  · -- `u ≤ τ`: the lift `0` of the vertex receives charge only as the smaller endpoint.
    have hzero : ∫ s in u..tau, b0 s = 0 := by
      rw [integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_, intervalIntegral.integral_zero]
      rw [uIcc_of_le h] at hs
      exact b0_of_le (hu.trans_le hs.1) hs.2
    rw [a0_of_le hu h, mul_zero, zero_add,
      ← integral_add_adjacent_intervals (b0_intervalIntegrable hu tau_pos)
        (b0_intervalIntegrable tau_pos one_pos),
      hzero, zero_add, integral_b0 le_rfl tau_lt_one.le]
    field_simp
    linear_combination hτ
  · -- `τ ≤ u`
    rw [a0_of_ge hu h, integral_b0 h hu1]
    field_simp
    linear_combination u * hτ

/-! ### Second moments -/

/-- `s ↦ (f1 u s)^2` is interval integrable on every interval. -/
theorem f1_sq_intervalIntegrable {u : ℝ} (hu : 0 < u) (a b : ℝ) :
    IntervalIntegrable (fun s => (f1 u s) ^ 2) volume a b :=
  intervalIntegrable_of_abs_le ((measurable_f1 u).pow_const 2) (C := 1) fun s _ => by
    rw [abs_of_nonneg (sq_nonneg _)]
    have h0 := f1_nonneg hu s
    have h1 := f1_le_one u s
    nlinarith

/-- `s ↦ (f0 u s)^2` is interval integrable on every interval. -/
theorem f0_sq_intervalIntegrable {u : ℝ} (hu : 0 < u) (a b : ℝ) :
    IntervalIntegrable (fun s => (f0 u s) ^ 2) volume a b :=
  intervalIntegrable_of_abs_le ((measurable_f0 u).pow_const 2) (C := 1) fun s _ => by
    rw [abs_of_nonneg (sq_nonneg _)]
    have h0 := f0_nonneg hu s
    have h1 := f0_le_half hu s
    nlinarith

/-- The variance of the charge at the lift `1` is at most `τ (1 - τ)`. -/
theorem integral_f1_sq_sub_le {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    (∫ s in (0 : ℝ)..1, (f1 u s) ^ 2) - (∫ s in (0 : ℝ)..1, f1 u s) ^ 2 ≤ tau * (1 - tau) := by
  have hsq : ∫ s in (0 : ℝ)..1, (f1 u s) ^ 2 = u * a1 u ^ 2 := by
    rw [integral_step hu.le hu1 (g := fun _ => 0) (a1 u ^ 2) (f1_sq_intervalIntegrable hu)
      (fun s hs => by simp [f1, hs]) (fun s hs => by simp [f1, not_lt.2 hs.le]),
      intervalIntegral.integral_zero, add_zero]
  rw [hsq, integral_f1 hu hu1]
  rcases le_total u tau with h | h
  · rw [a1_of_le hu h, min_eq_left h]
    nlinarith [mul_nonneg (sub_nonneg.2 h) (by linarith [tau_lt_half] : (0 : ℝ) ≤ 1 - u - tau)]
  · rw [a1_of_ge hu h, min_eq_right h]
    have h1 : tau ^ 2 / u ≤ tau := by
      rw [div_le_iff₀ hu]
      nlinarith [tau_pos]
    have h2 : u * (tau / u) ^ 2 = tau ^ 2 / u := by
      field_simp
    nlinarith

/-- The second moment of the charge at the lift `0` is at most `τ / 2`: the charge takes values
in `[0, 1/2]` and has mean `τ`. -/
theorem integral_f0_sq_le {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    ∫ s in (0 : ℝ)..1, (f0 u s) ^ 2 ≤ tau / 2 := by
  calc ∫ s in (0 : ℝ)..1, (f0 u s) ^ 2 ≤ ∫ s in (0 : ℝ)..1, 1 / 2 * f0 u s := by
        refine integral_mono_on zero_le_one (f0_sq_intervalIntegrable hu 0 1)
          ((f0_intervalIntegrable hu 0 1).const_mul (1 / 2)) fun s _ => ?_
        have h0 := f0_nonneg hu s
        have h1 := f0_le_half hu s
        nlinarith
    _ = tau / 2 := by
        rw [intervalIntegral.integral_const_mul, integral_f0 hu hu1]
        ring

/-- The variance of the charge at the lift `0` is at most `τ (1 - τ)`. -/
theorem integral_f0_sq_sub_le {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    (∫ s in (0 : ℝ)..1, (f0 u s) ^ 2) - (∫ s in (0 : ℝ)..1, f0 u s) ^ 2 ≤ tau * (1 - tau) := by
  rw [integral_f0 hu hu1]
  have := integral_f0_sq_le hu hu1
  nlinarith [tau_pos]

end Fluid

end AboveHalf

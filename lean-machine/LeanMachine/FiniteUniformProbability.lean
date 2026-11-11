import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-! # Exact finite uniform laws and the bounded-interval mgf bound

All probabilities are literal normalized counts on finite spaces. Product
averages express the independent uniform law. The analytic input is Mathlib's
proved Hoeffding lemma, with the full interval length (not a doubled bound).
-/

namespace LeanMachine.FiniteProbability

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def avg (f : α → ℝ) : ℝ := 𝔼 x, f x

theorem avg_eq_sum_div_card (f : α → ℝ) :
    avg f = (∑ x, f x)/(Fintype.card α : ℝ) :=
  Fintype.expect_eq_sum_div_card f

theorem avg_const [Nonempty α] (c : ℝ) : avg (fun _ : α => c)=c :=
  Fintype.expect_const c

theorem avg_add (f g : α → ℝ) : avg (fun x => f x+g x)=avg f+avg g :=
  Finset.expect_add_distrib _ _ _

theorem avg_sub (f g : α → ℝ) : avg (fun x => f x-g x)=avg f-avg g :=
  Finset.expect_sub_distrib _ _ _

theorem avg_const_mul (c : ℝ) (f : α → ℝ) : avg (fun x => c*f x)=c*avg f :=
  (Finset.mul_expect _ _ _).symm

theorem avg_mul_const (f : α → ℝ) (c : ℝ) : avg (fun x => f x*c)=avg f*c :=
  (Finset.expect_mul _ _ _).symm

theorem avg_neg (f : α → ℝ) : avg (fun x => -f x) = -avg f := by
  simpa only [neg_one_mul] using avg_const_mul (-1) f

theorem avg_sum {J : Type*} [Fintype J] (f : J → α → ℝ) :
    avg (fun x => ∑ j, f j x) = ∑ j, avg (f j) :=
  Finset.expect_sum_comm _ _ _

theorem avg_mono {f g : α → ℝ} (h : ∀ x, f x≤g x) : avg f≤avg g :=
  Finset.expect_le_expect (fun x _ => h x)

theorem avg_nonneg {f : α → ℝ} (h : ∀ x, 0≤f x) : 0≤avg f :=
  Finset.expect_nonneg (fun x _ => h x)

theorem avg_le [Nonempty α] {f : α → ℝ} {c : ℝ} (h : ∀ x, f x≤c) : avg f≤c :=
  Finset.expect_le Finset.univ_nonempty (fun x _ => h x)

theorem le_avg [Nonempty α] {f : α → ℝ} {c : ℝ} (h : ∀ x, c≤f x) : c≤avg f :=
  Finset.le_expect Finset.univ_nonempty (fun x _ => h x)

theorem avg_equiv (e : α ≃ β) (f : β → ℝ) : avg (fun x => f (e x))=avg f :=
  Fintype.expect_equiv e _ _ (fun _ => rfl)

theorem avg_product (f : α × β → ℝ) : avg f=avg (fun x => avg (fun y => f (x,y))) := by
  exact (show (𝔼 z ∈ (Finset.univ : Finset α) ×ˢ (Finset.univ : Finset β), f z) = _ from
    Finset.expect_product _ _ _)

theorem avg_cons {κ : Type*} [Fintype κ] {n : ℕ}
    (f : (Fin (n+1) → κ) → ℝ) :
    avg f = avg (fun x : κ => avg (fun y : Fin n → κ => f (Fin.cons x y))) := by
  have he := avg_equiv (Fin.consEquiv (fun _ : Fin (n+1) => κ)) f
  exact he.symm.trans (avg_product _)

theorem uniform_integral_eq_avg [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) :
    (∫ x, f x ∂(PMF.uniformOfFintype α).toMeasure) = avg f := by
  rw [PMF.integral_eq_sum, avg_eq_sum_div_card]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← Finset.mul_sum, div_eq_inv_mul]

/-- A finite random variable whose pairwise differences are at most `c` has
the exact bounded-interval mgf estimate after centering at its actual mean. -/
theorem avg_exp_centered_le [Nonempty α] (f : α → ℝ) (c : ℝ) (hc : 0≤c)
    (hchange : ∀ x y, |f x-f y|≤c) (t : ℝ) :
    avg (fun x => Real.exp (t*(f x-avg f))) ≤ Real.exp (c^2*t^2/8) := by
  classical
  let : MeasurableSpace α := ⊤
  let μ := (PMF.uniformOfFintype α).toMeasure
  obtain ⟨x₀,hmin⟩ := Finite.exists_min f
  have hm : AEMeasurable f μ := (measurable_of_countable f).aemeasurable
  have hbound : ∀ᵐ x ∂μ, f x ∈ Set.Icc (f x₀) (f x₀+c) :=
    Filter.Eventually.of_forall fun x => ⟨hmin x, by
      have hh := (abs_le.mp (hchange x x₀)).2
      linarith⟩
  have h := (hasSubgaussianMGF_of_mem_Icc hm hbound).mgf_le t
  change (∫ x, Real.exp (t*(f x-(∫ y, f y ∂μ))) ∂μ) ≤ _ at h
  simp only [μ, uniform_integral_eq_avg] at h
  have hexp : (((‖f x₀+c-f x₀‖₊/2)^2 : ℝ≥0) : ℝ)*t^2/2 = c^2*t^2/8 := by
    simp only [add_sub_cancel_left, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat,
      coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hc]
    ring
  rwa [hexp] at h

noncomputable def prob (P : α → Prop) : ℝ := by
  classical
  exact avg (fun x => if P x then 1 else 0)

theorem prob_nonneg (P : α → Prop) : 0≤prob P := by
  classical
  exact avg_nonneg (fun x => by split <;> norm_num)

theorem prob_le_one [Nonempty α] (P : α → Prop) : prob P≤1 := by
  classical
  exact avg_le (fun x => by split <;> norm_num)

theorem prob_mono {P Q : α → Prop} (h : ∀ x, P x → Q x) : prob P≤prob Q := by
  classical
  apply avg_mono
  intro x
  by_cases hp : P x
  · simp [hp,h x hp]
  · by_cases hq : Q x <;> simp [hp,hq]

open Classical in
theorem prob_eq_card (P : α → Prop) :
    prob P = (Fintype.card {x // P x} : ℝ)/(Fintype.card α : ℝ) := by
  classical
  rw [prob, avg_eq_sum_div_card]
  congr 1
  simp [Fintype.card_subtype, Finset.sum_boole]

theorem prob_exists_le_sum {J : Type*} [Fintype J] (P : J → α → Prop) :
    prob (fun x => ∃ j, P j x) ≤ ∑ j, prob (P j) := by
  classical
  simp only [prob]
  rw [← avg_sum]
  apply avg_mono
  intro x
  by_cases h : ∃ j, P j x
  · obtain ⟨j,hj⟩ := h
    rw [ite_eq_left ⟨j,hj⟩]
    have hh := Finset.single_le_sum
      (s := Finset.univ) (f := fun j => if P j x then (1 : ℝ) else 0)
      (fun j _ => by split <;> norm_num) (Finset.mem_univ j)
    simpa only [ite_eq_left hj] using hh
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun j _ => by split <;> norm_num)

end LeanMachine.FiniteProbability

namespace LeanMachine.FiniteProbability

open scoped BigOperators

theorem avg_div {α : Type*} [Fintype α] (f : α → ℝ) (a : ℝ) :
    avg (fun x => f x/a)=avg f/a := by
  simp only [div_eq_mul_inv,avg_mul_const]

theorem avg_finset_sum {α J : Type*} [Fintype α] (S : Finset J) (f : J → α → ℝ) :
    avg (fun x => ∑ j∈S, f j x)=∑ j∈S, avg (f j) := Finset.expect_sum_comm _ _ _

end LeanMachine.FiniteProbability

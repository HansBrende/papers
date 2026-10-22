import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A finite fractional cover of the nonedges of a bounded-degree graph by
independent sets, constructed by independent Bernoulli marks and isolation. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false

namespace FractionalIndependentCover

variable {V : Type*} [Fintype V]

/-- The product weight of a Boolean marking. -/
noncomputable def markWeight (p : ℝ) (m : V → Bool) : ℝ :=
  ∏ v, if m v then p else 1 - p

theorem markWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (m : V → Bool) :
    0 ≤ markWeight p m := by
  apply Finset.prod_nonneg
  intro v _
  split <;> linarith

theorem sum_product (f : V → Bool → ℝ) :
    (∑ m : V → Bool, ∏ v, f v (m v)) = ∏ v, ∑ b : Bool, f v b := by
  exact (Fintype.prod_sum f).symm

theorem sum_markWeight (p : ℝ) : ∑ m : V → Bool, markWeight p m = 1 := by
  unfold markWeight
  rw [sum_product (fun _ b => if b then p else 1 - p)]
  simp

/-- Keep precisely the marked vertices having no marked neighbor. -/
noncomputable def retained (G : SimpleGraph V) (m : V → Bool) : Finset V :=
  Finset.univ.filter (fun v => m v = true ∧ ∀ u, G.Adj v u → m u = false)

@[simp] theorem mem_retained (G : SimpleGraph V) (m : V → Bool) (v : V) :
    v ∈ retained G m ↔ m v = true ∧ ∀ u, G.Adj v u → m u = false := by
  simp [retained]

theorem retained_independent (G : SimpleGraph V) (m : V → Bool) :
    G.IsIndepSet (retained G m : Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro v hv u hu _ hadj
  have h1 := (mem_retained G m v).mp hv
  have h2 := (mem_retained G m u).mp hu
  simpa [h2.1] using h1.2 u hadj

private def pairConstraint (G : SimpleGraph V) (i j v : V) (b : Bool) : Prop :=
  (v = i ∨ v = j → b = true) ∧ (G.Adj i v ∨ G.Adj j v → b = false)

private theorem pairConstraint_iff (G : SimpleGraph V) (i j : V) (m : V → Bool) :
    (∀ v, pairConstraint G i j v (m v)) ↔ i ∈ retained G m ∧ j ∈ retained G m := by
  simp only [mem_retained, pairConstraint]
  constructor
  · intro h
    exact ⟨⟨(h i).1 (Or.inl rfl), fun u hu => (h u).2 (Or.inl hu)⟩,
      ⟨(h j).1 (Or.inr rfl), fun u hu => (h u).2 (Or.inr hu)⟩⟩
  · rintro ⟨hi, hj⟩ v
    constructor
    · rintro (rfl | rfl)
      · exact hi.1
      · exact hj.1
    · rintro (hv | hv)
      · exact hi.2 v hv
      · exact hj.2 v hv

/-- The exact probability that a nonadjacent pair survives isolation. -/
theorem pair_mass (G : SimpleGraph V) (p : ℝ) (i j : V)
    (hne : i ≠ j) (hadj : ¬ G.Adj i j) :
    (∑ m : V → Bool, if i ∈ retained G m ∧ j ∈ retained G m
      then markWeight p m else 0) =
      p ^ 2 * (1 - p) ^ (G.neighborFinset i ∪ G.neighborFinset j).card := by
  let f : V → Bool → ℝ := fun v b =>
    if pairConstraint G i j v b then (if b then p else 1 - p) else 0
  have hf (v : V) : (∑ b : Bool, f v b) =
      (if v = i then p else 1) * (if v = j then p else 1) *
        (if G.Adj i v ∨ G.Adj j v then 1 - p else 1) := by
    have hji : ¬ G.Adj j i := fun h => hadj h.symm
    by_cases hi : v = i
    · subst v
      simp [f, pairConstraint, hne, hji]
    by_cases hj : v = j
    · subst v
      simp [f, pairConstraint, hne.symm, hadj]
    by_cases ha : G.Adj i v ∨ G.Adj j v
    · simp [f, pairConstraint, hi, hj, ha]
    · simp [f, pairConstraint, hi, hj, ha]
  calc
    _ = ∑ m : V → Bool, ∏ v, f v (m v) := by
      apply Finset.sum_congr rfl
      intro m _
      simp only [f, Fintype.prod_ite_zero, pairConstraint_iff, markWeight]
    _ = ∏ v, ∑ b : Bool, f v b := sum_product f
    _ = _ := by
      simp_rw [hf, Finset.prod_mul_distrib]
      rw [Fintype.prod_ite_eq', Fintype.prod_ite_eq']
      have he : (∏ v : V, if G.Adj i v ∨ G.Adj j v then 1 - p else 1) =
          (1 - p) ^ (G.neighborFinset i ∪ G.neighborFinset j).card := by
        simp_rw [← G.mem_neighborFinset, ← Finset.mem_union]
        rw [Fintype.prod_ite_mem]
        simp
      rw [he]
      ring


/-- The marking probability used for a maximum-degree bound. -/
noncomputable def markingProbability (K : ℕ) : ℝ := 1 / (2 * ((K : ℝ) + 1))

theorem markingProbability_pos (K : ℕ) : 0 < markingProbability K := by
  unfold markingProbability
  positivity

theorem markingProbability_le_one (K : ℕ) : markingProbability K ≤ 1 := by
  unfold markingProbability
  have hK : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  apply (div_le_one (by positivity)).mpr
  linarith

private theorem survival_lower_bound (K n : ℕ) (hn : n ≤ 2 * K) :
    1 / (16 * ((K : ℝ) + 1)^2) ≤
      markingProbability K ^ 2 * (1 - markingProbability K)^n := by
  let p := markingProbability K
  have hp : 0 ≤ p := (markingProbability_pos K).le
  have hp1 : p ≤ 1 := markingProbability_le_one K
  have hb : (1 / 2 : ℝ) ≤ 1 - (K : ℝ) * p := by
    dsimp [p, markingProbability]
    have hd : 0 < 2 * ((K : ℝ) + 1) := by positivity
    have hfrac : (K : ℝ) * (1 / (2 * ((K : ℝ) + 1))) ≤ 1 / 2 := by
      rw [mul_one_div]
      apply (div_le_iff₀ hd).mpr
      nlinarith
    linarith
  have hbern : 1 - (K : ℝ) * p ≤ (1 - p)^K := by
    have h := one_add_mul_le_pow (a := -p) (by linarith : -2 ≤ -p) K
    convert h using 1; ring
  have hhalf := hb.trans hbern
  have hs : (1 / 4 : ℝ) ≤ ((1 - p)^K)^2 := by nlinarith
  have hpow : (1 - p)^(2*K) ≤ (1-p)^n :=
    pow_le_pow_of_le_one (by linarith) (by linarith) hn
  have hquarter : (1 / 4 : ℝ) ≤ (1-p)^n := by
    calc
      _ ≤ ((1-p)^K)^2 := hs
      _ = (1-p)^(2*K) := by rw [← pow_mul]; congr 1; omega
      _ ≤ _ := hpow
  calc
    _ = p^2 * (1 / 4) := by dsimp [p, markingProbability]; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hquarter (sq_nonneg p)

theorem pair_mass_lower_bound (G : SimpleGraph V) (K : ℕ)
    (hdegree : ∀ v, G.degree v ≤ K) (i j : V)
    (hne : i ≠ j) (hadj : ¬ G.Adj i j) :
    1 / (16 * ((K : ℝ) + 1)^2) ≤
      ∑ m : V → Bool, if i ∈ retained G m ∧ j ∈ retained G m
        then markWeight (markingProbability K) m else 0 := by
  rw [pair_mass G _ i j hne hadj]
  apply survival_lower_bound
  calc
    _ ≤ (G.neighborFinset i).card + (G.neighborFinset j).card :=
      Finset.card_union_le _ _
    _ ≤ K + K := Nat.add_le_add (hdegree i) (hdegree j)
    _ = 2 * K := by omega

/-- Push forward the product marking distribution to finite independent sets. -/
noncomputable def weight (G : SimpleGraph V) (K : ℕ) (S : Finset V) : ℝ :=
  ∑ m : V → Bool, if retained G m = S then markWeight (markingProbability K) m else 0

theorem weight_nonneg (G : SimpleGraph V) (K : ℕ) (S : Finset V) :
    0 ≤ weight G K S := by
  apply Finset.sum_nonneg
  intro m _
  split
  · exact markWeight_nonneg (markingProbability_pos K).le (markingProbability_le_one K) m
  · rfl

/-- Finite pushforward integration, also useful for weighted entropy sums. -/
theorem sum_weight_mul (G : SimpleGraph V) (K : ℕ) (f : Finset V → ℝ) :
    (∑ S, weight G K S * f S) =
      ∑ m : V → Bool, markWeight (markingProbability K) m * f (retained G m) := by
  simp only [weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  simp only [ite_mul, zero_mul]
  simp

theorem sum_weight (G : SimpleGraph V) (K : ℕ) : ∑ S, weight G K S = 1 := by
  simpa using (sum_weight_mul G K (fun _ => 1)).trans (by simp [sum_markWeight])

theorem independent_of_weight_pos (G : SimpleGraph V) (K : ℕ) (S : Finset V)
    (hS : 0 < weight G K S) : G.IsIndepSet (S : Set V) := by
  by_contra h
  have hz : weight G K S = 0 := by
    apply Finset.sum_eq_zero
    intro m _
    have hne : retained G m ≠ S := by
      intro he
      exact h (he ▸ retained_independent G m)
    simp [hne]
  linarith

theorem weight_pair_coverage (G : SimpleGraph V) (K : ℕ)
    (hdegree : ∀ v, G.degree v ≤ K) (i j : V)
    (hne : i ≠ j) (hadj : ¬ G.Adj i j) :
    1 / (16 * ((K : ℝ) + 1)^2) ≤
      ∑ S, if i ∈ S ∧ j ∈ S then weight G K S else 0 := by
  have h := sum_weight_mul G K (fun S => if i ∈ S ∧ j ∈ S then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [h]
  exact pair_mass_lower_bound G K hdegree i j hne hadj


/-- The total mass of the cover normalized to give every nonedge mass at least one. -/
noncomputable def coverConstant (K : ℕ) : ℝ := 16 * ((K : ℝ) + 1)^2

theorem coverConstant_pos (K : ℕ) : 0 < coverConstant K := by
  unfold coverConstant
  positivity

/-- Independent-set weights with total mass `16 * (K + 1)^2`. -/
noncomputable def coverWeight (G : SimpleGraph V) (K : ℕ) (S : Finset V) : ℝ :=
  coverConstant K * weight G K S

theorem coverWeight_nonneg (G : SimpleGraph V) (K : ℕ) (S : Finset V) :
    0 ≤ coverWeight G K S :=
  mul_nonneg (coverConstant_pos K).le (weight_nonneg G K S)

theorem sum_coverWeight (G : SimpleGraph V) (K : ℕ) :
    ∑ S, coverWeight G K S = coverConstant K := by
  simp only [coverWeight, ← Finset.mul_sum, sum_weight, mul_one]

theorem independent_of_coverWeight_pos (G : SimpleGraph V) (K : ℕ) (S : Finset V)
    (hS : 0 < coverWeight G K S) : G.IsIndepSet (S : Set V) := by
  apply independent_of_weight_pos G K S
  exact (mul_pos_iff_of_pos_left (coverConstant_pos K)).mp hS

theorem coverWeight_pair_coverage (G : SimpleGraph V) (K : ℕ)
    (hdegree : ∀ v, G.degree v ≤ K) (i j : V)
    (hne : i ≠ j) (hadj : ¬ G.Adj i j) :
    1 ≤ ∑ S, if i ∈ S ∧ j ∈ S then coverWeight G K S else 0 := by
  have h := weight_pair_coverage G K hdegree i j hne hadj
  have hc := coverConstant_pos K
  change 1 / coverConstant K ≤ _ at h
  calc
    1 = coverConstant K * (1 / coverConstant K) := by field_simp
    _ ≤ coverConstant K * ∑ S, if i ∈ S ∧ j ∈ S then weight G K S else 0 :=
      mul_le_mul_of_nonneg_left h hc.le
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      simp only [mul_ite, mul_zero, coverWeight]

end FractionalIndependentCover

/-- Every finite bounded-degree graph has a fractional cover of its nonedges
by independent sets. The weights are explicitly constructed, not a premise. -/
theorem exists_fractional_independent_cover {V : Type*} [Fintype V]
    (G : SimpleGraph V) (K : ℕ) (hdegree : ∀ v, G.degree v ≤ K) :
    ∃ w : Finset V → ℝ,
      (∀ S, 0 ≤ w S) ∧
      (∑ S, w S = 1) ∧
      (∀ S, 0 < w S → G.IsIndepSet (S : Set V)) ∧
      (∀ i j, i ≠ j → ¬ G.Adj i j →
        1 / (16 * ((K : ℝ) + 1)^2) ≤ ∑ S, if i ∈ S ∧ j ∈ S then w S else 0) := by
  exact ⟨FractionalIndependentCover.weight G K,
    FractionalIndependentCover.weight_nonneg G K,
    FractionalIndependentCover.sum_weight G K,
    FractionalIndependentCover.independent_of_weight_pos G K,
    FractionalIndependentCover.weight_pair_coverage G K hdegree⟩

/-- A version normalized to cover every nonedge with weight at least one. -/
theorem exists_fractional_independent_cover_scaled {V : Type*} [Fintype V]
    (G : SimpleGraph V) (K : ℕ) (hdegree : ∀ v, G.degree v ≤ K) :
    ∃ w : Finset V → ℝ,
      (∀ S, 0 ≤ w S) ∧
      (∑ S, w S = 16 * ((K : ℝ) + 1)^2) ∧
      (∀ S, 0 < w S → G.IsIndepSet (S : Set V)) ∧
      (∀ i j, i ≠ j → ¬ G.Adj i j →
        1 ≤ ∑ S, if i ∈ S ∧ j ∈ S then w S else 0) := by
  exact ⟨FractionalIndependentCover.coverWeight G K,
    FractionalIndependentCover.coverWeight_nonneg G K,
    FractionalIndependentCover.sum_coverWeight G K,
    FractionalIndependentCover.independent_of_coverWeight_pos G K,
    FractionalIndependentCover.coverWeight_pair_coverage G K hdegree⟩

end TransposeFollowup

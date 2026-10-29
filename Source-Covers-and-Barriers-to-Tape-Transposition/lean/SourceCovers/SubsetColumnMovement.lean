import SourceCovers.SubsetColumns
import SourceCovers.SubsetCalibration

/-! Finite movement bills for all actual columns of the subset code.
The internal-discard and movement-clock widths remain independent. -/

namespace SourceCovers.SubsetMovement

open Finset LeanMachine LeanMachine.QueryMovement
open scoped BigOperators Classical
noncomputable section

/-- General widths in the already verified interval-query argument. -/
theorem interval_lower_of_widths {ι τ : Type*} [Fintype ι] [Nonempty ι] [DecidableEq τ]
    {L ρ w δ η r : ℝ} {N n k : ℕ} (hL : 0 < L) (hN : 0 < N)
    (hρ : 0 ≤ ρ) (hw : 0 ≤ w) (hδ : 0 < δ) (hη : 0 < η) (hr : 0 < r)
    (T : Finset τ) (S : τ → Finset (Fin N)) (Y : ι → ℕ → AddCircle L)
    (a b : τ → ℕ) (hab : ∀ j ∈ T, a j ≤ b j) (hbn : ∀ j ∈ T, b j ≤ n)
    (hdisj : (T : Set τ).PairwiseDisjoint fun j => Ico (a j) (b j))
    (hsize : ∀ j ∈ T, (S j).card = k)
    (hrepeat : ∀ A ∈ T.image S, r ≤ ((T.filter fun j => S j = A).card : ℝ))
    (hraw : ∀ j ∈ T, ∀ x ∈ S j, ∃ t ∈ Icc (a j) (b j), ∃ i, ∃ z : AddCircle L,
      dist z (QueryMovement.centre L N x) ≤ w ∧ dist z (Y i t) ≤ ρ) :
    let F := (T.image S).card
    let B := (QueryMovement.capacity L (ρ + w + δ + η) N (Fintype.card ι)).choose k
    η * (((F : ℝ) - B) / (B + η / (δ * r))) ≤ elapsed (maxStep Y) n := by
  dsimp only
  have hc : 0 ≤ elapsed (maxStep Y) n := elapsed_nonneg (fun e _ => maxStep_nonneg Y e) le_rfl
  apply (interval_real_bounds_general hc hδ hη hr ?_).2
  apply card_interval_types_le T S (QueryMovement.centre L N) Y a b (maxStep Y) n k
    _ ρ w δ η r hδ hη hr (fun e _ => maxStep_nonneg Y e)
    (fun i e _ => step_le_maxStep Y e i) hab hbn hdisj hsize hrepeat hraw
  intro y
  rw [QueryMovement.centre_eq]
  exact CircleGridCapacity.card_covered_le L (L / (2 * N)) N hL hN y
    (ρ + w + δ + η) (by positivity)

def subsetCapacity (N k m h : ℕ) (lam tau sigma : ℝ) : ℕ :=
  min N (m * (⌊2 * (lam + tau + sigma + 1 / SubsetHelper.side N k h) * N⌋₊ + 1))

theorem row_width_ratio {N k h b : ℕ} (hN : 0 < N) (hk : k ≤ N)
    (hh : 0 < h) (hb : 0 < b) :
    ((SubsetHelper.side N k h : ℝ) * b) / SubsetHelper.inputBits N k h b =
      1 / SubsetHelper.side N k h := by
  have hd : 0 < SubsetHelper.side N k h := by
    unfold SubsetHelper.side
    have hF := Nat.choose_pos hk
    positivity
  have hdR : (SubsetHelper.side N k h : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  simp only [SubsetHelper.inputBits, Nat.cast_mul, Nat.cast_pow]
  field_simp

theorem actual_capacity {N k m h b : ℕ} {lam tau sigma : ℝ}
    (hN : 0 < N) (hk : k ≤ N) (hh : 0 < h) (hb : 0 < b) :
    QueryMovement.capacity (SubsetHelper.inputBits N k h b)
      (lam * SubsetHelper.inputBits N k h b + (SubsetHelper.side N k h : ℝ) * b +
        sigma * SubsetHelper.inputBits N k h b + tau * SubsetHelper.inputBits N k h b) N m =
      subsetCapacity N k m h lam tau sigma := by
  have hL : (SubsetHelper.inputBits N k h b : ℝ) ≠ 0 := by
    exact_mod_cast (SubsetHelper.input_bits_pos hN hk hh hb).ne'
  unfold QueryMovement.capacity subsetCapacity
  congr 4
  rw [← row_width_ratio hN hk hh hb]
  field_simp
  ring

/-- Normalizing the repetition loss uses `r * F = d`. -/
theorem normalize_column_bill {F B r L tau sigma : ℝ}
    (hF : 0 < F) (hr : 0 < r) (hL : 0 < L) (htau : 0 < tau) (hsigma : 0 < sigma) :
    ((tau * L) * ((F - B) / (B + (tau * L) / ((sigma * L) * r)))) / L =
      tau * ((1 - B / F) / (B / F + tau / (sigma * (r * F)))) := by
  field_simp

namespace ColumnQueries

/-- The finite full-column bound, retaining the smaller maximum-step bill.
Its positive repetition penalty also handles zero binomial capacity. -/
theorem finite_lower {N k m h b : ℕ} [NeZero m] {lam tau sigma : ℝ}
    (Q : ColumnQueries N k m h b lam)
    (hN : 0 < N) (hk : k ≤ N) (hh : 0 < h) (hb : 0 < b)
    (hlam : 0 < lam) (htau : 0 < tau) (hsigma : 0 < sigma) :
    let F := (N.choose k : ℝ)
    let B := ((subsetCapacity N k m h lam tau sigma).choose k : ℝ)
    tau * ((1 - B / F) / (B / F + tau / (sigma * SubsetHelper.side N k h))) ≤
      Q.maxCost / SubsetHelper.inputBits N k h b := by
  dsimp only
  have hL : (0 : ℝ) < SubsetHelper.inputBits N k h b := by
    exact_mod_cast SubsetHelper.input_bits_pos hN hk hh hb
  have hF : (0 : ℝ) < N.choose k := by exact_mod_cast Nat.choose_pos hk
  have hr : (0 : ℝ) < N * h := by positivity
  have hbound := interval_lower_of_widths hL hN (by positivity) (by positivity)
    (mul_pos hsigma hL) (mul_pos htau hL) hr
    (univ : Finset (Column N k h)) query Q.path Q.first Q.last
    (fun c _ => Q.ordered c) (fun c _ => Q.bounded c)
    (by simpa only [coe_univ] using Q.disjoint)
    (fun c _ => query_card c) ?_ (fun c _ => Q.cover c)
  · dsimp only at hbound
    rw [card_query_types hN hh, Fintype.card_fin, actual_capacity hN hk hh hb] at hbound
    have hn := div_le_div_of_nonneg_right hbound hL.le
    rw [normalize_column_bill hF hr hL htau hsigma] at hn
    have hd : ((N : ℝ) * h) * N.choose k = SubsetHelper.side N k h := by
      simp only [SubsetHelper.side, Nat.cast_mul]
      ring
    simpa only [hd, maxCost] using hn
  · intro S hS
    have hc : S.card = k := (mem_powersetCard.mp (query_types hN hh ▸ hS)).2
    rw [query_repetitions ⟨S, hc⟩, Nat.cast_mul]

end ColumnQueries
end
end SourceCovers.SubsetMovement

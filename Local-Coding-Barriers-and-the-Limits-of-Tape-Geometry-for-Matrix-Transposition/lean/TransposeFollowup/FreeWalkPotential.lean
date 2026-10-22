import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Tactic

/-! An elementary radial supersolution for a symmetric free-group walk.
The bound is deliberately weaker than the sharp spectral radius. -/
namespace TransposeFollowup.FreeWalk
open Classical FreeGroup
set_option autoImplicit false

variable {α : Type*} [DecidableEq α]

noncomputable def weight (q : ℝ) (x : FreeGroup α) : ℝ := q ^ x.toWord.length

theorem weight_nonneg {q : ℝ} (hq : 0 ≤ q) (x : FreeGroup α) : 0 ≤ weight q x :=
  pow_nonneg hq _

theorem weight_one (q : ℝ) : weight q (1 : FreeGroup α) = 1 := by simp [weight]

theorem weight_le_one {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (x : FreeGroup α) :
    weight q x ≤ 1 := pow_le_one₀ hq hq1

theorem neighbor_weight_le {q : ℝ} (hq : 0 < q) (a : α × Bool) (x : FreeGroup α) :
    weight q ((mk [a])⁻¹ * x) ≤ q * weight q x +
      if x.toWord.head? = some a then q⁻¹ * weight q x else 0 := by
  have he : (mk [a])⁻¹ = mk [(a.1, !a.2)] := by rw [inv_mk]; rfl
  have hw : ((mk [a])⁻¹ * x).toWord =
      if x.toWord.head? = some a then x.toWord.tail else (a.1, !a.2) :: x.toWord := by
    rw [he, toWord_mk_mul_eq]
    simp only [Bool.not_not, Prod.mk.eta]
  by_cases h : x.toWord.head? = some a
  · have hlen : x.toWord.length = x.toWord.tail.length + 1 := by
      cases hx : x.toWord with
      | nil => simp [hx] at h
      | cons b t => simp
    unfold weight
    rw [hw, ite_eq_left h, ite_eq_left h, hlen, pow_succ]
    have hz : 0 ≤ q * (q ^ x.toWord.tail.length * q) := by positivity
    have hi : q⁻¹ * (q ^ x.toWord.tail.length * q) = q ^ x.toWord.tail.length := by
      field_simp
    rw [hi]
    linarith
  · simp only [weight, hw, ite_eq_right h, List.length_cons, pow_succ, add_zero]
    exact (mul_comm _ _).le

theorem sum_head_indicator_le [Fintype α] (x : FreeGroup α) {C : ℝ} (hC : 0 ≤ C) :
    (∑ a : α × Bool, if x.toWord.head? = some a then C else 0) ≤ C := by
  by_cases h : ∃ a, x.toWord.head? = some a
  · obtain ⟨a, ha⟩ := h
    calc
      _ = C := by
        rw [Finset.sum_eq_single a]
        · rw [ite_eq_left ha]
        · intro b _ hba
          rw [ite_eq_right (fun hb => hba (Option.some.inj (hb.symm.trans ha)))]
        · simp
      _ ≤ C := le_rfl
  · have hn : ∀ a, x.toWord.head? ≠ some a := by simpa using h
    simpa only [ite_eq_right (hn _), Finset.sum_const_zero] using hC

theorem sum_neighbor_weight_le [Fintype α] {q : ℝ} (hq : 0 < q) (x : FreeGroup α) :
    (∑ a : α × Bool, weight q ((mk [a])⁻¹ * x)) ≤
      ((2 * Fintype.card α : ℕ) * q + q⁻¹) * weight q x := by
  calc
    _ ≤ ∑ a : α × Bool, (q * weight q x +
        if x.toWord.head? = some a then q⁻¹ * weight q x else 0) :=
      Finset.sum_le_sum (fun a _ => neighbor_weight_le hq a x)
    _ = (2 * Fintype.card α : ℕ) * (q * weight q x) +
        ∑ a : α × Bool, if x.toWord.head? = some a then q⁻¹ * weight q x else 0 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_bool, nsmul_eq_mul, Nat.mul_comm]
    _ ≤ (2 * Fintype.card α : ℕ) * (q * weight q x) + q⁻¹ * weight q x := by
      linarith [sum_head_indicator_le x (show 0 ≤ q⁻¹ * weight q x by
        exact mul_nonneg (inv_nonneg.mpr hq.le) (weight_nonneg hq.le x))]
    _ = _ := by ring

end TransposeFollowup.FreeWalk

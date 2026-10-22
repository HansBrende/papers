import TransposeFollowup.PageOpcode

/-! Regroup the edge-pulse walk by its actual vertex records. The matching
property justifies one three-symbol record per page and vertex. -/

namespace TransposeFollowup

open Classical
open scoped BigOperators
set_option autoImplicit false

theorem event_weight_sum {E V P : Type*} [Fintype E] [Fintype V]
    (endpoint : E → V) (page : E → P) (p : P) (weight : V → ℤ)
    (hunique : ∀ u e f, endpoint e = u ∧ page e = p → endpoint f = u ∧ page f = p → e = f) :
    (∑ u, if ∃ e, endpoint e = u ∧ page e = p then weight u else 0) =
      ∑ e, if page e = p then weight (endpoint e) else 0 := by
  have hfiber (u : V) :
      (if ∃ e, endpoint e = u ∧ page e = p then weight u else 0) =
        ∑ e, if endpoint e = u ∧ page e = p then weight u else 0 := by
    by_cases h : ∃ e, endpoint e = u ∧ page e = p
    · rw [ite_eq_left h]
      obtain ⟨e, he⟩ := h
      symm
      calc
        _ = (if endpoint e = u ∧ page e = p then weight u else 0) := by
          apply Finset.sum_eq_single e
          · intro f _ hfe
            have hn : ¬(endpoint f = u ∧ page f = p) := fun hf => hfe (hunique u f e hf he)
            exact ite_eq_right hn
          · simp
        _ = _ := ite_eq_left he
    · rw [ite_eq_right h]
      symm
      apply Finset.sum_eq_zero
      intro e _
      exact ite_eq_right (fun he => h ⟨e, he⟩)
  simp_rw [hfiber]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hp : page e = p <;> simp [hp]

namespace NestedMatchingPages

variable {v k : ℕ} {G : SimpleGraph (Fin v)} [DecidableRel G.Adj]
    (D : NestedMatchingPages G k)

theorem opcode_weight_sum (p : Fin k) (weight : Fin v → ℤ) :
    (∑ u, (D.opcode u p).direction * weight u) =
      ∑ e : G.edgeFinset, if D.page e = p then weight (D.src e) - weight (D.dst e) else 0 := by
  have hs := event_weight_sum D.src D.page p weight (fun _ _ _ he hf => D.source_unique he hf)
  have ht := event_weight_sum D.dst D.page p weight (fun _ _ _ he hf => D.target_unique he hf)
  calc
    _ = (∑ u, if D.SourceEvent u p then weight u else 0) -
        ∑ u, if D.TargetEvent u p then weight u else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro u _
      rw [D.opcode_direction, sub_mul]
      simp only [ite_mul, one_mul, zero_mul]
    _ = (∑ e, if D.page e = p then weight (D.src e) else 0) -
        ∑ e, if D.page e = p then weight (D.dst e) else 0 := by
      convert congrArg₂ (fun a b : ℤ => a - b) hs ht using 2 <;>
        apply Finset.sum_congr rfl <;> intro u _ <;>
        split_ifs <;> simp_all [SourceEvent, TargetEvent]
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hp : D.page e = p <;> simp [hp]

theorem walk_eq_opcode_sum (r K offset : ℕ) (hr : 0 < r) (hK : 0 < K)
    (p : Fin k) (t : ℕ) :
    D.walk r K offset hr hK p t =
      ∑ u : Fin v, (D.opcode u p).direction *
        cappedRamp (4 * K * r) (start r K offset u + K * r) t := by
  rw [D.opcode_weight_sum]
  rfl

end NestedMatchingPages
end TransposeFollowup

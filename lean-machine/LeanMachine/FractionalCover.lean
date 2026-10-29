import LeanMachine.IntervalCover
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Basic.ENNReal.Basic

set_option autoImplicit false

/-!
# Minimum finite fractional covers

Weights on a finite family may be capped at one. The extreme value theorem
then supplies an actual minimum, including for an empty target. The extended
value is infinite exactly when no feasible cover exists.
-/

namespace LeanMachine.FractionalCover

open Finset
open scoped BigOperators ENNReal
noncomputable section

variable {α ι : Type*} [Fintype ι]

def Covers (S : Finset α) (A : ι → Set α) (w : ι → ℝ) : Prop := by
  classical
  exact (∀ i, 0 ≤ w i) ∧ ∀ a ∈ S, 1 ≤ ∑ i, if a ∈ A i then w i else 0

def cost (w : ι → ℝ) : ℝ := ∑ i, w i

theorem cost_nonneg {S : Finset α} {A : ι → Set α} {w : ι → ℝ}
    (hw : Covers S A w) : 0 ≤ cost w := sum_nonneg fun i _ => hw.1 i

theorem one_le_cost {S : Finset α} (hS : S.Nonempty) {A : ι → Set α}
    {w : ι → ℝ} (hw : Covers S A w) : 1 ≤ cost w := by
  classical
  obtain ⟨a, ha⟩ := hS
  exact (hw.2 a ha).trans (sum_le_sum fun i _ => by
    split_ifs
    · exact le_rfl
    · exact hw.1 i)

theorem cap_covers {S : Finset α} {A : ι → Set α} {w : ι → ℝ}
    (hw : Covers S A w) : Covers S A (fun i => min (w i) 1) := by
  classical
  refine ⟨fun i => le_min (hw.1 i) zero_le_one, fun a ha => ?_⟩
  by_cases h : ∃ i, a ∈ A i ∧ 1 ≤ w i
  · obtain ⟨j, hj, hjw⟩ := h
    have hsingle := single_le_sum (f := fun i => if a ∈ A i then min (w i) 1 else 0)
      (s := univ) (a := j) (fun i _ => by split_ifs; exact le_min (hw.1 i) zero_le_one; rfl)
      (mem_univ j)
    simpa only [ite_eq_left hj, min_eq_right hjw] using hsingle
  · convert hw.2 a ha using 1
    apply sum_congr rfl
    intro i _
    by_cases hai : a ∈ A i
    · have hi : w i ≤ 1 := le_of_not_ge fun hwi => h ⟨i, hai, hwi⟩
      simp only [ite_eq_left hai, min_eq_left hi]
    · simp only [ite_eq_right hai]

theorem cap_cost_le (w : ι → ℝ) : cost (fun i => min (w i) 1) ≤ cost w :=
  sum_le_sum fun _ _ => min_le_left _ _

theorem covers_closed (S : Finset α) (A : ι → Set α) :
    IsClosed {w : ι → ℝ | Covers S A w} := by
  classical
  simp only [Covers, Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter ?_
  exact isClosed_iInter fun a => isClosed_iInter fun _ =>
    isClosed_le continuous_const (continuous_finsetSum _ fun i _ => by
      by_cases h : a ∈ A i
      · simpa only [ite_eq_left h] using continuous_apply (A := fun _ : ι => ℝ) i
      · simpa only [ite_eq_right h] using (continuous_const : Continuous (fun _ : ι → ℝ => (0 : ℝ))))

/-- Every feasible finite fractional-cover problem has a minimum, with all
weights at most one; no linear-programming theorem is needed. -/
theorem exists_minimum {S : Finset α} {A : ι → Set α}
    (h : ∃ w, Covers S A w) :
    ∃ w, Covers S A w ∧ (∀ i, w i ≤ 1) ∧
      ∀ v, Covers S A v → cost w ≤ cost v := by
  classical
  let F := Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ => (1 : ℝ)) ∩ {w | Covers S A w}
  have hcompact : IsCompact F := isCompact_Icc.inter_right (covers_closed S A)
  have hne : F.Nonempty := by
    obtain ⟨w, hw⟩ := h
    exact ⟨fun i => min (w i) 1,
      ⟨⟨fun i => le_min (hw.1 i) zero_le_one, fun _ => min_le_right _ _⟩, cap_covers hw⟩⟩
  have hcont : Continuous (cost : (ι → ℝ) → ℝ) :=
    continuous_finsetSum _ fun i _ => continuous_apply i
  obtain ⟨w, hw, hmin⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  refine ⟨w, hw.2, hw.1.2, fun v hv => ?_⟩
  exact (hmin ⟨⟨fun i => le_min (hv.1 i) zero_le_one,
      fun _ => min_le_right _ _⟩, cap_covers hv⟩).trans (cap_cost_le v)

/-- Real value on feasible instances; use `number` for the infeasible case. -/
def value (S : Finset α) (A : ι → Set α) : ℝ :=
  sInf (cost '' {w | Covers S A w})

theorem exists_optimal {S : Finset α} {A : ι → Set α}
    (h : ∃ w, Covers S A w) :
    ∃ w, Covers S A w ∧ cost w = value S A ∧ (∀ i, w i ≤ 1) := by
  obtain ⟨w, hw, hw1, hmin⟩ := exists_minimum h
  refine ⟨w, hw, ?_, hw1⟩
  symm
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨_, w, hw, rfl⟩
  · rintro c ⟨v, hv, rfl⟩
    exact hmin v hv
  · intro c hc
    exact ⟨cost w, ⟨w, hw, rfl⟩, hc⟩

theorem value_nonneg {S : Finset α} {A : ι → Set α}
    (h : ∃ w, Covers S A w) : 0 ≤ value S A := by
  obtain ⟨w, hw, he, _⟩ := exists_optimal h
  rw [← he]
  exact cost_nonneg hw

theorem one_le_value {S : Finset α} (hS : S.Nonempty) {A : ι → Set α}
    (h : ∃ w, Covers S A w) : 1 ≤ value S A := by
  obtain ⟨w, hw, he, _⟩ := exists_optimal h
  rw [← he]
  exact one_le_cost hS hw

/-- The minimum cover weight, with infinity for an infeasible target. -/
def number (S : Finset α) (A : ι → Set α) : ℝ≥0∞ := by
  classical
  exact if ∃ w, Covers S A w then ENNReal.ofReal (value S A) else ⊤

theorem number_ne_top_iff (S : Finset α) (A : ι → Set α) :
    number S A ≠ ⊤ ↔ ∃ w, Covers S A w := by
  classical
  simp only [number]
  split_ifs <;> simp_all

theorem number_toReal {S : Finset α} {A : ι → Set α}
    (h : ∃ w, Covers S A w) : (number S A).toReal = value S A := by
  classical
  rw [number, ite_eq_left h, ENNReal.toReal_ofReal (value_nonneg h)]

end
end LeanMachine.FractionalCover

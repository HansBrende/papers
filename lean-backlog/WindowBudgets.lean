import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Quantitative invoices for the native window extraction

The finite counts below are supplied by the geometric modules, not assumed
as replacements for their conclusions. We retain the reviewed proof's slack.
-/
namespace LeanBacklog.WindowBudgets

theorem physical_window_budget {d b N T : ℕ} {C : ℝ}
    (hd : 4 ≤ d) (hb : 1 ≤ b) (hC : 1 ≤ C)
    (hT : (T : ℝ) ≤ C * ((d * d * b : ℕ) + 1))
    (hN : N * (d * b) ≤ T + d * b) :
    16 * (N * (d * b) : ℝ) ≤ 21 * C * (d * d * b : ℕ) := by
  have hL : 16 ≤ d * d * b := by
    have hdd : 16 ≤ d * d := Nat.mul_le_mul hd hd
    have hb' : d * d ≤ d * d * b := by nlinarith
    omega
  have hh : 4 * (d * b) ≤ d * d * b := by
    have := Nat.mul_le_mul_right (d * b) hd
    simpa [Nat.mul_assoc] using this
  have hL' : (16 : ℝ) ≤ (d * d * b : ℕ) := by exact_mod_cast hL
  have hh' : (4 : ℝ) * (d * b : ℕ) ≤ (d * d * b : ℕ) := by exact_mod_cast hh
  have hN' : (N * (d * b) : ℝ) ≤ (T : ℝ) + (d * b : ℕ) := by exact_mod_cast hN
  have hC0 : 0 ≤ C := by linarith
  have hscale₁ := mul_le_mul_of_nonneg_left hL' hC0
  have hscale₂ := mul_le_mul_of_nonneg_left hh' hC0
  have hh0 : (0 : ℝ) ≤ (d * b : ℕ) := Nat.cast_nonneg _
  have hscale₃ := mul_le_mul_of_nonneg_right hC hh0
  nlinarith

/-- Exact cut invoice after combining the bad-window and guard counts. -/
theorem guarded_cut_budget {k β d b N T cuts : ℕ} {C ε : ℝ}
    (hd : 4 ≤ d) (hb : 1 ≤ b) (hC : 1 ≤ C) (hε : 0 < ε)
    (hT : (T : ℝ) ≤ C * ((d * d * b : ℕ) + 1))
    (hN : N * (d * b) ≤ T + d * b)
    (hcount : (⌈4 * (k : ℝ) * (k + 1) * β * C / ε⌉₊ + 1) * cuts ≤
      3 * k * (k + 1) * (N * (d * b))) :
    (β * cuts : ℝ) ≤ (63 / 64 : ℝ) * ε * (d * d * b : ℕ) := by
  let M : ℕ := ⌈4 * (k : ℝ) * (k + 1) * β * C / ε⌉₊
  have hcountNat : (M + 1) * cuts ≤ 3 * k * (k + 1) * (N * (d * b)) := hcount
  have hcount' : ((M : ℝ) + 1) * cuts ≤
      3 * k * (k + 1) * (N * (d * b) : ℝ) := by exact_mod_cast hcountNat
  have hM : 4 * (k : ℝ) * (k + 1) * β * C ≤ ε * M := by
    have hc : 4 * (k : ℝ) * (k + 1) * β * C / ε ≤ M := Nat.le_ceil _
    exact ((div_le_iff₀ hε).mp hc).trans_eq (mul_comm _ _)
  by_cases hk : k = 0
  · have hc : cuts = 0 := by simpa [hk] using hcount
    subst cuts
    simp only [Nat.cast_zero, mul_zero]
    positivity
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hkprod : 0 < (k : ℝ) * (k + 1) := by positivity
  have hc0 : (0 : ℝ) ≤ cuts := Nat.cast_nonneg _
  have hprod := mul_le_mul_of_nonneg_right hM hc0
  have hupper := mul_le_mul_of_nonneg_left hcount' hε.le
  have hinvoice : 4 * C * β * cuts ≤ 3 * ε * (N * (d * b) : ℝ) := by
    apply (mul_le_mul_iff_left₀ hkprod).mp
    nlinarith
  have hphys := physical_window_budget hd hb hC hT hN
  have hphys' := mul_le_mul_of_nonneg_left hphys hε.le
  have hCpos : 0 < C := by linarith
  apply (mul_le_mul_iff_left₀ hCpos).mp
  nlinarith

/-- The exceptional-row invoice retains its independent slack. -/
theorem exceptional_row_budget {d b N T exceptions : ℕ} {C ε : ℝ}
    (hd : 4 ≤ d) (hb : 1 ≤ b) (hC : 1 ≤ C) (hε : 0 < ε)
    (hT : (T : ℝ) ≤ C * ((d * d * b : ℕ) + 1))
    (hN : N * (d * b) ≤ T + d * b)
    (hcount : ⌈2 * C / ε⌉₊ * exceptions ≤ N) :
    (exceptions : ℝ) ≤ (21 / 32 : ℝ) * ε * d := by
  let M : ℕ := ⌈2 * C / ε⌉₊
  have hM : 2 * C ≤ ε * M := by
    have hc : 2 * C / ε ≤ M := Nat.le_ceil _
    exact ((div_le_iff₀ hε).mp hc).trans_eq (mul_comm _ _)
  have hcount' : (M : ℝ) * exceptions ≤ N := by exact_mod_cast hcount
  have he0 : (0 : ℝ) ≤ exceptions := Nat.cast_nonneg _
  have hprod := mul_le_mul_of_nonneg_right hM he0
  have hupper := mul_le_mul_of_nonneg_left hcount' hε.le
  have hstep : 2 * C * exceptions ≤ ε * N := by nlinarith
  have hwidth : (0 : ℝ) < (d * b : ℕ) := by positivity
  have hstep' := mul_le_mul_of_nonneg_right hstep hwidth.le
  have hphys := physical_window_budget hd hb hC hT hN
  have hphys' := mul_le_mul_of_nonneg_left hphys hε.le
  have hCpos : 0 < C := by linarith
  apply (mul_le_mul_iff_left₀ (mul_pos hCpos hwidth)).mp
  push_cast at hstep' hphys' ⊢
  nlinarith

#print axioms physical_window_budget
#print axioms guarded_cut_budget
#print axioms exceptional_row_budget

end LeanBacklog.WindowBudgets

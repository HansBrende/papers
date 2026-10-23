import BitWord.CompilerCoverage

namespace BitWord.Compiler
open Geometry
open scoped BigOperators
open Classical

/-- A single scale is selected after summing the dirt of every path. -/
theorem exists_common_scale {P K L m : ℕ} (paths : Fin K → Path P)
    (hlen : ∀ j, (paths j).length ≤ L) (B : Fin m → ℕ) (hm : 0 < m)
    (hsep : ∀ i j, i < j → volume (B i) ≤ B j) :
    ∃ i : Fin m, m * (∑ j, (dirty (B i) (paths j)).card) ≤ K * L * P := by
  let f := fun i : Fin m => ∑ j, (dirty (B i) (paths j)).card
  have ht : (∑ i, f i) ≤ K * L * P := by
    rw [show (∑ i, f i) = ∑ j : Fin K, ∑ i : Fin m, (dirty (B i) (paths j)).card from Finset.sum_comm]
    calc
      _ ≤ ∑ j : Fin K, (paths j).length * P :=
        Finset.sum_le_sum (fun j _ => total_dirty_volume_le (paths j) B hsep)
      _ ≤ ∑ _j : Fin K, L * P := Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_right P (hlen j))
      _ = _ := by simp; ring
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ f
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  refine ⟨i, ?_⟩
  have ha : m * f i ≤ ∑ j, f j := by
    calc
      _ = ∑ _j : Fin m, f i := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j hj => hmin j hj)
  exact ha.trans ht

noncomputable def covered {P K : ℕ} (paths : Fin K → Path P) (target : ℕ → ℕ) : Finset ℕ :=
  Finset.univ.biUnion (fun j => agreement (paths j) target)

/-- The quantitative heterogeneous-stage coverage bound. All finite-scale
geometry and every intermediate bad occurrence have already been discharged
from the actual operation grammar. -/
theorem coverage_bound {P K L m B₀ : ℕ} (paths : Fin K → Path P)
    (hlen : ∀ j, (paths j).length ≤ L) (B : Fin m → ℕ)
    (hm : 0 < m) (hB₀ : 0 < B₀) (hlower : ∀ i, B₀ ≤ B i)
    (hdiv : ∀ i, B i ∣ P)
    (hsep : ∀ i j, i < j → volume (B i) ≤ B j)
    (target : ℕ → ℕ) (hd : ∀ i, Disperses P (B i) target) :
    ((covered paths target).card : ℝ) ≤
      (K : ℝ) * L * P / m + K * (11 : ℝ)^L * P / B₀ := by
  obtain ⟨i, hi⟩ := exists_common_scale paths hlen B hm hsep
  have hBi : 0 < B i := lt_of_lt_of_le hB₀ (hlower i)
  have hc : (covered paths target).card ≤
      (∑ j, (dirty (B i) (paths j)).card) + K * (P / B i) * 11^L := by
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ j : Fin K, ((dirty (B i) (paths j)).card + (P / B i) * 11 ^ (paths j).length) :=
        Finset.sum_le_sum (fun j _ => agreement_card_le (paths j) hBi (hdiv i) target (hd i))
      _ ≤ ∑ j : Fin K, ((dirty (B i) (paths j)).card + (P / B i) * 11 ^ L) := by
        apply Finset.sum_le_sum
        intro j hj
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (hlen j))) _
      _ = _ := by rw [Finset.sum_add_distrib]; simp; ring
  have hid : ((∑ j, (dirty (B i) (paths j)).card : ℕ) : ℝ) ≤ (K : ℝ)*L*P/m := by
    apply (le_div_iff₀ (by exact_mod_cast hm : (0:ℝ)<m)).2
    have hi' : (m:ℝ) * (∑ j, ((dirty (B i) (paths j)).card : ℝ)) ≤ (K:ℝ)*L*P := by exact_mod_cast hi
    simpa [Nat.cast_sum, mul_comm] using hi'
  have hquot : ((P / B i : ℕ) : ℝ) ≤ (P : ℝ)/B₀ := by
    apply (le_div_iff₀ (by exact_mod_cast hB₀ : (0:ℝ)<B₀)).2
    have hn : (P / B i) * B₀ ≤ P := by
      calc
        _ ≤ (P / B i) * B i := Nat.mul_le_mul_left _ (hlower i)
        _ = P := Nat.div_mul_cancel (hdiv i)
    exact_mod_cast hn
  have hc' : ((covered paths target).card : ℝ) ≤
      (∑ j, ((dirty (B i) (paths j)).card : ℝ)) + (K:ℝ)*(P/B i : ℕ)*(11:ℝ)^L := by exact_mod_cast hc
  have hmul := mul_le_mul_of_nonneg_left hquot (show (0:ℝ) ≤ K * (11:ℝ)^L by positivity)
  push_cast at hid
  calc
    _ ≤ (∑ j, ((dirty (B i) (paths j)).card : ℝ)) + (K:ℝ)*(P/B i : ℕ)*(11:ℝ)^L := hc'
    _ ≤ (K:ℝ)*L*P/m + K*(11:ℝ)^L*((P:ℝ)/B₀) :=
      add_le_add hid (by simpa [mul_assoc, mul_comm, mul_left_comm] using hmul)
    _ = _ := by ring

end BitWord.Compiler

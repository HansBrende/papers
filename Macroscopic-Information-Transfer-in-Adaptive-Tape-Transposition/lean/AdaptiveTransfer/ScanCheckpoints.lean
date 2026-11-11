import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Exact locality and support accounting for position-dependent finite scans.
No invertibility, source independence, or native time bound is assumed. -/

namespace AdaptiveTransfer

open Finset Classical
open scoped BigOperators

/-- The state type itself may depend on the position. -/
def scanState {S : ℕ → Type*} (step : (i : ℕ) → S i → Bool → S (i + 1))
    (initial : S 0) (X : ℕ → Bool) : (i : ℕ) → S i
  | 0 => initial
  | i + 1 => step i (scanState step initial X i) (X i)

/-- Equal anchor states and the intervening raw bits determine the same state. -/
theorem scanState_locality {S : ℕ → Type*}
    (step : (i : ℕ) → S i → Bool → S (i + 1)) (initial : S 0)
    (X Y : ℕ → Bool) {a b : ℕ} (hab : a ≤ b)
    (ha : scanState step initial X a = scanState step initial Y a)
    (hbits : ∀ i, a ≤ i → i < b → X i = Y i) :
    scanState step initial X b = scanState step initial Y b := by
  induction b, hab using Nat.le_induction with
  | base => exact ha
  | succ b hab ih =>
    have hb := hbits b hab (by omega)
    have hprev := ih (fun i hai hib => hbits i hai (by omega))
    simp only [scanState, hprev, hb]

/-- A preceding checkpoint at distance at most R uses only the radius-R
window at the queried coordinate. Including its center also gives the next state. -/
theorem scanState_window {S : ℕ → Type*}
    (step : (i : ℕ) → S i → Bool → S (i + 1)) (initial : S 0)
    (X Y : ℕ → Bool) {a i R : ℕ} (hai : a ≤ i) (hgap : i - a ≤ R)
    (ha : scanState step initial X a = scanState step initial Y a)
    (hwindow : ∀ j, i - R ≤ j → j ≤ i → X j = Y j) :
    scanState step initial X i = scanState step initial Y i ∧
    scanState step initial X (i + 1) = scanState step initial Y (i + 1) := by
  have hs := scanState_locality step initial X Y hai ha (fun j haj hji =>
    hwindow j (by omega) (by omega))
  refine ⟨hs, ?_⟩
  simp only [scanState, hs, hwindow i (Nat.sub_le _ _) le_rfl]

/-- Every residue grid, completed by zero, has a preceding anchor with gap < B. -/
theorem preceding_residue_anchor {B r : ℕ} (hB : 0 < B) (hr : r < B) (i : ℕ) :
    ∃ a, a ≤ i ∧ i - a < B ∧ (a = 0 ∨ a % B = r) := by
  by_cases hir : i < r
  · exact ⟨0, Nat.zero_le _, by omega, Or.inl rfl⟩
  · let a := r + B * ((i - r) / B)
    have hd := Nat.mod_add_div (i - r) B
    have hm := Nat.mod_lt (i - r) hB
    refine ⟨a, ?_, ?_, Or.inr ?_⟩
    · dsimp [a]; omega
    · dsimp [a]; omega
    · simp [a, Nat.add_mod, Nat.mod_eq_of_lt hr]

/-- One public residue pays at most the average total profile weight. The
weights need not be independent, and may be arbitrary real numbers. -/
theorem checkpoint_residue_average (positions : Finset ℕ) (weight : ℕ → ℝ)
    {B : ℕ} (hB : 0 < B) :
    ∃ r : Fin B, (B : ℝ) *
      (∑ i ∈ positions, if i % B = r.val then weight i else 0) ≤
        ∑ i ∈ positions, weight i := by
  classical
  let : NeZero B := ⟨by omega⟩
  let cost (r : Fin B) := ∑ i ∈ positions,
    if (⟨i % B, Nat.mod_lt i hB⟩ : Fin B) = r then weight i else 0
  have hsum : ∑ r : Fin B, cost r = ∑ i ∈ positions, weight i := by
    dsimp [cost]
    rw [Finset.sum_comm]
    simp
  have hex : ∃ r : Fin B, (B : ℝ) * cost r ≤ ∑ i ∈ positions, weight i := by
    by_contra hn
    push Not at hn
    have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := Fin B))
      (fun r _ => hn r)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, hsum] at hlt
    exact (lt_irrefl _ hlt)
  obtain ⟨r, hr⟩ := hex
  refine ⟨r, ?_⟩
  simpa only [cost, Fin.ext_iff] using hr

abbrev CheckpointLabel {ι : Type*} (S : ι → ℕ → Type*) (anchors : Finset ℕ) :=
  (ν : ι) → (i : anchors) → S ν i.val

/-- This is a joint product alphabet, not an independence assertion. -/
theorem checkpointLabel_card {ι : Type*} [Fintype ι]
    (S : ι → ℕ → Type*) [∀ ν i, Fintype (S ν i)] (anchors : Finset ℕ) :
    Fintype.card (CheckpointLabel S anchors) =
      ∏ ν : ι, ∏ i : anchors, Fintype.card (S ν i.val) := by
  simp [CheckpointLabel, Fintype.card_pi]

theorem checkpoint_image_card_le {ι X : Type*} [Fintype ι]
    (S : ι → ℕ → Type*) [∀ ν i, Fintype (S ν i)] (anchors : Finset ℕ)
    (inputs : Finset X) (label : X → CheckpointLabel S anchors) :
    (inputs.image label).card ≤ ∏ ν : ι, ∏ i : anchors, Fintype.card (S ν i.val) := by
  classical
  rw [← checkpointLabel_card S anchors]
  exact Finset.card_le_univ _

end AdaptiveTransfer

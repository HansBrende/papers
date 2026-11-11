import Mathlib

/-! # Actual top sets and finite atom envelopes

The selected set consists of the largest positive weights. Its construction
and the atom/support bounds do not assume a supplied top-set certificate.
-/

namespace LeanMachine.FiniteTopSets

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- Select exactly the available number of largest entries of a finite list
of weights, retaining every tie choice permitted by this specification. -/
theorem exists_largest (s : Finset V) (w : V → ℝ) (K : ℕ) :
    ∃ T ⊆ s, T.card = min K s.card ∧
      ∀ x ∈ s, x ∉ T → ∀ y ∈ T, w x ≤ w y := by
  induction K generalizing s with
  | zero => exact ⟨∅, empty_subset _, by simp, by simp⟩
  | succ K ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨z, hz, hmax⟩ := s.exists_max_image w hs
      obtain ⟨T, hT, hcard, horder⟩ := ih (s.erase z)
      have hzT : z ∉ T := fun h => (mem_erase.mp (hT h)).1 rfl
      refine ⟨insert z T, insert_subset hz (hT.trans (erase_subset _ _)), ?_, ?_⟩
      · rw [card_insert_of_notMem hzT, hcard, card_erase_of_mem hz]
        have hp := hs.card_pos
        omega
      · intro x hx hxT y hy
        have hxz : x ≠ z := fun he => hxT (mem_insert.mpr (Or.inl he))
        rcases mem_insert.mp hy with rfl | hy
        · exact hmax x hx
        · exact horder x (mem_erase.mpr ⟨hxz, hx⟩)
            (fun h => hxT (mem_insert_of_mem h)) y hy
    · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hs
      simp [he]

variable [Fintype V]

noncomputable def positiveSupport (w : V → ℝ) : Finset V :=
  univ.filter fun x => 0 < w x

noncomputable def top (w : V → ℝ) (K : ℕ) : Finset V :=
  Classical.choose (exists_largest (positiveSupport w) w K)

theorem top_spec (w : V → ℝ) (K : ℕ) :
    top w K ⊆ positiveSupport w ∧
      (top w K).card = min K (positiveSupport w).card ∧
      ∀ x ∈ positiveSupport w, x ∉ top w K → ∀ y ∈ top w K, w x ≤ w y :=
  Classical.choose_spec (exists_largest (positiveSupport w) w K)

theorem card_top_le (w : V → ℝ) (K : ℕ) : (top w K).card ≤ K := by
  rw [(top_spec w K).2.1]
  exact min_le_left _ _

theorem top_positive (w : V → ℝ) (K : ℕ) {x : V} (hx : x ∈ top w K) :
    0 < w x := (mem_filter.mp ((top_spec w K).1 hx)).2

theorem top_eq_support (w : V → ℝ) (K : ℕ)
    (hcard : (positiveSupport w).card ≤ K) : top w K = positiveSupport w := by
  apply eq_of_subset_of_card_le (top_spec w K).1
  rw [(top_spec w K).2.1, min_eq_right hcard]

theorem top_contains_constant (v : V) (mass : ℝ) (hmass : 0 < mass)
    {K : ℕ} (hK : 1 ≤ K) : v ∈ top (fun x => if x = v then mass else 0) K := by
  have hs : positiveSupport (fun x => if x = v then mass else 0) = {v} := by
    ext x
    by_cases hx : x = v <;> simp [positiveSupport, hx, hmass]
  rw [top_eq_support _ K (by simpa only [hs, card_singleton] using hK), hs]
  exact mem_singleton_self _

/-- An attained positive atom outside the actual top set forces at least
K+1 distinct positive atoms, even when the total weight is not one. -/
theorem support_large_of_outside (w : V → ℝ) (K : ℕ) {x : V}
    (hx : x ∉ top w K) (hpos : 0 < w x) :
    K + 1 ≤ (positiveSupport w).card := by
  have hmem : x ∈ positiveSupport w := mem_filter.mpr ⟨mem_univ _, hpos⟩
  have hstrict : (top w K).card < (positiveSupport w).card :=
    card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨(top_spec w K).1, by
      intro he
      exact hx (he ▸ hmem)⟩)
  rw [(top_spec w K).2.1] at hstrict
  omega

/-- The exact outside-atom bound, multiplied to avoid any zero-total or
zero-denominator side condition. -/
theorem outside_mul_le_total (w : V → ℝ) (hw : ∀ x, 0 ≤ w x) (K : ℕ)
    {x : V} (hx : x ∉ top w K) :
    (K + 1 : ℝ) * w x ≤ ∑ y, w y := by
  by_cases hp : 0 < w x
  · have hsupport := support_large_of_outside w K hx hp
    have hcard : (top w K).card = K := by
      rw [(top_spec w K).2.1, min_eq_left (by omega)]
    calc
      (K + 1 : ℝ) * w x = ∑ _y ∈ insert x (top w K), w x := by
        simp [hx, hcard]
      _ ≤ ∑ y ∈ insert x (top w K), w y := by
        apply sum_le_sum
        intro y hy
        rcases mem_insert.mp hy with rfl | hy
        · rfl
        · exact (top_spec w K).2.2 x (mem_filter.mpr ⟨mem_univ _, hp⟩) hx y hy
      _ ≤ ∑ y, w y := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun y _ _ => hw y)
  · have hz : w x = 0 := le_antisymm (le_of_not_gt hp) (hw x)
    simp only [hz, mul_zero]
    exact sum_nonneg (fun y _ => hw y)

theorem outside_le_total_div (w : V → ℝ) (hw : ∀ x, 0 ≤ w x) (K : ℕ)
    {x : V} (hx : x ∉ top w K) :
    w x ≤ (∑ y, w y) / (K + 1) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < K + 1)).mpr
  simpa only [mul_comm] using outside_mul_le_total w hw K hx

end LeanMachine.FiniteTopSets

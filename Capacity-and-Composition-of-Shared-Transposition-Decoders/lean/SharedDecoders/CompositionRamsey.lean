import Mathlib.Combinatorics.HalesJewett
import Mathlib.Tactic

/-!
# A finite interval form of van der Waerden's theorem

The proof uses Mathlib's finite Hales--Jewett theorem.  Summing the symbols of
a combinatorial line produces an ordinary arithmetic progression inside one
fixed finite interval.  No quantitative estimate for the interval is asserted.
-/

namespace SharedDecoders

open scoped BigOperators

/-- Every finite coloring has a monochromatic progression of the prescribed
positive length in a single interval fixed before the coloring is chosen. -/
theorem exists_progression_bound (κ : Type*) [Finite κ] (ell : ℕ) (hell : 0 < ell) :
    ∃ N : ℕ, ell ≤ N ∧ ∀ C : ℕ → κ,
      ∃ a s : ℕ, 0 < s ∧ ∀ j < ell,
        a + s * j < N ∧ C (a + s * j) = C a := by
  classical
  obtain ⟨ι, instι, hι⟩ :=
    Combinatorics.Line.exists_mono_in_high_dimension (Fin ell) κ
  let := instι
  refine ⟨Fintype.card ι * (ell - 1) + ell, by omega, ?_⟩
  intro C
  obtain ⟨l, c, hc⟩ := hι (fun v => C (∑ i, (v i).val))
  let s : Finset ι := Finset.univ.filter (fun i => l.idxFun i = none)
  let a : ℕ := ∑ i ∈ sᶜ, ((l.idxFun i).map Fin.val).getD 0
  have hs : 0 < s.card := by
    obtain ⟨i, hi⟩ := l.proper
    exact Finset.card_pos.mpr ⟨i, by simp [s, hi]⟩
  have hsum (j : Fin ell) : (∑ i, (l j i).val) = a + s.card * j.val := by
    rw [← Finset.sum_add_sum_compl s]
    have hvar : (∑ i ∈ s, (l j i).val) = s.card * j.val := by
      calc
        (∑ i ∈ s, (l j i).val) = ∑ _i ∈ s, j.val := by
          apply Finset.sum_congr rfl
          intro i hi
          have hnone : l.idxFun i = none := (Finset.mem_filter.mp hi).2
          rw [l.apply_none _ _ hnone]
        _ = s.card * j.val := by simp
    have hfixed : (∑ i ∈ sᶜ, (l j i).val) = a := by
      apply Finset.sum_congr rfl
      intro i hi
      have hnone : l.idxFun i ≠ none := by
        simpa [s] using hi
      obtain ⟨z, hz⟩ := Option.ne_none_iff_exists.mp hnone
      simp [← hz]
    rw [hvar, hfixed, Nat.add_comm]
  have hbound (j : Fin ell) : a + s.card * j.val < Fintype.card ι * (ell - 1) + ell := by
    rw [← hsum]
    have hle : (∑ i, (l j i).val) ≤ Fintype.card ι * (ell - 1) := by
      calc
        (∑ i, (l j i).val) ≤ ∑ _i : ι, (ell - 1) := by
          exact Finset.sum_le_sum (fun i _ => Nat.le_sub_one_of_lt (l j i).isLt)
        _ = Fintype.card ι * (ell - 1) := by simp
    omega
  refine ⟨a, s.card, hs, ?_⟩
  intro j hj
  refine ⟨hbound ⟨j, hj⟩, ?_⟩
  have h0 := hc (⟨0, hell⟩ : Fin ell)
  have hj' := hc (⟨j, hj⟩ : Fin ell)
  change C (∑ i, (l (⟨0, hell⟩ : Fin ell) i).val) = c at h0
  change C (∑ i, (l (⟨j, hj⟩ : Fin ell) i).val) = c at hj'
  rw [hsum] at h0 hj'
  simpa using hj'.trans h0.symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- A kernel-evaluated finite certificate for the upper bound `W(2,3) ≤ 9`.
No minimality claim is needed or made. -/
theorem binary_progression_nine_finite :
    ∀ C : Fin 9 → Fin 2, ∃ a : Fin 9, ∃ s : Fin 5,
      0 < s.val ∧ a.val + 2 * s.val < 9 ∧
      ∀ j : Fin 3, C (Fin.ofNat 9 (a.val + s.val * j.val)) = C a := by
  decide

theorem binary_progression_nine (C : ℕ → Fin 2) :
    ∃ a s : ℕ, 0 < s ∧ ∀ j < 3,
      a + s * j < 9 ∧ C (a + s * j) = C a := by
  obtain ⟨a, s, hs, hlast, hmono⟩ :=
    binary_progression_nine_finite (fun i => C i.val)
  refine ⟨a.val, s.val, hs, ?_⟩
  intro j hj
  have hlt : a.val + s.val * j < 9 := by nlinarith
  refine ⟨hlt, ?_⟩
  have h := hmono (⟨j, hj⟩ : Fin 3)
  simpa [Fin.ofNat, Nat.mod_eq_of_lt hlt] using h

end SharedDecoders

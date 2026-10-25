import MotionDepthCodes.Polymatroid

/-!
# Three-part conditional elimination

Reuse the fourth paper's polymatroid and recovery definitions. The source
condition is stated as an entropy dependence, so this lemma also applies
without a graph. No disjointness is needed for the tuple inequality.
-/

namespace CircularMemo

open Finset MotionDepthCodes

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Adding one coordinate increases a tuple's entropy by at most its
conditional entropy given the already revealed coordinates. -/
theorem tuple_increment {h : Finset V → ℝ} (hh : IsPolymatroid h)
    (S P : Finset V) (v : V) :
    h (insert v S ∪ P) + h S ≤ h (S ∪ P) + h (insert v S) := by
  apply hh.elemental (A := S ∪ P) (B := insert v S)
  · ext x; simp only [mem_union, mem_insert]; tauto
  · exact subset_inter subset_union_left (subset_insert v S)

/-- At every proper revealed set there is a coordinate belonging to one
part and determined by the revealed set together with the next part. Then
the three complete part records pay for the joint entropy twice. -/
theorem three_part_elimination {h : Finset V → ℝ} (hh : IsPolymatroid h)
    (A B C : Finset V)
    (helim : ∀ S : Finset V, S ≠ univ → ∃ v, v ∉ S ∧
      ((v ∈ A ∧ h (insert v (S ∪ B)) = h (S ∪ B)) ∨
       (v ∈ B ∧ h (insert v (S ∪ C)) = h (S ∪ C)) ∨
       (v ∈ C ∧ h (insert v (S ∪ A)) = h (S ∪ A)))) :
    2 * h univ ≤ h A + h B + h C := by
  have aux : ∀ n : ℕ, ∀ S : Finset V, (univ \ S).card = n →
      2 * h univ + h S ≤ h (S ∪ A) + h (S ∪ B) + h (S ∪ C) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hn
      by_cases hS : S = univ
      · rw [hS]
        have hu (P : Finset V) : univ ∪ P = (univ : Finset V) :=
          union_eq_left.mpr (subset_univ P)
        rw [hu A, hu B, hu C]
        linarith
      obtain ⟨v, hv, he⟩ := helim S hS
      have hlt : (univ \ insert v S).card < n := by
        rw [← hn]
        apply card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        constructor
        · intro x hx; simp only [mem_sdiff, mem_univ, true_and, mem_insert] at hx ⊢
          exact fun hxS => hx (Or.inr hxS)
        · intro heq
          have : v ∈ univ \ S := by simp [hv]
          rw [← heq] at this
          simp at this
      have hi := ih _ hlt (insert v S) rfl
      have own (P : Finset V) (hp : v ∈ P) : insert v S ∪ P = S ∪ P := by
        rw [insert_union, insert_eq_of_mem (mem_union_right S hp)]
      rcases he with ⟨ha, hb⟩ | ⟨hb, hc⟩ | ⟨hc, ha⟩
      · rw [own A ha] at hi
        simp only [insert_union] at hi
        rw [hb] at hi
        have ht := tuple_increment hh S C v
        rw [insert_union] at ht
        linarith
      · rw [own B hb] at hi
        simp only [insert_union] at hi
        rw [hc] at hi
        have ht := tuple_increment hh S A v
        rw [insert_union] at ht
        linarith
      · rw [own C hc] at hi
        simp only [insert_union] at hi
        rw [ha] at hi
        have ht := tuple_increment hh S B v
        rw [insert_union] at ht
        linarith
  simpa [hh.empty] using aux ((univ : Finset V).card) ∅ (by simp)

end CircularMemo

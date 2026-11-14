import LeanMachine.ClosedCutRank
import LeanMachine.OrderedRowRank
import LeanMachine.SupportTraversal

/-!
# Rank from outgoing width and a forbidden four-arc pattern

These bounds concern the actual scalar support of a matrix. The number of
helper rows in a whole-row code is not an outgoing scalar support bound.
-/

namespace LeanMachine.SparseRankBounds

open Finset

set_option autoImplicit false

universe u v
variable {F : Type v} [Field F] {V : Type u} [Fintype V] [DecidableEq V]

/-- Off-diagonal nonzero entries in a row. -/
noncomputable def outgoing (B : Matrix V V F) (i : V) : Finset V := by
  classical
  exact univ.filter fun j => j ≠ i ∧ B i j ≠ 0

@[simp] theorem mem_outgoing (B : Matrix V V F) (i j : V) :
    j ∈ outgoing B i ↔ j ≠ i ∧ B i j ≠ 0 := by
  classical
  simp [outgoing]

theorem outgoing_submatrix_card_le {U : Type*} [Fintype U] [DecidableEq U]
    (B : Matrix V V F) (f : U → V) (hf : Function.Injective f) (i : U) :
    (outgoing (B.submatrix f f) i).card ≤ (outgoing B (f i)).card := by
  apply Finset.card_le_card_of_injOn f
  · intro j hj
    obtain ⟨hji, hij⟩ := (mem_outgoing _ _ _).mp hj
    exact (mem_outgoing _ _ _).mpr ⟨fun heq => hji (hf heq), hij⟩
  · intro j _ k _ hjk
    exact hf hjk

omit [Fintype V] [DecidableEq V] in
theorem noFourArcPattern_submatrix {U : Type*}
    (B : Matrix V V F) (f : U → V) (hf : Function.Injective f)
    (hB : LastRowSupport.NoFourArcPattern B) :
    LastRowSupport.NoFourArcPattern (B.submatrix f f) := by
  intro a j k haj hak hjk hbad
  exact hB (fun h => haj (hf h)) (fun h => hak (hf h))
    (fun h => hjk (hf h)) hbad

/-- An earlier nonzero in a row's own column leaves all newly introduced
columns among its off-diagonal entries. -/
theorem newColumns_le_outgoing {n : ℕ}
    (B : Matrix (Fin n) (Fin n) F) (i : Fin n)
    (hown : ∃ p, p.val < i.val ∧ B p i ≠ 0) :
    (OrderedRowRank.newColumns B i).card ≤ (outgoing B i).card := by
  apply Finset.card_le_card
  intro j hj
  obtain ⟨hij, hzero⟩ := (OrderedRowRank.mem_newColumns B i j).mp hj
  refine (mem_outgoing B i j).mpr ⟨?_, hij⟩
  rintro rfl
  obtain ⟨p, hp, hpi⟩ := hown
  exact hpi (hzero p hp)

/-- Without a predecessor, charge at most one diagonal entry in addition
to the outgoing support. -/
theorem newColumns_le_outgoing_add_one {n : ℕ}
    (B : Matrix (Fin n) (Fin n) F) (i : Fin n) :
    (OrderedRowRank.newColumns B i).card ≤ (outgoing B i).card + 1 := by
  classical
  have hsub : OrderedRowRank.newColumns B i ⊆ insert i (outgoing B i) := by
    intro j hj
    by_cases hji : j = i
    · exact Finset.mem_insert.mpr (Or.inl hji)
    · exact Finset.mem_insert.mpr (Or.inr ((mem_outgoing B i j).mpr
        ⟨hji, ((OrderedRowRank.mem_newColumns B i j).mp hj).1⟩))
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- The ordered count applied to a relation reachable from a chosen root.
It saves `k - 2` columns beyond the general bound when `k ≥ 2`. This sharper
inequality itself does not require a lower bound on `k`. -/
theorem card_add_width_le_mul_rank_add_two_of_cut (B : Matrix V V F) (k : ℕ)
    (hdiag : ∀ i, B i i ≠ 0) (hpattern : LastRowSupport.NoFourArcPattern B)
    (hdegree : ∀ i, (outgoing B i).card ≤ k) (hrank : 2 ≤ B.rank)
    (s : V) (hcut : ∀ P : Finset V, s ∈ P → P ≠ univ →
      ∃ u ∈ P, ∃ v ∉ P, B u v ≠ 0) :
    Fintype.card V + k ≤ k * B.rank + 2 := by
  classical
  obtain ⟨e, _, he⟩ := SupportTraversal.exists_equiv (fun u v => B u v ≠ 0) s hcut
  let Q := B.submatrix e e
  have hQr : Q.rank = B.rank := Matrix.rank_submatrix B e e
  have hQd : ∀ i, (outgoing Q i).card ≤ k := fun i =>
    (outgoing_submatrix_card_le B e e.injective i).trans (hdegree (e i))
  have hown : ∀ i : Fin (Fintype.card V), 0 < i.val →
      ∃ p, p.val < i.val ∧ Q p i ≠ 0 := by
    intro i hi
    obtain ⟨p, hp, hpi⟩ := he i hi
    exact ⟨p, hp, hpi⟩
  have hcount := OrderedRowRank.rank_count_of_order Q (k + 1) k
    (fun i => hdiag (e i)) (noFourArcPattern_submatrix B e e.injective hpattern)
    (hQr.symm ▸ hrank)
    (fun i _ => (newColumns_le_outgoing_add_one Q i).trans
      (Nat.add_le_add_right (hQd i) 1))
    (fun i hi => (newColumns_le_outgoing Q i (hown i hi)).trans (hQd i)) hown
  rw [hQr] at hcount
  have hr := Nat.sub_add_cancel hrank
  nlinarith

/-- The root-reachable case of the general outgoing-width bound. -/
theorem card_le_mul_rank_of_cut (B : Matrix V V F) (k : ℕ) (hk : 2 ≤ k)
    (hdiag : ∀ i, B i i ≠ 0) (hpattern : LastRowSupport.NoFourArcPattern B)
    (hdegree : ∀ i, (outgoing B i).card ≤ k) (hrank : 2 ≤ B.rank)
    (s : V) (hcut : ∀ P : Finset V, s ∈ P → P ≠ univ →
      ∃ u ∈ P, ∃ v ∉ P, B u v ≠ 0) :
    Fintype.card V ≤ k * B.rank := by
  have h := card_add_width_le_mul_rank_add_two_of_cut B k
    hdiag hpattern hdegree hrank s hcut
  omega

/-- A nonzero diagonal, outgoing width at most `k ≥ 2`, and absence of
`v → j`, `v → k`, `j → k`, `k → j` on three distinct indices force
`|V| ≤ k * rank B`. Incoming degrees are unrestricted. -/
theorem card_le_mul_rank (B : Matrix V V F) (k : ℕ) (hk : 2 ≤ k)
    (hdiag : ∀ i, B i i ≠ 0) (hpattern : LastRowSupport.NoFourArcPattern B)
    (hdegree : ∀ i, (outgoing B i).card ≤ k) :
    Fintype.card V ≤ k * B.rank := by
  classical
  let Q : ∀ (W : Type u) [Fintype W] [DecidableEq W], Matrix W W F → Prop :=
    fun W _ _ A => (∀ i, A i i ≠ 0) ∧ LastRowSupport.NoFourArcPattern A ∧
      (∀ i, (outgoing A i).card ≤ k)
  refine ClosedCutRank.card_le_mul_rank_of_closed_cuts Q k ?_ ?_ B
    ⟨hdiag, hpattern, hdegree⟩
  · intro W U _ _ _ _ A f hf hA
    exact ⟨fun i => hA.1 (f i), noFourArcPattern_submatrix A f hf hA.2.1,
      fun i => (outgoing_submatrix_card_le A f hf i).trans (hA.2.2 (f i))⟩
  · intro W _ _ A hA hcut
    obtain ⟨hdiagA, hpatternA, hdegreeA⟩ := hA
    cases isEmpty_or_nonempty W with
    | inl h => simp
    | inr h =>
      let s : W := Classical.choice h
      by_cases hrank : 2 ≤ A.rank
      · exact card_le_mul_rank_of_cut A k hk hdiagA hpatternA hdegreeA hrank s
          (fun P hs hproper => hcut P ⟨s, hs⟩ hproper)
      · have hr1 : A.rank ≤ 1 := by omega
        have hcard := ClosedCutRank.card_le_two_of_rank_le_one A hdiagA hpatternA hr1
        have hpos := ClosedCutRank.one_le_rank_of_entry_ne_zero A s s (hdiagA s)
        nlinarith

end LeanMachine.SparseRankBounds

#print axioms LeanMachine.SparseRankBounds.card_add_width_le_mul_rank_add_two_of_cut
#print axioms LeanMachine.SparseRankBounds.card_le_mul_rank_of_cut
#print axioms LeanMachine.SparseRankBounds.card_le_mul_rank

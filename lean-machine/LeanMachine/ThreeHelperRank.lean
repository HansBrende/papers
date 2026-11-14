import LeanMachine.SparseRankBounds
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Half rank with three outgoing helpers

The four-arc exclusion suffices when every row has at most three outgoing
entries and a one-way incoming arc can only enter a row with at most two.
The proof reuses the ordered count, rooted traversal and closed-cut induction.
-/

namespace LeanMachine.ThreeHelperRank

open Finset SparseRankBounds

set_option autoImplicit false

universe u v
variable {F : Type v} [Field F] {V : Type u} [Fintype V] [DecidableEq V]

/-- A one-way arc can only enter a row with at most two outgoing entries. -/
def OneWayHeadsLow (B : Matrix V V F) : Prop :=
  ∀ ⦃u v⦄, B u v ≠ 0 → B v u = 0 → (outgoing B v).card ≤ 2

theorem oneWayHeadsLow_submatrix {U : Type*} [Fintype U] [DecidableEq U]
    (B : Matrix V V F) (f : U → V) (hf : Function.Injective f)
    (hB : OneWayHeadsLow B) : OneWayHeadsLow (B.submatrix f f) := by
  intro u v huv hvu
  exact (outgoing_submatrix_card_le B f hf v).trans (hB huv hvu)

/-- A row reached by an earlier row introduces at most two columns:
on a reciprocal arc both endpoint columns are old; on a one-way arc
the new row already has outgoing width at most two. -/
theorem newColumns_card_le_two {n : ℕ}
    (B : Matrix (Fin n) (Fin n) F) (hdiag : ∀ i, B i i ≠ 0)
    (hdegree : ∀ i, (outgoing B i).card ≤ 3) (hheads : OneWayHeadsLow B)
    (i : Fin n) (hown : ∃ p, p.val < i.val ∧ B p i ≠ 0) :
    (OrderedRowRank.newColumns B i).card ≤ 2 := by
  classical
  obtain ⟨p, hp, hpi⟩ := hown
  by_cases hip : B i p = 0
  · exact (newColumns_le_outgoing B i ⟨p, hp, hpi⟩).trans (hheads hpi hip)
  · have hpout : p ∈ outgoing B i :=
      (mem_outgoing B i p).mpr ⟨fun heq => by subst p; omega, hip⟩
    have hsub : OrderedRowRank.newColumns B i ⊆ (outgoing B i).erase p := by
      intro j hj
      obtain ⟨hij, hzero⟩ := (OrderedRowRank.mem_newColumns B i j).mp hj
      apply Finset.mem_erase.mpr
      constructor
      · intro hjp
        exact hdiag p (by simpa only [hjp] using hzero p hp)
      · apply (mem_outgoing B i j).mpr
        refine ⟨?_, hij⟩
        rintro rfl
        exact hpi (hzero p hp)
    have hc := Finset.card_le_card hsub
    have he := Finset.card_erase_add_one hpout
    have hd := hdegree i
    omega

/-- The exact traversal charge retains the outgoing degree of its chosen
root. In particular a root with at most two outgoing entries gives half. -/
theorem card_add_two_le_two_mul_rank_add_root_degree_of_cut
    (B : Matrix V V F) (hdiag : ∀ i, B i i ≠ 0)
    (hpattern : LastRowSupport.NoFourArcPattern B)
    (hdegree : ∀ i, (outgoing B i).card ≤ 3) (hheads : OneWayHeadsLow B)
    (hrank : 2 ≤ B.rank) (s : V)
    (hcut : ∀ P : Finset V, s ∈ P → P ≠ univ →
      ∃ u ∈ P, ∃ v ∉ P, B u v ≠ 0) :
    Fintype.card V + 2 ≤ 2 * B.rank + (outgoing B s).card := by
  classical
  obtain ⟨e, hfirst, he⟩ := SupportTraversal.exists_equiv
    (fun u v => B u v ≠ 0) s hcut
  let Q := B.submatrix e e
  have hQr : Q.rank = B.rank := Matrix.rank_submatrix B e e
  have hQd : ∀ i, (outgoing Q i).card ≤ 3 := fun i =>
    (outgoing_submatrix_card_le B e e.injective i).trans (hdegree (e i))
  have hQdiag : ∀ i, Q i i ≠ 0 := fun i => hdiag (e i)
  have hQheads : OneWayHeadsLow Q := oneWayHeadsLow_submatrix B e e.injective hheads
  have hown : ∀ i : Fin (Fintype.card V), 0 < i.val →
      ∃ p, p.val < i.val ∧ Q p i ≠ 0 := by
    intro i hi
    obtain ⟨p, hp, hpi⟩ := he i hi
    exact ⟨p, hp, hpi⟩
  have hcount := OrderedRowRank.rank_count_of_order Q ((outgoing B s).card + 1) 2
    hQdiag (noFourArcPattern_submatrix B e e.injective hpattern)
    (hQr.symm ▸ hrank)
    (fun i hi => (newColumns_le_outgoing_add_one Q i).trans
      (Nat.add_le_add_right (by
        simpa only [hfirst i hi] using outgoing_submatrix_card_le B e e.injective i) 1))
    (fun i hi => newColumns_card_le_two Q hQdiag hQd hQheads i (hown i hi)) hown
  rw [hQr] at hcount
  have hr := Nat.sub_add_cancel hrank
  omega

/-- If every outgoing degree is three, the one-way-head condition makes
the support an undirected cubic graph. The handshaking lemma gives parity. -/
theorem even_card_of_outgoing_eq_three (B : Matrix V V F)
    (hdegree : ∀ i, (outgoing B i).card = 3) (hheads : OneWayHeadsLow B) :
    Even (Fintype.card V) := by
  classical
  have hsym : ∀ u v, B u v ≠ 0 → B v u ≠ 0 := by
    intro u v huv hvu
    have h := hheads huv hvu
    rw [hdegree v] at h
    omega
  let G : SimpleGraph V :=
    { Adj := fun u v => u ≠ v ∧ B u v ≠ 0
      symm := ⟨by intro u v h; exact ⟨h.1.symm, hsym u v h.2⟩⟩
      loopless := ⟨by intro v h; exact h.1 rfl⟩ }
  have hnb : ∀ v, G.neighborFinset v = outgoing B v := by
    intro v
    ext w
    simp only [SimpleGraph.mem_neighborFinset, mem_outgoing]
    change (v ≠ w ∧ B v w ≠ 0) ↔ (w ≠ v ∧ B v w ≠ 0)
    rw [ne_comm]
  have hd : ∀ v, G.degree v = 3 := by
    intro v
    rw [← G.card_neighborFinset_eq_degree v, hnb v, hdegree v]
  have hev := G.even_card_odd_degree_vertices
  have hodd : Odd (3 : ℕ) := by decide
  simpa [hd, hodd] using hev

/-- The rank-at-least-two case without closed principal cuts. A low-degree
root gives the bound directly; otherwise cubic parity removes the extra one. -/
theorem card_le_two_mul_rank_of_cuts (B : Matrix V V F)
    (hdiag : ∀ i, B i i ≠ 0) (hpattern : LastRowSupport.NoFourArcPattern B)
    (hdegree : ∀ i, (outgoing B i).card ≤ 3) (hheads : OneWayHeadsLow B)
    (hrank : 2 ≤ B.rank)
    (hcut : ∀ P : Finset V, P.Nonempty → P ≠ univ →
      ∃ u ∈ P, ∃ v ∉ P, B u v ≠ 0) :
    Fintype.card V ≤ 2 * B.rank := by
  classical
  by_cases hlow : ∃ s, (outgoing B s).card ≤ 2
  · obtain ⟨s, hs⟩ := hlow
    have hc := card_add_two_le_two_mul_rank_add_root_degree_of_cut
      B hdiag hpattern hdegree hheads hrank s
      (fun P hsP hproper => hcut P ⟨s, hsP⟩ hproper)
    omega
  · have hall : ∀ i, (outgoing B i).card = 3 := by
      intro i
      have hi := hdegree i
      have hni : ¬ (outgoing B i).card ≤ 2 := fun hi => hlow ⟨i, hi⟩
      omega
    obtain ⟨m, hm⟩ := even_card_of_outgoing_eq_three B hall hheads
    cases isEmpty_or_nonempty V with
    | inl h => simp
    | inr h =>
      let s : V := Classical.choice h
      have hc := card_add_two_le_two_mul_rank_add_root_degree_of_cut
        B hdiag hpattern hdegree hheads hrank s
        (fun P hsP hproper => hcut P ⟨s, hsP⟩ hproper)
      rw [hall s] at hc
      omega

/-- Three outgoing helpers give half rank under the four-arc exclusion,
provided every one-way arc enters a row with at most two outgoing helpers.
There is no bound on incoming degrees at those lower-degree rows. -/
theorem card_le_two_mul_rank (B : Matrix V V F)
    (hdiag : ∀ i, B i i ≠ 0) (hpattern : LastRowSupport.NoFourArcPattern B)
    (hdegree : ∀ i, (outgoing B i).card ≤ 3) (hheads : OneWayHeadsLow B) :
    Fintype.card V ≤ 2 * B.rank := by
  classical
  let Q : ∀ (W : Type u) [Fintype W] [DecidableEq W], Matrix W W F → Prop :=
    fun W _ _ A => (∀ i, A i i ≠ 0) ∧ LastRowSupport.NoFourArcPattern A ∧
      (∀ i, (outgoing A i).card ≤ 3) ∧ OneWayHeadsLow A
  refine ClosedCutRank.card_le_mul_rank_of_closed_cuts Q 2 ?_ ?_ B
    ⟨hdiag, hpattern, hdegree, hheads⟩
  · intro W U _ _ _ _ A f hf hA
    exact ⟨fun i => hA.1 (f i), noFourArcPattern_submatrix A f hf hA.2.1,
      fun i => (outgoing_submatrix_card_le A f hf i).trans (hA.2.2.1 (f i)),
      oneWayHeadsLow_submatrix A f hf hA.2.2.2⟩
  · intro W _ _ A hA hcut
    obtain ⟨hdiagA, hpatternA, hdegreeA, hheadsA⟩ := hA
    by_cases hrank : 2 ≤ A.rank
    · exact card_le_two_mul_rank_of_cuts A hdiagA hpatternA hdegreeA hheadsA hrank hcut
    · have hc := ClosedCutRank.card_le_two_of_rank_le_one A hdiagA hpatternA (by omega)
      cases isEmpty_or_nonempty W with
      | inl h => simp
      | inr h =>
        let s : W := Classical.choice h
        have hpos := ClosedCutRank.one_le_rank_of_entry_ne_zero A s s (hdiagA s)
        omega

end LeanMachine.ThreeHelperRank

#print axioms LeanMachine.ThreeHelperRank.card_add_two_le_two_mul_rank_add_root_degree_of_cut
#print axioms LeanMachine.ThreeHelperRank.even_card_of_outgoing_eq_three
#print axioms LeanMachine.ThreeHelperRank.card_le_two_mul_rank_of_cuts
#print axioms LeanMachine.ThreeHelperRank.card_le_two_mul_rank

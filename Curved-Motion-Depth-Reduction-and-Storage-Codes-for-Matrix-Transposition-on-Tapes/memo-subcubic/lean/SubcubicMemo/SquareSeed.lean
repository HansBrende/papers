import SubcubicMemo.LadderGeometry

/-! Every hypothetical bad connected component contains a three-rung ladder. -/

namespace SubcubicMemo.Squares

open Finset MotionDepthCodes
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (h : Hyp G) (hc : G.Preconnected) (hn : ¬ Nonempty (G →g circularClique 8 3))

include h hc hn in
theorem two_squares_ladder {u v a b x y : V} (s : Square G u v a b)
    (t : Square G u x y v) (hx : x ∉ ({u,v,a,b} : Finset V)) :
    Nonempty (Ladder G 3) := by
  have hx' : x≠u ∧ x≠v ∧ x≠a ∧ x≠b := by simpa using hx
  have hyu : y≠u := Ne.symm t.2.2.2.2.1
  have hyv : y≠v := t.2.2.1.ne
  have hya : y≠a := by
    intro he; subst y
    exact no_three_common h hc hn s.2.2.2.2.1 s.2.2.2.2.2
      (Ne.symm hx'.2.1) (Ne.symm hx'.2.2.2)
      s.1 s.2.2.2.1.symm t.1 s.2.1.symm s.2.2.1 t.2.1.symm
  have hyb : y≠b := by
    intro he; subst y
    exact no_triangle G h.triangle s.1 s.2.2.2.1.symm t.2.2.1.symm
  let f : Fin 3 × Bool → V := fun p =>
    ![![b,a],![u,v],![x,y]] p.1 (if p.2 then (1 : Fin 2) else 0)
  have hf : Function.Injective f := by
    rintro ⟨i,c⟩ ⟨j,d⟩ he
    fin_cases i <;> fin_cases j <;> cases c <;> cases d <;> simp [f] at he ⊢ <;>
      first | rfl | exact False.elim (by
        have := s.1.ne; have := s.2.1.ne; have := s.2.2.1.ne
        have := s.2.2.2.1.ne; have := s.2.2.2.2.1; have := s.2.2.2.2.2
        have := t.2.1.ne
        grind)
  refine ⟨{ vert := ⟨f,hf⟩, rung := ?_, rail := ?_ }⟩
  · intro i c
    fin_cases i <;> cases c <;> simp only [f] <;>
      first | exact s.2.2.1 | exact s.2.2.1.symm | exact s.1 | exact s.1.symm |
        exact t.2.1 | exact t.2.1.symm
  · intro i j c hij
    fin_cases i <;> fin_cases j <;> cases c <;> simp_all [f,SimpleGraph.adj_comm] <;>
      first | exact s.2.2.2.1 | exact s.2.2.2.1.symm | exact s.2.1 | exact s.2.1.symm |
        exact t.1 | exact t.1.symm | exact t.2.2.1 | exact t.2.2.1.symm

include h hc hn in
theorem square_outside_ladder {u v a b x : V} (s : Square G u v a b)
    (hx : x ∉ ({u,v,a,b} : Finset V)) (hux : G.Adj u x) :
    Nonempty (Ladder G 3) := by
  have hx' : x≠u ∧ x≠v ∧ x≠a ∧ x≠b := by simpa using hx
  obtain ⟨y,z,t⟩ := h.covered u x hux
  have hz := neighbor_of_three G h.degree s.1 s.2.2.2.1.symm hux s.2.2.2.2.2
    (Ne.symm hx'.2.1) (Ne.symm hx'.2.2.2) t.2.2.2.1.symm
  rcases hz with hz | hz | hz
  · subst z; exact two_squares_ladder h hc hn s t hx
  · subst z
    apply two_squares_ladder h hc hn ((s.reverse G).rotate G) t
    simpa [or_comm,or_left_comm,or_assoc] using hx
  · exact False.elim (t.2.2.2.2.2 hz.symm)

include h hc in
theorem square_closed_hom {u v a b : V} (s : Square G u v a b)
    (hclosed : ∀ w ∈ ({u,v,a,b} : Finset V), ∀ x, G.Adj w x → x ∈ ({u,v,a,b} : Finset V)) :
    Nonempty (G →g circularClique 8 3) := by
  have huv := s.1.ne
  have hva := s.2.1.ne
  have hab := s.2.2.1.ne
  have hbu := s.2.2.2.1.ne
  have hua := s.2.2.2.2.1
  have hvb := s.2.2.2.2.2
  apply hom_of_closed_bipartition G hc {u,a} {v,b}
  · exact ⟨u,by simp⟩
  · simp [huv,huv.symm,hbu,hbu.symm,hva,hva.symm,hab,hab.symm]
  · intro w hw x hwx
    have hx := hclosed w (by simp only [mem_insert,mem_singleton] at hw ⊢; aesop) x hwx
    simp only [mem_insert,mem_singleton] at hw hx ⊢
    rcases hw with rfl | rfl <;> rcases hx with rfl | rfl | rfl | rfl
    all_goals first | exact Or.inl rfl | exact Or.inr rfl | exact False.elim (G.irrefl hwx) |
      exact False.elim (no_triangle G h.triangle s.1.symm s.2.1 hwx) |
      exact False.elim (no_triangle G h.triangle s.1.symm s.2.1 hwx.symm)
  · intro w hw x hwx
    have hx := hclosed w (by simp only [mem_insert,mem_singleton] at hw ⊢; aesop) x hwx
    simp only [mem_insert,mem_singleton] at hw hx ⊢
    rcases hw with rfl | rfl <;> rcases hx with rfl | rfl | rfl | rfl
    all_goals first | exact Or.inl rfl | exact Or.inr rfl | exact False.elim (G.irrefl hwx) |
      exact False.elim (no_triangle G h.triangle s.1 s.2.2.2.1.symm hwx) |
      exact False.elim (no_triangle G h.triangle s.1 s.2.2.2.1.symm hwx.symm)

include h hc hn in
theorem three_rung_seed : Nonempty (Ladder G 3) := by
  have he : ∃ u v, G.Adj u v := by
    by_contra hh
    apply hn
    exact ⟨{ toFun := fun _ => 0, map_rel' := fun {u v} huv => False.elim (hh ⟨u,v,huv⟩) }⟩
  obtain ⟨u,v,huv⟩ := he
  obtain ⟨a,b,s⟩ := h.covered u v huv
  have hnot : ¬ (∀ w ∈ ({u,v,a,b} : Finset V), ∀ x, G.Adj w x → x ∈ ({u,v,a,b} : Finset V)) :=
    fun hh => hn (square_closed_hom h hc s hh)
  push Not at hnot
  obtain ⟨w,hw,x,hwx,hx⟩ := hnot
  simp only [mem_insert,mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact square_outside_ladder h hc hn s hx hwx
  · apply square_outside_ladder h hc hn (s.rotate G) _ hwx
    simpa [or_comm,or_left_comm,or_assoc] using hx
  · apply square_outside_ladder h hc hn ((s.rotate G).rotate G) _ hwx
    simpa [or_comm,or_left_comm,or_assoc] using hx
  · apply square_outside_ladder h hc hn (((s.rotate G).rotate G).rotate G) _ hwx
    simpa [or_comm,or_left_comm,or_assoc] using hx

end SubcubicMemo.Squares

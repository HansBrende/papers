import SubcubicMemo.LadderGeometry
import SubcubicMemo.LadderTargets

/-! A spanning ladder has only a partial matching between its ends.
It therefore maps to one of the closed ladders already certified. -/

namespace SubcubicMemo.Squares

open Finset MotionDepthCodes
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (h : Hyp G)

namespace Ladder

variable {n : ℕ} (L : Ladder G (n+3))

include h in
theorem cross_left_injective {b c d : Bool}
    (hc : G.Adj (L.v 0 b) (L.v (Fin.last (n+2)) c))
    (hd : G.Adj (L.v 0 b) (L.v (Fin.last (n+2)) d)) : c=d := by
  let i : Fin (n+3) := ⟨1,by omega⟩
  have hr := neighbor_of_three G h.degree (L.rung 0 b) (L.rail 0 i b rfl) hc
    (by intro he; have := congrArg Fin.val (L.v_inj.mp he).1; simp [i] at this)
    (by intro he; have := congrArg Fin.val (L.v_inj.mp he).1; simp at this)
    (by intro he; have := congrArg Fin.val (L.v_inj.mp he).1; simp [i] at this) hd
  rcases hr with he | he | he
  · have := congrArg Fin.val (L.v_inj.mp he).1
    simp at this
  · have := congrArg Fin.val (L.v_inj.mp he).1
    simp [i] at this
  · exact (L.v_inj.mp he).2.symm

include h in
theorem cross_right_injective {b c d : Bool}
    (hc : G.Adj (L.v 0 c) (L.v (Fin.last (n+2)) b))
    (hd : G.Adj (L.v 0 d) (L.v (Fin.last (n+2)) b)) : c=d := by
  exact L.reverse.cross_left_injective h (by simpa using hc.symm) (by simpa using hd.symm)

include h in
theorem cross_twist {a b c d : Bool}
    (hab : G.Adj (L.v 0 a) (L.v (Fin.last (n+2)) b))
    (hcd : G.Adj (L.v 0 c) (L.v (Fin.last (n+2)) d)) : (a ^^ b)=(c ^^ d) := by
  by_cases hac : a=c
  · subst c
    rw [L.cross_left_injective h hab hcd]
  · have hbd : b ≠ d := by
      intro he; subst d
      exact hac (L.cross_right_injective h hab hcd)
    cases a <;> cases b <;> cases c <;> cases d <;>
      first | rfl | exact False.elim (hac rfl) | exact False.elim (hbd rfl)

include h in
theorem interior_edge {i j : Fin (n+3)} {b c : Bool}
    (hi : 0 < i.val ∧ i.val+1 < n+3) (hij : G.Adj (L.v i b) (L.v j c)) :
    (i=j ∧ b≠c) ∨ ((i.val+1=j.val ∨ j.val+1=i.val) ∧ b=c) := by
  let p : Fin (n+3) := ⟨i.val-1,by omega⟩
  let q : Fin (n+3) := ⟨i.val+1,by omega⟩
  have hr := L.internal_neighbor h (i₀ := p) (i₁ := q) (by dsimp [p]; omega) rfl b hij
  rcases hr with he | he | he
  · obtain ⟨hj,hc⟩ := L.v_inj.mp he
    subst j; subst c
    exact Or.inr ⟨Or.inr (by dsimp [p]; omega),rfl⟩
  · obtain ⟨hj,hc⟩ := L.v_inj.mp he
    subst j; subst c
    exact Or.inr ⟨Or.inl rfl,rfl⟩
  · obtain ⟨hj,hc⟩ := L.v_inj.mp he
    subst j; subst c
    exact Or.inl ⟨rfl,by simp⟩

include h in
theorem edge_shape {i j : Fin (n+3)} {b c : Bool}
    (hij : G.Adj (L.v i b) (L.v j c)) :
    (i=j ∧ b≠c) ∨ ((i.val+1=j.val ∨ j.val+1=i.val) ∧ b=c) ∨
    ((i.val=0 ∧ j.val+1=n+3) ∨ (j.val=0 ∧ i.val+1=n+3)) := by
  by_cases he : i=j
  · subst j
    exact Or.inl ⟨rfl,fun he => hij.ne (congrArg (L.v i) he)⟩
  by_cases hi : 0 < i.val ∧ i.val+1 < n+3
  · rcases L.interior_edge h hi hij with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  by_cases hj : 0 < j.val ∧ j.val+1 < n+3
  · rcases L.interior_edge h hj hij.symm with h | h
    · exact Or.inl ⟨h.1.symm,Ne.symm h.2⟩
    · exact Or.inr (Or.inl ⟨h.1.symm,h.2.symm⟩)
  · have hne : i.val ≠ j.val := fun hh => he (Fin.ext hh)
    exact Or.inr (Or.inr (by omega))

include h in
theorem closed_target (hsurj : Function.Surjective L.vert) :
    Nonempty (G →g circularClique 8 3) := by
  have choice : ∃ t : Bool, (n=0 → t=true) ∧
      ∀ b c, G.Adj (L.v 0 b) (L.v (Fin.last (n+2)) c) → (b ^^ c)=t := by
    by_cases hh : ∃ b c, G.Adj (L.v 0 b) (L.v (Fin.last (n+2)) c)
    · obtain ⟨b,c,hbc⟩ := hh
      refine ⟨b ^^ c,?_,fun d e hde => L.cross_twist h hde hbc⟩
      intro hn
      subst n
      have hne : b ≠ c := by
        intro he; subst c
        exact no_triangle G h.triangle (L.rail 0 1 b rfl).symm (L.rail 1 2 b rfl) hbc
      cases b <;> cases c <;> simp_all
    · exact ⟨true,fun _ => rfl,fun b c hh' => False.elim (hh ⟨b,c,hh'⟩)⟩
  obtain ⟨t,ht,hcross⟩ := choice
  have hmap {i j : Fin (n+3)} {b c : Bool} (ha : G.Adj (L.v i b) (L.v j c)) :
      (closedLadder (n+3) t).Adj (i,b) (j,c) := by
    rcases L.edge_shape h ha with hh | hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
    · apply Or.inr; apply Or.inr
      refine ⟨hh,?_,?_⟩
      · change i ≠ j
        intro he; subst j; omega
      · rcases hh with hh | hh
        · have hi : i=0 := Fin.ext hh.1
          have hj : j=Fin.last (n+2) := by apply Fin.ext; simp only [Fin.val_last]; omega
          subst i; subst j; exact hcross b c ha
        · have hj : j=0 := Fin.ext hh.1
          have hi : i=Fin.last (n+2) := by apply Fin.ext; simp only [Fin.val_last]; omega
          subst i; subst j
          simpa [Bool.xor_comm] using hcross c b ha.symm
  let e : (Fin (n+3) × Bool) ≃ V := Equiv.ofBijective L.vert ⟨L.vert.injective,hsurj⟩
  let f : G →g closedLadder (n+3) t :=
    { toFun := e.symm
      map_rel' := by
        intro u v huv
        apply hmap
        change G.Adj (e (e.symm u)) (e (e.symm v))
        simpa using huv }
  exact ⟨(ladder_target (n+3) t (by omega) (by intro he; exact ht (by omega))).some.comp f⟩

end Ladder

end SubcubicMemo.Squares

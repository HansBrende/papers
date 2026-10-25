import SubcubicMemo.LadderExtension

/-! A longest embedded ladder has no attachments outside its vertices. -/

namespace SubcubicMemo.Squares

open Finset MotionDepthCodes
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (h : Hyp G) (hc : G.Preconnected) (hn : ¬ Nonempty (G →g circularClique 8 3))

namespace Ladder

include h in
theorem outside_at_end {n : ℕ} (L : Ladder G n) {i : Fin n} {b : Bool} {x : V}
    (hx : ∀ j c, x ≠ L.v j c) (hix : G.Adj (L.v i b) x) :
    i.val = 0 ∨ i.val+1=n := by
  by_contra hh
  push Not at hh
  let j : Fin n := ⟨i.val-1,by omega⟩
  let k : Fin n := ⟨i.val+1,by omega⟩
  have hr := L.internal_neighbor h (i₀ := j) (i₁ := k) (by dsimp [j]; omega) rfl b hix
  rcases hr with hr | hr | hr <;> exact hx _ _ hr

include h in
theorem extra_fresh {n : ℕ} (L : Ladder G (n+3)) (b : Bool) {x y : V}
    (hx : ∀ j c, x ≠ L.v j c)
    (hs : Square G (L.v (Fin.last (n+2)) b) x y (L.v (Fin.last (n+2)) (!b))) :
    ∀ j c, y ≠ L.v j c := by
  intro j c he
  subst y
  have hj := L.outside_at_end h hx hs.2.1.symm
  rcases hj with hj | hj
  · have hj0 : j = 0 := Fin.ext hj
    subst j
    let k : Fin (n+3) := ⟨1,by omega⟩
    have hthird := hs.2.2.1
    have hr := neighbor_of_three G h.degree (L.rung 0 c) (L.rail 0 k c rfl) hthird
      (by intro he; have := congrArg Fin.val (L.v_inj.mp he).1; simp [k] at this)
      (by intro he; have := congrArg Fin.val (L.v_inj.mp he).1; simp at this)
      (by intro he; have := congrArg Fin.val (L.v_inj.mp he).1; simp [k] at this)
      hs.2.1.symm
    rcases hr with hr | hr | hr <;> exact hx _ _ hr
  · have hjn : j = Fin.last (n+2) := by apply Fin.ext; simp only [Fin.val_last]; omega
    subst j
    cases b <;> cases c
    · exact hs.2.2.2.2.1 rfl
    · exact G.irrefl hs.2.2.1
    · exact G.irrefl hs.2.2.1
    · exact hs.2.2.2.2.1 rfl

include h hc hn in
theorem extend_of_outside {n : ℕ} (L : Ladder G (n+3)) (b : Bool) {x : V}
    (hx : ∀ j c, x ≠ L.v j c) (hax : G.Adj (L.v (Fin.last (n+2)) b) x) :
    Nonempty (Ladder G (n+4)) := by
  let i₀ : Fin (n+3) := ⟨n,by omega⟩
  let i : Fin (n+3) := ⟨n+1,by omega⟩
  obtain ⟨y,hs⟩ := L.extra_square h hc hn (i₀ := i₀) (i := i)
    (i₁ := Fin.last (n+2)) rfl rfl b hx hax
  have hy := L.extra_fresh h b hx hs
  let f : Bool → V := fun c => if c=b then x else y
  have hfi : Function.Injective f := by
    intro c d he
    cases b <;> cases c <;> cases d <;> simp_all [f,hs.2.1.ne,hs.2.1.ne.symm]
  refine ⟨L.extend f hfi ?_ ?_ ?_⟩
  · intro j c d
    dsimp [f]
    split_ifs
    · exact hx j d
    · exact hy j d
  · intro c
    cases b <;> cases c <;> simp only [f,ite_true,ite_false,Bool.not_true,Bool.not_false,
      Bool.true_eq_false,Bool.false_eq_true] <;> first | exact hs.2.1 | exact hs.2.1.symm
  · intro c
    cases b <;> cases c <;> simp only [f,ite_true,ite_false,Bool.not_true,Bool.not_false,
      Bool.true_eq_false,Bool.false_eq_true] <;> first | exact hax | exact hs.2.2.1.symm

include h hc hn in
theorem longest_closed {n : ℕ} (L : Ladder G (n+3))
    (hmax : ¬ Nonempty (Ladder G (n+4))) :
    ∀ i b x, G.Adj (L.v i b) x → ∃ j c, x=L.v j c := by
  intro i b x hix
  by_contra hh
  push Not at hh
  have hi := L.outside_at_end h hh hix
  rcases hi with hi | hi
  · have hi0 : i=0 := Fin.ext hi
    subst i
    have hf : ∀ j c, x ≠ L.reverse.v j c := fun j c => hh j.rev c
    have ha : G.Adj (L.reverse.v (Fin.last (n+2)) b) x := by simpa using hix
    exact hmax (L.reverse.extend_of_outside h hc hn b hf ha)
  · have hin : i=Fin.last (n+2) := by apply Fin.ext; simp only [Fin.val_last]; omega
    subst i
    exact hmax (L.extend_of_outside h hc hn b hh hix)

end Ladder

end SubcubicMemo.Squares

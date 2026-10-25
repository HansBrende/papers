import SubcubicMemo.LadderGeometry

/-! Extending an embedded ladder by a new rung. -/

namespace SubcubicMemo.Squares

open Finset MotionDepthCodes
open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

namespace Ladder

def extendFun (L : Ladder G (n+1)) (x : Bool → V) (p : Fin (n+2) × Bool) : V :=
  Fin.snoc (α := fun _ => V) (fun i => L.v i p.2) (x p.2) p.1

theorem extendFun_injective (L : Ladder G (n+1)) (x : Bool → V)
    (hx : Function.Injective x) (hfresh : ∀ i b c, x b ≠ L.v i c) :
    Function.Injective (extendFun L x) := by
    rintro ⟨i,b⟩ ⟨j,c⟩ he
    change Fin.snoc (α := fun _ => V) (fun i => L.v i b) (x b) i =
      Fin.snoc (α := fun _ => V) (fun i => L.v i c) (x c) j at he
    cases i using Fin.lastCases <;> cases j using Fin.lastCases
    · simp only [Fin.snoc_last] at he
      exact Prod.ext rfl (hx he)
    · simp only [Fin.snoc_last, Fin.snoc_castSucc] at he
      exact False.elim (hfresh _ _ _ he)
    · simp only [Fin.snoc_last, Fin.snoc_castSucc] at he
      exact False.elim (hfresh _ _ _ he.symm)
    · simp only [Fin.snoc_castSucc] at he
      obtain ⟨hi,hb⟩ := L.v_inj.mp he
      exact Prod.ext (congrArg Fin.castSucc hi) hb

def extend (L : Ladder G (n+1)) (x : Bool → V) (hx : Function.Injective x)
    (hfresh : ∀ i b c, x b ≠ L.v i c)
    (hrung : ∀ b, G.Adj (x b) (x (!b)))
    (hrail : ∀ b, G.Adj (L.v (Fin.last n) b) (x b)) : Ladder G (n+2) where
  vert := ⟨extendFun L x,extendFun_injective L x hx hfresh⟩
  rung i b := by
    change G.Adj (extendFun L x (i,b)) (extendFun L x (i,!b))
    simp only [extendFun]
    cases i using Fin.lastCases <;> simp only [Fin.snoc_last,Fin.snoc_castSucc]
    · exact hrung b
    · exact L.rung _ b
  rail i j b hij := by
    change G.Adj (extendFun L x (i,b)) (extendFun L x (j,b))
    simp only [extendFun]
    cases i using Fin.lastCases with
    | last => simp only [Fin.val_last] at hij; omega
    | cast i =>
      cases j using Fin.lastCases with
      | last =>
        have hi : i = Fin.last n := by apply Fin.ext; simp only [Fin.val_castSucc,Fin.val_last] at hij ⊢; omega
        subst i
        simp only [Fin.snoc_castSucc,Fin.snoc_last]
        exact hrail b
      | cast j =>
        simp only [Fin.snoc_castSucc]
        exact L.rail i j b hij

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  (h : Hyp G) (hc : G.Preconnected) (hn : ¬ Nonempty (G →g circularClique 8 3))
  (L : Ladder G n)

include h hc hn in
theorem extra_square {i₀ i i₁ : Fin n} (h₀ : i₀.val+1=i.val)
    (h₁ : i.val+1=i₁.val) (b : Bool) {x : V}
    (hx : ∀ j c, x ≠ L.v j c) (hax : G.Adj (L.v i₁ b) x) :
    ∃ y, Square G (L.v i₁ b) x y (L.v i₁ (!b)) := by
  obtain ⟨y,z,hs⟩ := h.covered _ _ hax
  have hz := neighbor_of_three G h.degree (L.rail i i₁ b h₁).symm (L.rung i₁ b)
    hax (by intro he; have := congrArg Fin.val (L.v_inj.mp he).1; omega)
    (Ne.symm (hx i b)) (Ne.symm (hx i₁ (!b))) hs.2.2.2.1.symm
  rcases hz with hz | hz | hz
  · subst z
    have hy := L.internal_neighbor h h₀ h₁ b hs.2.2.1.symm
    rcases hy with hy | hy | hy
    · subst y
      apply False.elim (L.no_rail_square h hc hn h₀ h₁ b x ?_)
      exact ⟨(L.rail i₀ i b h₀).symm,hs.2.1.symm,hax.symm,
        (L.rail i i₁ b h₁).symm,Ne.symm (hx i b),by
          intro he; have := congrArg Fin.val (L.v_inj.mp he).1; omega⟩
    · exact False.elim (hs.2.2.2.2.1 hy.symm)
    · subst y
      exfalso
      apply no_three_common h hc hn (p := L.v i₁ b) (q := L.v i (!b))
        (a := L.v i b) (b := L.v i₁ (!b)) (c := x) ?_ ?_
        (Ne.symm (hx i b)) (Ne.symm (hx i₁ (!b)))
        (L.rail i i₁ b h₁).symm (L.rung i₁ b) hax (L.rung i b).symm
        (L.rail i i₁ (!b) h₁) hs.2.1.symm
      · intro he; have := congrArg Fin.val (L.v_inj.mp he).1; omega
      · intro he; have := congrArg Fin.val (L.v_inj.mp he).1; omega
  · subst z; exact ⟨y,hs⟩
  · exact False.elim (hs.2.2.2.2.2 hz.symm)

end Ladder

end SubcubicMemo.Squares

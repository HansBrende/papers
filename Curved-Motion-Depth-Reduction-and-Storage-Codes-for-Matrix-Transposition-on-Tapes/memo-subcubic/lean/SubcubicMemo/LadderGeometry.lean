import SubcubicMemo.SquareFork
import Mathlib.Data.Fin.Rev

/-! Embedded open ladders and their saturated interior vertices. -/

namespace SubcubicMemo.Squares

open Finset MotionDepthCodes
open scoped Classical

variable {V : Type*} {G : SimpleGraph V}

structure Ladder (G : SimpleGraph V) (n : ℕ) where
  vert : Fin n × Bool ↪ V
  rung : ∀ i b, G.Adj (vert (i,b)) (vert (i,!b))
  rail : ∀ i j b, i.val+1=j.val → G.Adj (vert (i,b)) (vert (j,b))

namespace Ladder

variable {n : ℕ} (L : Ladder G n)

def v (i : Fin n) (b : Bool) : V := L.vert (i,b)

theorem v_inj {i j : Fin n} {b c : Bool} : L.v i b = L.v j c ↔ i=j ∧ b=c := by
  change L.vert (i,b) = L.vert (j,c) ↔ _
  rw [L.vert.injective.eq_iff, Prod.mk.injEq]

theorem v_ne_flip (i : Fin n) (b : Bool) : L.v i b ≠ L.v i (!b) := by
  simp [v_inj]

theorem square {i j : Fin n} (hij : i.val+1=j.val) (b : Bool) :
    Square G (L.v i b) (L.v j b) (L.v j (!b)) (L.v i (!b)) := by
  have hn : i ≠ j := by intro he; subst j; omega
  exact ⟨L.rail i j b hij,L.rung j b,(L.rail i j (!b) hij).symm,
    (L.rung i b).symm,fun he => hn (v_inj L |>.mp he).1,
    fun he => hn (v_inj L |>.mp he).1.symm⟩

def reverse : Ladder G n where
  vert := ⟨fun x => L.v x.1.rev x.2,by
    rintro ⟨i,b⟩ ⟨j,c⟩ he
    obtain ⟨hi,hb⟩ := (L.v_inj).mp he
    exact Prod.ext (Fin.rev_injective hi) hb⟩
  rung i b := L.rung i.rev b
  rail i j b hij := (L.rail j.rev i.rev b (by simp only [Fin.val_rev]; omega)).symm

@[simp] theorem reverse_v (i : Fin n) (b : Bool) : L.reverse.v i b = L.v i.rev b := rfl

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  (h : Hyp G)

include h in
theorem internal_neighbor {i₀ i i₁ : Fin n} (h₀ : i₀.val+1=i.val)
    (h₁ : i.val+1=i₁.val) (b : Bool) {x : V} (hx : G.Adj (L.v i b) x) :
    x = L.v i₀ b ∨ x = L.v i₁ b ∨ x = L.v i (!b) := by
  apply neighbor_of_three G h.degree (L.rail i₀ i b h₀).symm (L.rail i i₁ b h₁)
    (L.rung i b) ?_ ?_ ?_ hx
  · intro he
    have := congrArg Fin.val ((L.v_inj).mp he).1
    omega
  · intro he
    have := congrArg Fin.val ((L.v_inj).mp he).1
    omega
  · intro he
    have := congrArg Fin.val ((L.v_inj).mp he).1
    omega

variable (hc : G.Preconnected) (hn : ¬ Nonempty (G →g circularClique 8 3))

include h hc hn in
theorem no_rail_square {i₀ i i₁ : Fin n} (h₀ : i₀.val+1=i.val)
    (h₁ : i.val+1=i₁.val) (b : Bool) (x : V) :
    ¬ Square G (L.v i b) (L.v i₀ b) x (L.v i₁ b) := by
  intro hx
  apply no_three_wedges h hc hn (a := L.v i₀ b) (b := L.v i₁ b)
    (c := L.v i (!b)) (z := L.v i₀ (!b)) ?_ ?_ ?_ hx (L.square h₁ b) ?_
  · intro he
    have := congrArg Fin.val ((L.v_inj).mp he).1
    omega
  · intro he
    have := congrArg Fin.val ((L.v_inj).mp he).1
    omega
  · intro he
    have := congrArg Fin.val ((L.v_inj).mp he).1
    omega
  · exact (L.square h₀ b).rotate G

end Ladder

end SubcubicMemo.Squares

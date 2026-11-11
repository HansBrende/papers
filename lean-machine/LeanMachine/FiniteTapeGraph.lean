import LeanMachine.GraphBall

/-! # The actual one-write, unit-motion graph of a finite tape

A vertex contains the whole finite word and its head. Both forward and
backward neighbors are enumerated; a backward step pays the overwritten
symbol, so the degree bound does not assume that writes are reversible.
-/

namespace LeanMachine.FiniteTapeGraph

open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

abbrev Vertex (A : Type*) (n : ℕ) := (Fin n → A) × Fin n

def Near (h h' : Fin n) : Prop := h.val ≤ h'.val + 1 ∧ h'.val ≤ h.val + 1

def Step (v w : Vertex A n) : Prop :=
  Near v.2 w.2 ∧ ∃ a : A, w.1 = Function.update v.1 v.2 a

noncomputable def graph (A : Type*) [Fintype A] [DecidableEq A] (n : ℕ) :
    SimpleGraph (Vertex A n) where
  Adj v w := v ≠ w ∧ (Step v w ∨ Step w v)
  symm := ⟨by intro v w h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

noncomputable def headNeighbors (h : Fin n) : Finset (Fin n) :=
  univ.filter (Near h)

theorem card_headNeighbors (h : Fin n) : (headNeighbors h).card ≤ 3 := by
  classical
  calc
    _ = ((headNeighbors h).image Fin.val).card := (card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Icc (h.val - 1) (h.val + 1)).card := by
      apply card_le_card
      intro j hj
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hj
      have hh := (mem_filter.mp hv).2
      simp only [mem_Icc]
      dsimp [Near] at hh
      omega
    _ ≤ 3 := by simp; omega

noncomputable def outgoing (v : Vertex A n) : Finset (Vertex A n) :=
  ((headNeighbors v.2) ×ˢ (univ : Finset A)).image
    (fun ha => (Function.update v.1 v.2 ha.2, ha.1))

noncomputable def incoming (v : Vertex A n) : Finset (Vertex A n) :=
  ((headNeighbors v.2) ×ˢ (univ : Finset A)).image
    (fun ha => (Function.update v.1 ha.1 ha.2, ha.1))

theorem outgoing_card (v : Vertex A n) : (outgoing v).card ≤ 3 * Fintype.card A := by
  classical
  calc
    _ ≤ ((headNeighbors v.2) ×ˢ (univ : Finset A)).card := card_image_le
    _ = (headNeighbors v.2).card * Fintype.card A := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (card_headNeighbors v.2)

theorem incoming_card (v : Vertex A n) : (incoming v).card ≤ 3 * Fintype.card A := by
  classical
  calc
    _ ≤ ((headNeighbors v.2) ×ˢ (univ : Finset A)).card := card_image_le
    _ = (headNeighbors v.2).card * Fintype.card A := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (card_headNeighbors v.2)

theorem step_mem_outgoing {v w : Vertex A n} (h : Step v w) : w ∈ outgoing v := by
  classical
  obtain ⟨hn, a, ha⟩ := h
  exact mem_image.mpr ⟨(w.2, a), mem_product.mpr
    ⟨mem_filter.mpr ⟨mem_univ _, hn⟩, mem_univ _⟩, Prod.ext ha.symm rfl⟩

theorem step_mem_incoming {v w : Vertex A n} (h : Step w v) : w ∈ incoming v := by
  classical
  obtain ⟨hn, a, ha⟩ := h
  refine mem_image.mpr ⟨(w.2, w.1 w.2), mem_product.mpr
    ⟨mem_filter.mpr ⟨mem_univ _, hn.symm⟩, mem_univ _⟩, Prod.ext ?_ rfl⟩
  change Function.update v.1 w.2 (w.1 w.2) = w.1
  rw [ha]
  funext i
  by_cases hi : i = w.2 <;> simp [hi]

theorem degree_le (v : Vertex A n) : (graph A n).degree v ≤ 6 * Fintype.card A := by
  classical
  have hsub : (graph A n).neighborFinset v ⊆ outgoing v ∪ incoming v := by
    intro w hw
    have h := ((graph A n).mem_neighborFinset v w).mp hw
    rcases h.2 with h | h
    · exact mem_union_left _ (step_mem_outgoing h)
    · exact mem_union_right _ (step_mem_incoming h)
  calc
    _ ≤ (outgoing v ∪ incoming v).card := card_le_card hsub
    _ ≤ (outgoing v).card + (incoming v).card := card_union_le _ _
    _ ≤ 3 * Fintype.card A + 3 * Fintype.card A := Nat.add_le_add (outgoing_card v) (incoming_card v)
    _ = _ := by omega

theorem step_edist_le {v w : Vertex A n} (h : Step v w) :
    (graph A n).edist v w ≤ 1 := by
  apply SimpleGraph.edist_le_one_iff_adj_or_eq.mpr
  by_cases he : v = w
  · exact Or.inr he
  · exact Or.inl ⟨he, Or.inl h⟩

theorem path_edist_le (v : ℕ → Vertex A n) {u l : ℕ}
    (h : ∀ j < l, Step (v (u + j)) (v (u + j + 1))) :
    (graph A n).edist (v u) (v (u + l)) ≤ (l : ℕ∞) := by
  induction l with
  | zero => simp
  | succ l ih =>
    have hp := ih (fun j hj => h j (by omega))
    have hs := step_edist_le (h l (by omega))
    calc
      _ ≤ (graph A n).edist (v u) (v (u + l)) +
          (graph A n).edist (v (u + l)) (v (u + l + 1)) :=
        SimpleGraph.edist_triangle
      _ ≤ (l : ℕ∞) + 1 := add_le_add hp hs
      _ = _ := by simp

private theorem geometric_le_pow {D : ℕ} (hD : 2 ≤ D) (R : ℕ) :
    ∑ j ∈ range (R + 1), D ^ j ≤ D ^ (R + 1) := by
  have hstrong : ∀ r : ℕ, (∑ j ∈ range (r + 1), D ^ j) + 1 ≤ D ^ (r + 1) := by
    intro r
    induction r with
    | zero => simpa using hD
    | succ r ih =>
      rw [sum_range_succ, pow_succ D (r + 1)]
      have hp : 1 ≤ D ^ (r + 1) := Nat.one_le_pow _ _ (by omega)
      nlinarith
  exact (Nat.le_add_right _ _).trans (hstrong R)

theorem card_ball_le [Nonempty A] (v : Vertex A n) (R : ℕ) :
    (GraphBall.closedBall (graph A n) v R).card ≤ (6 * Fintype.card A) ^ (R + 1) := by
  classical
  exact (GraphBall.card_closedBall_le (graph A n) _ degree_le v R).trans
    (geometric_le_pow (by have := Fintype.card_pos (α := A); omega) R)

end LeanMachine.FiniteTapeGraph

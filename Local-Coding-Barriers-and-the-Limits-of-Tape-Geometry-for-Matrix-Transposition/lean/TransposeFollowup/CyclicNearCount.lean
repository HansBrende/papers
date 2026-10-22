import TransposeFollowup.GraphNearCount
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Int.Interval

/-! Linear ball growth for a graph whose edges move by plus or minus one
fixed group element. Cycle and path support graphs are special cases. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false
universe u

theorem walk_integer_offset {V : Type u} [AddCommGroup V]
    (G : SimpleGraph V) (step : V)
    (hstep : ∀ {x y}, G.Adj x y → y = x + step ∨ y = x - step)
    {x y : V} (p : G.Walk x y) :
    ∃ d : ℤ, y = x + d • step ∧ -(p.length : ℤ) ≤ d ∧ d ≤ (p.length : ℤ) := by
  induction p with
  | nil => exact ⟨0, by simp, by simp, by simp⟩
  | @cons x z y hxz p ih =>
    obtain ⟨d, he, hlo, hhi⟩ := ih
    rcases hstep hxz with hz | hz
    · refine ⟨d + 1, ?_, ?_, ?_⟩
      · rw [he, hz, add_zsmul, one_zsmul]
        abel
      all_goals simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]; omega
    · refine ⟨d - 1, ?_, ?_, ?_⟩
      · rw [he, hz, sub_zsmul, one_zsmul]
        abel
      all_goals simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]; omega

theorem nearVertices_card_le_linear {V : Type u} [Fintype V] [DecidableEq V] [AddCommGroup V]
    (G : SimpleGraph V) (step : V)
    (hstep : ∀ {x y}, G.Adj x y → y = x + step ∨ y = x - step)
    (ell : ℕ) (hell : 1 ≤ ell) (i : V) :
    (nearVertices G ell i).card ≤ 2 * ell - 1 := by
  have hsub : nearVertices G ell i ⊆
      (Finset.Icc (-(ell : ℤ) + 1) ((ell : ℤ) - 1)).image (fun d => i + d • step) := by
    intro j hj
    obtain ⟨p, hp⟩ := (mem_nearVertices G ell i j).mp hj
    obtain ⟨d, he, hlo, hhi⟩ := walk_integer_offset G step hstep p
    apply Finset.mem_image.mpr
    exact ⟨d, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, he.symm⟩
  calc
    _ ≤ ((Finset.Icc (-(ell : ℤ) + 1) ((ell : ℤ) - 1)).image
        (fun d => i + d • step)).card := Finset.card_le_card hsub
    _ ≤ (Finset.Icc (-(ell : ℤ) + 1) ((ell : ℤ) - 1)).card := Finset.card_image_le
    _ = 2 * ell - 1 := by rw [Int.card_Icc]; omega

theorem cycleGraph_step {n : ℕ} [NeZero n] {i j : Fin n}
    (h : (SimpleGraph.cycleGraph n).Adj i j) : j = i + 1 ∨ j = i - 1 := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    cases n with
    | zero => exact False.elim (SimpleGraph.cycleGraph_one_adj h)
    | succ n =>
      rcases SimpleGraph.cycleGraph_adj.mp h with h | h
      · have hi : i = j + 1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h
        exact Or.inr (by rw [hi]; simp)
      · exact Or.inl (by simpa [add_comm] using sub_eq_iff_eq_add.mp h)

theorem nearVertices_card_subcycle {n : ℕ} [NeZero n]
    (G : SimpleGraph (Fin n)) (hG : G ≤ SimpleGraph.cycleGraph n)
    (ell : ℕ) (hell : 1 ≤ ell) (i : Fin n) :
    (nearVertices G ell i).card ≤ 2 * ell - 1 :=
  nearVertices_card_le_linear G (1 : Fin n) (fun h => cycleGraph_step (hG h)) ell hell i

end TransposeFollowup

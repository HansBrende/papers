import SubcubicMemo.RankOneCore

/-! Original square edges and the unique two-step paths touching their
complement. The graph is fixed throughout; no iterative deletion is used. -/

namespace SubcubicMemo

open Finset
open scoped Classical

variable {V : Type*} (G : SimpleGraph V)

/-- A simple four-cycle, with the named edge first. -/
def Square (u v a b : V) : Prop :=
  G.Adj u v ∧ G.Adj v a ∧ G.Adj a b ∧ G.Adj b u ∧ u ≠ a ∧ v ≠ b

namespace Square

theorem rotate {u v a b : V} (h : Square G u v a b) : Square G v a b u := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h2, h3, h4, h1, h6, h5.symm⟩

theorem reverse {u v a b : V} (h : Square G u v a b) : Square G v u b a := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1.symm, h4.symm, h3.symm, h2.symm, h6, h5⟩

end Square

def squareCore : SimpleGraph V where
  Adj u v := ∃ a b, Square G u v a b
  symm := ⟨by rintro u v ⟨a, b, h⟩; exact ⟨b, a, h.reverse G⟩⟩
  loopless := ⟨by rintro v ⟨a, b, h⟩; exact G.irrefl h.1⟩

theorem squareCore_le : squareCore G ≤ G := by
  rintro u v ⟨a, b, h⟩
  exact h.1

theorem square_in_core {u v a b : V} (h : Square G u v a b) :
    Square (squareCore G) u v a b := by
  exact ⟨⟨a, b, h⟩, ⟨b, u, h.rotate G⟩,
    ⟨u, v, (h.rotate G).rotate G⟩,
    ⟨v, a, ((h.rotate G).rotate G).rotate G⟩, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem squareCore_covered {u v : V} (h : (squareCore G).Adj u v) :
    ∃ a b, Square (squareCore G) u v a b := by
  obtain ⟨a, b, h⟩ := h
  exact ⟨a, b, square_in_core G h⟩

def offSquare : SimpleGraph V := G \ squareCore G

/-- Ordered endpoints of a nonbacktracking two-step path containing an
original off-square edge. -/
def touchedPair (a c : V) : Prop :=
  a ≠ c ∧ ∃ b, G.Adj a b ∧ G.Adj b c ∧
    ((offSquare G).Adj a b ∨ (offSquare G).Adj b c)

theorem offSquare_unique_middle {a b c z : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c)
    (hf : (offSquare G).Adj a b ∨ (offSquare G).Adj b c)
    (haz : G.Adj a z) (hzc : G.Adj z c) : z = b := by
  by_contra hzb
  have hs : Square G a b c z :=
    ⟨hab, hbc, hzc.symm, haz.symm, hac, Ne.symm hzb⟩
  rcases hf with hf | hf
  · exact hf.2 ⟨c, z, hs⟩
  · exact hf.2 ⟨z, a, hs.rotate G⟩

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def twoStep (v : V) : Finset V :=
  (G.neighborFinset v).biUnion fun u => (G.neighborFinset u).erase v

theorem mem_twoStep {v w : V} : w ∈ twoStep G v ↔
    w ≠ v ∧ ∃ u, G.Adj v u ∧ G.Adj u w := by
  simp only [twoStep, mem_biUnion, SimpleGraph.mem_neighborFinset, mem_erase]
  aesop

theorem twoStep_card_le_six (hdeg : ∀ v, G.degree v ≤ 3) (v : V) :
    (twoStep G v).card ≤ 6 := by
  calc
    (twoStep G v).card ≤ ∑ u ∈ G.neighborFinset v, ((G.neighborFinset u).erase v).card :=
      card_biUnion_le
    _ ≤ ∑ _u ∈ G.neighborFinset v, 2 := by
      apply sum_le_sum
      intro u hu
      have hm : v ∈ G.neighborFinset u :=
        (G.mem_neighborFinset u v).mpr ((G.mem_neighborFinset v u).mp hu).symm
      rw [card_erase_of_mem hm, G.card_neighborFinset_eq_degree]
      have := hdeg u
      omega
    _ ≤ 6 := by
      simp only [sum_const, smul_eq_mul, G.card_neighborFinset_eq_degree]
      have := hdeg v
      omega

end SubcubicMemo

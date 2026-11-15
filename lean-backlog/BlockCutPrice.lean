import Transpose.Tape.CECount
import Transpose.Tape.CEProfile
import Transpose.Tape.MStarTM

/-! # The exact outgoing-message and cut-output price -/

namespace LeanBacklog.BlockTCC

open Finset Transpose Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem sum_cut_chordTapes {k r L : ℕ} {Dg : TSDiagram k}
    (hDg : Dg.Valid L) (hr : 1 ≤ r) (Γ : Finset ℕ) :
    ∑ e ∈ (Dg.chordEdges r).filter (fun e => e.1 ∈ Γ), Dg.chordTapes r e ≤ k * Γ.card := by
  classical
  let E := (Dg.chordEdges r).filter (fun e => e.1 ∈ Γ)
  have heq : ∑ e ∈ E, Dg.chordTapes r e =
      ∑ t : Fin k, (E.filter (fun e =>
        ∃ β : ℤ, IsChord (pairRes r (Dg.work t) Dg.T) β e.1 e.2)).card := by
    simp only [TSDiagram.chordTapes, card_filter]
    rw [sum_comm]
  rw [show (Dg.chordEdges r).filter (fun e => e.1 ∈ Γ) = E from rfl, heq]
  calc
    _ ≤ ∑ _t : Fin k, Γ.card := by
      apply sum_le_sum
      intro t _
      apply card_le_card_of_injOn (fun e => e.1)
      · intro e he
        exact (mem_filter.mp (mem_filter.mp he).1).2
      · intro e he e' he' hee
        simp only at hee
        obtain ⟨β, hβ⟩ := (mem_filter.mp he).2
        obtain ⟨β', hβ'⟩ := (mem_filter.mp he').2
        rw [← hee] at hβ'
        exact Prod.ext hee (pairRes_chord_source_unique (hDg.1 t).2 hr Dg.T hβ hβ').2
    _ = k * Γ.card := by simp

theorem card_cut_memEdges {k r : ℕ} (Dg : TSDiagram k) (Γ : Finset ℕ) :
    ((Dg.memEdges r).filter (fun e => e.1 ∈ Γ)).card ≤ Γ.card := by
  classical
  apply card_le_card_of_injOn (fun e => e.1)
  · intro e he
    exact (mem_filter.mp he).2
  · intro e he e' he' hee
    simp only at hee
    have h1 := (mem_memEdges Dg).mp (mem_filter.mp he).1
    have h2 := (mem_memEdges Dg).mp (mem_filter.mp he').1
    exact Prod.ext hee (by omega)

/-- A cut slot's outgoing memory and chords cost at most four blocks per
tape in total. No correctness or input distribution is used. -/
theorem cut_edge_price {k d G L : ℕ} {Dg : TSDiagram k}
    (hDg : Dg.Valid L) (hr : 1 ≤ TSDiagram.blockSize G d)
    {cap : ℕ × ℕ → ℕ} (hcap : Dg.CapProfile d G cap) (Γ : Finset ℕ) :
    ∑ e ∈ (Dg.edges (TSDiagram.blockSize G d)).filter (fun e => e.1 ∈ Γ), cap e ≤
      4 * k * (TSDiagram.blockSize G d * G) * Γ.card := by
  classical
  let r := TSDiagram.blockSize G d
  let M := (Dg.memEdges r).filter (fun e => e.1 ∈ Γ)
  let C := (Dg.chordEdges r).filter (fun e => e.1 ∈ Γ)
  have hdisj : Disjoint M C := by
    apply disjoint_left.mpr
    intro e hm hc
    exact not_mem_chordEdges_of_mem_memEdges Dg (mem_filter.mp hm).1 (mem_filter.mp hc).1
  have hsplit : (Dg.edges r).filter (fun e => e.1 ∈ Γ) = M ∪ C := by
    simp only [TSDiagram.edges, filter_union, M, C]
  rw [show TSDiagram.blockSize G d = r from rfl, hsplit, sum_union hdisj]
  have hM : ∑ e ∈ M, cap e ≤ Γ.card * (3 * k * (r * G)) := by
    calc
      _ ≤ ∑ _e ∈ M, 3 * k * (r * G) := by
        apply sum_le_sum
        intro e he
        exact (hcap.1 e (mem_filter.mp he).1).trans
          (Nat.mul_le_mul_right _ (resSum_le hDg hr e.1))
      _ = M.card * (3 * k * (r * G)) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (card_cut_memEdges Dg Γ)
  have hC : ∑ e ∈ C, cap e ≤ k * Γ.card * (r * G) := by
    calc
      _ ≤ ∑ e ∈ C, Dg.chordTapes r e * (r * G) :=
        sum_le_sum fun e he => hcap.2 e (mem_filter.mp he).1
      _ = (∑ e ∈ C, Dg.chordTapes r e) * (r * G) := by rw [sum_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (sum_cut_chordTapes hDg hr Γ)
  nlinarith [hM, hC]

/-- Output positions at one slot form an interval of at most `r` bits. -/
theorem card_slot_outputs {k L r : ℕ} {Dg : TSDiagram k}
    (hDg : Dg.Valid L) (hr : 1 ≤ r) (y : ℕ) :
    (univ.filter (fun o : Fin L => Dg.outNode r o.val = y)).card ≤ r := by
  classical
  calc
    _ ≤ (Ico (Dg.out (y * r)) (Dg.out (y * r) + r)).card := by
      apply card_le_card_of_injOn (fun o : Fin L => o.val)
      · intro o ho
        have hs := outNode_spec hDg hr o.isLt
        rw [(mem_filter.mp ho).2] at hs
        exact mem_Ico.mpr hs
      · intro o _ o' _ he
        exact Fin.ext he
    _ = r := by simp

theorem card_cut_outputs {k L r : ℕ} {Dg : TSDiagram k}
    (hDg : Dg.Valid L) (hr : 1 ≤ r) (Γ : Finset ℕ) :
    (univ.filter (fun o : Fin L => Dg.outNode r o.val ∈ Γ)).card ≤ r * Γ.card := by
  classical
  rw [← sum_card_fiberwise_eq_card_filter (univ : Finset (Fin L)) Γ (fun o => Dg.outNode r o.val)]
  calc
    _ ≤ ∑ _y ∈ Γ, r := sum_le_sum fun y _ => card_slot_outputs hDg hr y
    _ = r * Γ.card := by simp [mul_comm]

#print axioms sum_cut_chordTapes
#print axioms card_cut_memEdges
#print axioms cut_edge_price
#print axioms card_slot_outputs
#print axioms card_cut_outputs

end LeanBacklog.BlockTCC

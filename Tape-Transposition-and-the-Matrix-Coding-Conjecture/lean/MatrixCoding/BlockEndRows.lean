import MatrixCoding.BlockRowGrouping

/-!
# Output-at-end diagrams need no exceptional columns

The first paper already reduces arbitrary adaptive transposers to this
schedule. Each output row meets at most G+1 grain slots, independently of
the time constant and the depth cut.
-/

namespace LeanBacklog.BlockTCC

open Finset Transpose Transpose.Tape Transpose.Tape.Impl

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem outNode_atEnd {k L r : ℕ} {Dg : TSDiagram k}
    (hDg : Dg.Valid L) (hr : 1 ≤ r)
    (hend : ∀ t ≤ Dg.T, Dg.out t = L - (Dg.T - t))
    {o : ℕ} (ho : o < L) : Dg.outNode r o = (Dg.T - L + o) / r := by
  have hLT : L ≤ Dg.T := by
    have h := out_add_le hDg 0 Dg.T
    rw [zero_add, hDg.2.2.2.1, zero_add, hDg.2.2.2.2.2 Dg.T le_rfl] at h
    exact h
  let t := Dg.T - L + o
  let y := t / r
  have htT : t < Dg.T := by dsimp [t]; omega
  have hy0 : y*r ≤ t := Nat.div_mul_le_self _ _
  have hy1 : t < (y+1)*r := by
    have h1 := Nat.div_add_mod t r
    have h2 := Nat.mod_lt t (show 0 < r by omega)
    dsimp [y]
    nlinarith
  apply outNode_eq hDg
  · exact (numSlots_spec hr).2 (hy0.trans_lt htT)
  · rw [hend _ (hy0.trans htT.le)]
    dsimp [t] at hy0
    omega
  · change o < Dg.out ((y+1)*r)
    by_cases hnext : (y+1)*r ≤ Dg.T
    · rw [hend _ hnext]
      dsimp [t] at hy1
      omega
    · rw [hDg.2.2.2.2.2 _ (by omega)]
      exact ho

theorem card_rowSlots_atEnd {k d b r G : ℕ} {Dg : TSDiagram k}
    (hDg : Dg.Valid (d*d*b)) (hr : 1 ≤ r) (hW : 0 < d*b)
    (hrG : d*b ≤ r*G)
    (hend : ∀ t ≤ Dg.T, Dg.out t = d*d*b - (Dg.T - t))
    (j : Fin d) : (rowSlots Dg d b r j).card ≤ G+1 := by
  classical
  let start := Dg.T - d*d*b + j.val*(d*b)
  let q := start / r
  have hsub : rowSlots Dg d b r j ⊆ Icc q (q+G) := by
    intro y hy
    obtain ⟨o, ho, hnode⟩ := (mem_filter.mp (mem_filter.mp hy).2).2
    have hlow : j.val*(d*b) ≤ o.val := by
      simpa only [ho] using Nat.div_mul_le_self o.val (d*b)
    have hhigh : o.val < j.val*(d*b) + d*b := by
      have h1 := Nat.div_add_mod o.val (d*b)
      have h2 := Nat.mod_lt o.val hW
      rw [ho] at h1
      nlinarith
    rw [← hnode, outNode_atEnd hDg hr hend o.isLt]
    apply mem_Icc.mpr
    constructor
    · exact Nat.div_le_div_right (show start ≤ Dg.T-d*d*b+o.val by dsimp [start]; omega)
    · calc
        (Dg.T-d*d*b+o.val)/r ≤ (start+G*r)/r := Nat.div_le_div_right (by
          dsimp [start]; nlinarith)
        _ = q+G := by rw [Nat.mul_comm G r, Nat.add_mul_div_left _ _ (by omega)]
  exact (card_le_card hsub).trans (by simp; omega)

theorem badOutputRows_atEnd_eq_empty {k d b r G : ℕ} {Dg : TSDiagram k}
    (hDg : Dg.Valid (d*d*b)) (hr : 1 ≤ r) (hW : 0 < d*b)
    (hrG : d*b ≤ r*G)
    (hend : ∀ t ≤ Dg.T, Dg.out t = d*d*b - (Dg.T - t)) :
    badOutputRows Dg d b r (G+1) = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro j hj
  exact (not_lt_of_ge (card_rowSlots_atEnd hDg hr hW hrG hend j)) (mem_filter.mp hj).2

#print axioms outNode_atEnd
#print axioms card_rowSlots_atEnd
#print axioms badOutputRows_atEnd_eq_empty

end LeanBacklog.BlockTCC

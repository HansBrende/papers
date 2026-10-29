import SourceCovers.SerialNonleaves

set_option autoImplicit false

/-! Original component ranks, computed before deletion. The proof uses
the existing consecutive-rank theorem instead of recounting predecessors. -/

namespace SourceCovers.SerialGeometry.Parameters

open Classical Finset BoundedNesting LeanMachine
noncomputable section

variable (P : Parameters)

theorem bankCore_rank_base (c : Fin 2) {j : Fin P.bankCount} (hj : j.val ≤ 1) :
    (coreModel P.coreFamilies).spineRank (P.bankCore c j) = 1 := by
  have he : (coreModel P.coreFamilies).predecessors (P.bankCore c j) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro F hF
    simp only [ThinIntervals.Model.predecessors, mem_filter, mem_univ, true_and] at hF
    obtain ⟨hn, hr, hl⟩ := hF
    obtain ⟨c', i, rfl, hi, _⟩ := P.core_nonleaf_cases hn
    have hc := P.bankCore_same_copy_of_reachable hr
    subst c'
    change (P.bankFamily c i).start < (P.bankFamily c j).start at hl
    rw [bankFamily_start, bankFamily_start] at hl
    have hij : i.val < j.val :=
      (Nat.mul_lt_mul_right P.width_pos).mp (Nat.lt_of_add_lt_add_left hl)
    omega
  simp only [ThinIntervals.Model.spineRank, he, card_empty, zero_add]

/-- This also covers the rightmost leaf of the late path. Its generic
rank need not equal the adjacent-leaf convention in the written example;
original leaves are excluded from periodic deletion. -/
theorem bankCore_rank_of_pos (c : Fin 2) (j : Fin P.bankCount) (hj : 0 < j.val) :
    (coreModel P.coreFamilies).spineRank (P.bankCore c j) = j.val := by
  have h : ∀ a, ∀ ha : a < P.bankCount, 0 < a →
      (coreModel P.coreFamilies).spineRank (P.bankCore c ⟨a, ha⟩) = a := by
    intro a
    induction a with
    | zero => intro ha hpos; omega
    | succ a ih =>
      intro ha _
      by_cases hz : a = 0
      · subst a
        exact P.bankCore_rank_base c (by simp)
      · let i : Fin P.bankCount := ⟨a, by omega⟩
        let j : Fin P.bankCount := ⟨a + 1, ha⟩
        have hi : 0 < a := by omega
        have hn : (coreModel P.coreFamilies).Nonleaf (P.bankCore c i) :=
          (P.bankCore_nonleaf_iff c i).mpr ⟨hi, Or.inl ha⟩
        have he : (coreModel P.coreFamilies).graph.Adj (P.bankCore c i) (P.bankCore c j) :=
          (P.bankCore_adj_iff c c i j).mpr ⟨rfl, Or.inl rfl⟩
        have hl : (coreModel P.coreFamilies).left (P.bankCore c i) <
            (coreModel P.coreFamilies).left (P.bankCore c j) := by
          change (P.bankFamily c i).start < (P.bankFamily c j).start
          rw [bankFamily_start, bankFamily_start]
          exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right (by dsimp [i, j]; omega) P.width_pos) _
        have hs := ThinIntervals.Model.spineRank_step (core_thin P.core_span_coloring) hn he hl
        have hr : (coreModel P.coreFamilies).spineRank (P.bankCore c i) = a := ih i.isLt hi
        simpa only [hr] using hs
  exact h j.val j.isLt hj

theorem bankCore_phase_of_pos (c : Fin 2) (j : Fin P.bankCount) (hj : 0 < j.val) :
    corePhase P.coreFamilies P.m (P.bankCore c j) = j.val % P.m := by
  unfold corePhase
  rw [P.bankCore_rank_of_pos c j hj]

end
end SourceCovers.SerialGeometry.Parameters

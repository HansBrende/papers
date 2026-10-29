import SourceCovers.SerialHops

set_option autoImplicit false

/-! Adjacent bank reflections in the two serial continuations. Every
witness is a complete family retained by the original residue-zero phase. -/

namespace SourceCovers.SerialGeometry.Parameters

open Classical Finset BoundedNesting
noncomputable section

variable (P : Parameters)

theorem bankFamily_retained (c : Fin 2) (j : Fin P.bankCount)
    (hj : j.val = 0 ∨ j.val % P.m ≠ 0) : P.bankFamily c j ∈ P.retainedCore :=
  (P.mem_retainedCore _).mpr (Or.inl ⟨c, j, rfl, hj⟩)

theorem late_bank_step (k k' : Fin (P.m - 1)) (hk : k'.val = k.val + 1) :
    ∃ j : Fin P.bankCount, P.bankFamily 1 j ∈ P.retainedCore ∧
      (Fin.castAdd 4 (P.bankHeadIndex 1 j), P.lateTime k', P.lateTime k) ∈
        (P.bankFamily 1 j).hops := by
  let j : Fin P.bankCount := ⟨P.lateWindow k', P.lateWindow_lt k'⟩
  have hw : P.lateWindow k' + 1 = P.lateWindow k := by
    have hk' := k'.isLt
    rw [P.lateWindow_eq, P.lateWindow_eq]
    omega
  refine ⟨j, P.bankFamily_retained 1 j (Or.inr ?_), ?_⟩
  · change P.lateWindow k' % P.m ≠ 0
    rw [P.lateWindow_mod]
    exact (P.laneHeight_bounds k').1.ne'
  · have hh := P.bank_reflection_hop 1 j P.width_half_pos P.width_half_lt.le
    have he : P.width - P.width / 2 = P.width / 2 := by
      have := P.width_half_twice
      omega
    simpa only [j, bankBase, Fin.val_one, show ¬(1 : ℕ) = 0 by omega,
      ite_false, hw, he, lateTime] using hh

theorem bridge_exit_bank_step (k : Fin (P.m - 1)) :
    ∃ j : Fin P.bankCount, P.bankFamily 0 j ∈ P.retainedCore ∧
      (Fin.castAdd 4 (P.bankHeadIndex 0 j), P.olderTime (k, 0), P.bridgeExit k) ∈
        (P.bankFamily 0 j).hops := by
  have hn := P.bankCount_ge
  let j : Fin P.bankCount := ⟨P.bankCount - 1, by omega⟩
  have hj : j.val + 1 = P.bankCount := by dsimp only [j]; omega
  have ha := P.laneHeight_bounds k
  have hah : P.laneHeight k < P.width := ha.2.trans P.m_lt_width
  refine ⟨j, P.bankFamily_retained 0 j (Or.inr ?_), ?_⟩
  · intro hzero
    have := P.bank_zero_residue_interior hzero
    omega
  · have hh := P.bank_reflection_hop 0 j ha.1 hah.le
    have ho : P.olderOffset (k, 0) = P.width - P.laneHeight k := by
      simp [olderOffset, laneHeight]
    have hw : P.olderWindow (k, 0) = j.val := rfl
    have ht : P.bankBase 0 + (j.val + 1) * P.width + P.laneHeight k =
        P.bridgeExit k := by
      change 4 * P.length + (j.val + 1) * P.width + P.laneHeight k = _
      rw [hj]
      change 4 * P.length + P.length + P.laneHeight k = _
      dsimp only [bridgeExit]
      omega
    have hu : P.bankBase 0 + j.val * P.width + (P.width - P.laneHeight k) =
        P.olderTime (k, 0) := by
      change 4 * P.length + j.val * P.width + (P.width - P.laneHeight k) = _
      simp only [olderTime, hw, ho]
    rwa [hu, ht] at hh

theorem olderOffset_step (k l l' : Fin (P.m - 1)) (hl : l'.val = l.val + 1) :
    P.olderOffset (k, l') = P.width - P.olderOffset (k, l) := by
  have hk := k.isLt
  have hw := P.m_lt_width
  dsimp only [olderOffset]
  split_ifs <;> omega

theorem older_bank_step (k l l' : Fin (P.m - 1)) (hl : l'.val = l.val + 1) :
    ∃ j : Fin P.bankCount, P.bankFamily 0 j ∈ P.retainedCore ∧
      (Fin.castAdd 4 (P.bankHeadIndex 0 j), P.olderTime (k, l'), P.olderTime (k, l)) ∈
        (P.bankFamily 0 j).hops := by
  have hw := P.olderWindow_add (k, l)
  have hw' := P.olderWindow_add (k, l')
  dsimp only at hw hw'
  let j : Fin P.bankCount := ⟨P.olderWindow (k, l'), by omega⟩
  have hj : j.val + 1 = P.olderWindow (k, l) := by dsimp only [j]; omega
  refine ⟨j, P.bankFamily_retained 0 j (Or.inr ?_), ?_⟩
  · change P.olderWindow (k, l') % P.m ≠ 0
    rw [P.olderWindow_mod]
    exact (P.laneHeight_bounds l').1.ne'
  · have ha := P.olderOffset_bounds (k, l)
    have hh := P.bank_reflection_hop 0 j ha.1 ha.2.le
    have hu : P.bankBase 0 + j.val * P.width + (P.width - P.olderOffset (k, l)) =
        P.olderTime (k, l') := by
      change 4 * P.length + P.olderWindow (k, l') * P.width +
        (P.width - P.olderOffset (k, l)) = _
      rw [← P.olderOffset_step k l l' hl]
      rfl
    have ht : P.bankBase 0 + (j.val + 1) * P.width + P.olderOffset (k, l) =
        P.olderTime (k, l) := by
      rw [hj]
      rfl
    rwa [hu, ht] at hh

end
end SourceCovers.SerialGeometry.Parameters

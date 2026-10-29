import SourceCovers.SerialReachability

set_option autoImplicit false

/-! A retained bank can change a displayed point only by the next listed
reflection. At either end of a chain that next family has been deleted. -/

namespace SourceCovers.SerialGeometry.Parameters

open Classical Finset BoundedNesting
noncomputable section

variable (P : Parameters)

theorem bank_extended_copy_unique (c c' : Fin 2) {t : ℕ}
    (hc : P.bankBase c < t ∧ t ≤ P.bankBase c + P.length + P.width)
    (hc' : P.bankBase c' < t ∧ t ≤ P.bankBase c' + P.length + P.width) : c = c' := by
  have hw := P.width_lt_length
  fin_cases c <;> fin_cases c' <;> simp [bankBase] at hc hc' ⊢ <;> omega

theorem bank_active_window (c c' : Fin 2) (j : Fin P.bankCount) {w a : ℕ}
    (hw : w ≤ P.bankCount) (ha : 0 < a) (hah : a < P.width)
    (hactive : (P.bankFamily c j).shadow (P.bankBase c' + w * P.width + a) ≠
      P.bankBase c' + w * P.width + a) : c = c' ∧ j.val + 1 = w := by
  have hact := ((P.bankFamily c j).shadow_ne_self_iff _).mp hactive
  rw [P.bankFamily_owner, P.bankFamily_stop] at hact
  have hmul := Nat.mul_le_mul_right P.width hw
  change w * P.width ≤ P.length at hmul
  have hcopy : c = c' := by
    apply P.bank_extended_copy_unique c c' (t := P.bankBase c' + w * P.width + a)
    · have hb := P.bankFamily_span_bounds c j
      rw [P.bankFamily_stop] at hb
      have hl : P.bankBase c < P.bankBase c + (j.val + 1) * P.width := by
        have := P.width_pos
        nlinarith
      constructor
      · omega
      · omega
    · constructor
      · have := Nat.zero_le (w * P.width)
        omega
      · omega
  subst c'
  refine ⟨rfl, ?_⟩
  by_contra hne
  have hcases : j.val + 2 ≤ w ∨ w ≤ j.val := by omega
  rcases hcases with h | h
  · have := Nat.mul_le_mul_right P.width h
    omega
  · have := Nat.mul_le_mul_right P.width h
    have he : (j.val + 1) * P.width = j.val * P.width + P.width := by ring
    omega

theorem bank_shadow_fixed_away (c : Fin 2) (j : Fin P.bankCount) {t : ℕ}
    (ht : t ≤ 3 * P.length ∨ (6 * P.length ≤ t ∧ t ≤ 11 * P.length)) :
    (P.bankFamily c j).shadow t = t := by
  by_contra h
  have ha := ((P.bankFamily c j).shadow_ne_self_iff t).mp h
  rw [P.bankFamily_owner, P.bankFamily_stop] at ha
  have hb := P.bankFamily_span_bounds c j
  rw [P.bankFamily_stop] at hb
  have hw := P.width_lt_length
  fin_cases c <;> simp [bankBase] at ha hb <;> omega

theorem late_shadow_step (c : Fin 2) (j : Fin P.bankCount)
    (hj : P.bankFamily c j ∈ P.retainedCore) (k : Fin (P.m - 1)) :
    ∃ k' : Fin (P.m - 1), (P.bankFamily c j).shadow (P.lateTime k) = P.lateTime k' := by
  by_cases h : (P.bankFamily c j).shadow (P.lateTime k) = P.lateTime k
  · exact ⟨k, h⟩
  have hc := P.bank_active_window c 1 j (P.lateWindow_lt k).le
    P.width_half_pos P.width_half_lt h
  obtain ⟨rfl, hw⟩ := hc
  have hret : j.val = 0 ∨ j.val % P.m ≠ 0 := by
    have : P.bankCore 1 j ∈ P.serialPhase := by
      obtain ⟨F, hF, he⟩ := mem_image.mp hj
      have he' : F = P.bankCore 1 j := Subtype.ext he
      exact he' ▸ hF
    exact (P.bankCore_survives_iff 1 j).mp this
  have hk : k.val + 1 < P.m - 1 := by
    have hb := k.isLt
    have hm := P.hm
    have he := P.lateWindow_eq k
    by_contra hn
    have hjv : j.val = 3 * P.m := by omega
    rcases hret with hz | hnz
    · omega
    · exact hnz (by rw [hjv]; simp)
  let k' : Fin (P.m - 1) := ⟨k.val + 1, hk⟩
  refine ⟨k', ?_⟩
  have hw' : j.val = P.lateWindow k' := by
    have h₁ := P.lateWindow_eq k
    have h₂ := P.lateWindow_eq k'
    have hkv : k'.val = k.val + 1 := rfl
    have hb := k'.isLt
    omega
  have hh := P.bank_reflection_shadow 1 j P.width_half_pos P.width_half_lt
  have he : P.width - P.width / 2 = P.width / 2 := by
    have := P.width_half_twice
    omega
  change (P.bankFamily 1 j).shadow
    (11 * P.length + (j.val + 1) * P.width + P.width / 2) =
      11 * P.length + j.val * P.width + (P.width - P.width / 2) at hh
  rw [hw, hw', he] at hh
  exact hh

theorem bridgeExit_shadow_step (c : Fin 2) (j : Fin P.bankCount)
    (k : Fin (P.m - 1)) :
    (P.bankFamily c j).shadow (P.bridgeExit k) = P.bridgeExit k ∨
      (P.bankFamily c j).shadow (P.bridgeExit k) = P.olderTime (k, 0) := by
  by_cases h : (P.bankFamily c j).shadow (P.bridgeExit k) = P.bridgeExit k
  · exact Or.inl h
  right
  have ht : P.bridgeExit k = P.bankBase 0 + P.bankCount * P.width + P.laneHeight k := by
    change 5 * P.length + P.laneHeight k = 4 * P.length + P.length + P.laneHeight k
    omega
  rw [ht] at h
  have hc := P.bank_active_window c 0 j le_rfl (P.laneHeight_bounds k).1
    ((P.laneHeight_bounds k).2.trans P.m_lt_width) h
  obtain ⟨rfl, hj⟩ := hc
  have hh := P.bank_reflection_shadow 0 j (P.laneHeight_bounds k).1
    ((P.laneHeight_bounds k).2.trans P.m_lt_width)
  rw [hj, ← ht] at hh
  have hj' : j.val = P.olderWindow (k, 0) := by
    have hw := P.olderWindow_add (k, 0)
    change P.olderWindow (k, 0) + 1 = P.bankCount at hw
    omega
  rw [hh]
  change 4 * P.length + j.val * P.width + (P.width - P.laneHeight k) = _
  simp [olderTime, olderOffset, laneHeight, hj']

theorem older_shadow_step (c : Fin 2) (j : Fin P.bankCount)
    (hj : P.bankFamily c j ∈ P.retainedCore) (i : P.GridIndex) :
    ∃ i' : P.GridIndex, (P.bankFamily c j).shadow (P.olderTime i) = P.olderTime i' := by
  by_cases h : (P.bankFamily c j).shadow (P.olderTime i) = P.olderTime i
  · exact ⟨i, h⟩
  have hw := P.olderWindow_add i
  have hc := P.bank_active_window c 0 j (show P.olderWindow i ≤ P.bankCount by omega)
    (P.olderOffset_bounds i).1 (P.olderOffset_bounds i).2 h
  obtain ⟨rfl, hjw⟩ := hc
  have hret : j.val = 0 ∨ j.val % P.m ≠ 0 := by
    obtain ⟨F, hF, he⟩ := mem_image.mp hj
    have he' : F = P.bankCore 0 j := Subtype.ext he
    exact (P.bankCore_survives_iff 0 j).mp (he' ▸ hF)
  have hi : i.2.val + 1 < P.m - 1 := by
    have hb := i.2.isLt
    have hm := P.hm
    by_contra hn
    have hjv : j.val = 7 * P.m := by unfold bankCount at hw; omega
    rcases hret with hz | hnz
    · omega
    · exact hnz (by rw [hjv]; simp)
  let l' : Fin (P.m - 1) := ⟨i.2.val + 1, hi⟩
  refine ⟨(i.1, l'), ?_⟩
  have hw' := P.olderWindow_add (i.1, l')
  have hnew : j.val = P.olderWindow (i.1, l') := by
    change P.olderWindow (i.1, l') + (l'.val + 1) = P.bankCount at hw'
    have hl : l'.val = i.2.val + 1 := rfl
    omega
  have hh := P.bank_reflection_shadow 0 j (P.olderOffset_bounds i).1 (P.olderOffset_bounds i).2
  rw [hjw] at hh
  change (P.bankFamily 0 j).shadow (P.olderTime i) =
    4 * P.length + j.val * P.width + (P.width - P.olderOffset i) at hh
  rw [hh, hnew, ← P.olderOffset_step i.1 i.2 l' rfl]
  rfl

end
end SourceCovers.SerialGeometry.Parameters

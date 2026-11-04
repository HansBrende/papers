import BoundedStackDepth.FrameSystem

/-!
# One-step dynamics of a frame system

How the segment start and the running maximum of a frame `F` change from `t − 1` to `t`
(`F.1 < t`):
* at a *restart* of `F` (a restart point that is an own time of `F`) the segment starts afresh:
  `segStart_of_restart`, `runMax_of_restart` (and at the start of `F`: `runMax_start`);
* otherwise the segment continues (`segStart_succ`), and the running maximum
  - stays put if `t` is not an own time of `F` (`runMax_succ_of_not_own`; this is how a suspended
    frame keeps its maximum frozen, `runMax_frozen`),
  - takes the maximum with the new distance if `t` is an own time (`runMax_succ_of_own`; this covers
    the resumption time at a pop).
-/

namespace BoundedStackDepth

namespace FrameSystem

open Finset

variable {S : FrameSystem} {F : ℕ × ℕ} {t : ℕ}

/-- `t` is a restart of `F`: a restart point that is an own time of `F`, after its start. -/
def Restart (S : FrameSystem) (F : ℕ × ℕ) (t : ℕ) : Prop := t ∈ S.R ∧ F.1 < t ∧ S.Own F t

instance (S : FrameSystem) (F : ℕ × ℕ) (t : ℕ) : Decidable (S.Restart F t) := by
  unfold Restart; infer_instance

/-- At a restart, the segment starts afresh. -/
theorem segStart_of_restart (h : S.Restart F t) : S.segStart F t = t :=
  segStart_eq (Or.inr h) le_rfl fun _ _ h1 h2 => absurd h2 (not_le.mpr h1)

/-- At the start of the frame, the segment starts there. -/
theorem segStart_start (S : FrameSystem) (F : ℕ × ℕ) : S.segStart F F.1 = F.1 :=
  segStart_eq (Or.inl rfl) le_rfl fun _ _ h1 h2 => absurd h2 (not_le.mpr h1)

/-- Without a restart at `t`, the segment of `t − 1` continues. -/
theorem segStart_succ (ht : F.1 < t) (h : ¬ S.Restart F t) :
    S.segStart F t = S.segStart F (t - 1) := by
  refine segStart_eq ?_ ((segStart_le (by omega)).trans (Nat.sub_le t 1)) fun s' hs' h1 h2 hown => ?_
  · rcases segStart_mem (S := S) F (t - 1) with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h'.1, h'.2.1, h'.2.2.2⟩
  · rcases eq_or_lt_of_le h2 with he | hlt
    · rw [he] at hs' h1 hown
      exact h ⟨hs', lt_of_le_of_lt (start_le_segStart F (t - 1)) h1, hown⟩
    · exact not_restart_of_segStart_lt h1 (by omega) hs' hown

/-- The running maximum is `0` right after a restart. -/
theorem runMax_of_restart (h : S.Restart F t) : S.runMax F t = 0 := by
  refine Nat.eq_zero_of_le_zero (runMax_le fun t' _ h1 h2 => ?_)
  rw [segStart_of_restart h] at h1 ⊢
  rw [show t' = t by omega, sub_self, Int.natAbs_zero]

/-- The running maximum is `0` at the start of the frame. -/
theorem runMax_start (S : FrameSystem) (F : ℕ × ℕ) : S.runMax F F.1 = 0 := by
  refine Nat.eq_zero_of_le_zero (runMax_le fun t' _ h1 h2 => ?_)
  rw [segStart_start] at h1 ⊢
  rw [show t' = F.1 by omega, sub_self, Int.natAbs_zero]

/-- The own times of `F` in the segment up to `t`. -/
private theorem ownSeg_succ (ht : F.1 < t) (h : ¬ S.Restart F t) :
    (Icc (S.segStart F t) t).filter (S.Own F) =
      if S.Own F t then insert t ((Icc (S.segStart F (t - 1)) (t - 1)).filter (S.Own F))
      else (Icc (S.segStart F (t - 1)) (t - 1)).filter (S.Own F) := by
  have hs := segStart_succ ht h
  have hle : S.segStart F (t - 1) ≤ t - 1 := segStart_le (by omega)
  ext t'
  rw [hs]
  split_ifs with hown
  · simp only [mem_filter, mem_Icc, mem_insert]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases eq_or_lt_of_le h2 with he | hlt
      · exact Or.inl he
      · exact Or.inr ⟨⟨h1, by omega⟩, h3⟩
    · rintro (he | ⟨⟨h1, h2⟩, h3⟩)
      · subst he; exact ⟨⟨by omega, le_rfl⟩, hown⟩
      · exact ⟨⟨h1, by omega⟩, h3⟩
  · simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases eq_or_lt_of_le h2 with he | hlt
      · subst he; exact absurd h3 hown
      · exact ⟨⟨h1, by omega⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, by omega⟩, h3⟩

/-- **A suspended frame keeps its maximum.** If `t` is not an own time of `F`, the running maximum does
not change. -/
theorem runMax_succ_of_not_own (ht : F.1 < t) (hown : ¬ S.Own F t) :
    S.runMax F t = S.runMax F (t - 1) := by
  have hr : ¬ S.Restart F t := fun h => hown h.2.2
  unfold runMax
  rw [ownSeg_succ ht hr, segStart_succ ht hr]
  simp only [hown, ↓reduceIte]

/-- **The running maximum at an own time** without a restart: the maximum with the new distance. -/
theorem runMax_succ_of_own (ht : F.1 < t) (hown : S.Own F t) (hr : ¬ S.Restart F t) :
    S.runMax F t = max (S.runMax F (t - 1)) (S.x t - S.x (S.segStart F t)).natAbs := by
  unfold runMax
  rw [ownSeg_succ ht hr]
  simp only [hown, ↓reduceIte]
  rw [sup_insert, segStart_succ ht hr, max_comm]

/-- **Frozen maxima.** If `F` has no own time in `(t₀, t]`, its running maximum at `t` is that at `t₀`. -/
theorem runMax_frozen {t₀ : ℕ} (h0 : F.1 ≤ t₀) (hno : ∀ s, t₀ < s → s ≤ t → ¬ S.Own F s) (ht : t₀ ≤ t) :
    S.runMax F t = S.runMax F t₀ := by
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    rw [show S.runMax F (t + 1) = S.runMax F (t + 1 - 1) from
      runMax_succ_of_not_own (by omega) (hno _ (by omega) le_rfl)]
    exact ih fun s h1 h2 => hno s h1 (by omega)

/-- The running maximum never decreases without a restart. -/
theorem runMax_le_succ (ht : F.1 < t) (hr : ¬ S.Restart F t) :
    S.runMax F (t - 1) ≤ S.runMax F t := by
  by_cases hown : S.Own F t
  · rw [runMax_succ_of_own ht hown hr]; exact le_max_left _ _
  · rw [runMax_succ_of_not_own ht hown]

end FrameSystem

end BoundedStackDepth

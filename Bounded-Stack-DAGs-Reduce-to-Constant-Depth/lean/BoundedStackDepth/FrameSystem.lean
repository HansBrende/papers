import BoundedStackDepth.BandSums

/-!
# Frame systems: frames, own times, segments and bands

A *frame system* on `[0, T)` is a laminar family of intervals `[a, b)` (the *frames*) containing the root
`[0, T)`, together with a set `R` of *restart points* and a walk `x`. It abstracts the frame structure of
Theorem A (and is instantiated there by the suspend frames of one class).

* The *own times* of a frame are the times of which it is the innermost frame (`Own`); every time `t < T`
  has exactly one innermost frame (`exists_own`, `Own.unique`, `inner`).
* The *current segment* of a frame `F` at time `t` starts at the last restart point of `F` at or before `t`
  (`segStart`): the start of `F`, or a point of `R` that is an own time of `F`. Its *home* is `x` there.
* The *running maximum* of `F` at `t` (`runMax`) is the largest `|x − home|` over the own times of `F` in
  the current segment up to `t`. Only own times count: a suspended child does not move its parent's running
  maximum, and the parent resumes its own maximum when the child ends (the hybrid convention).
* The *band* at `t` (`beta`) is `band` of the running maximum of the innermost frame.

These are exactly the definitions of the reference implementation used in the exhaustive checks (a sweep
that pops, pushes and restarts the innermost frame).
-/

namespace BoundedStackDepth

open Finset

/-- A frame system on `[0, T)`: a laminar family of intervals `[a, b) ⊆ [0, T)` containing the root
`[0, T)`, a set of restart points and a walk. Empty frames are allowed; they contain no time. -/
structure FrameSystem where
  /-- The horizon. -/
  T : ℕ
  /-- The walk. -/
  x : ℕ → ℤ
  /-- The frames, as intervals `[F.1, F.2)`. -/
  frames : Finset (ℕ × ℕ)
  /-- The restart points. -/
  R : Finset ℕ
  root_mem : (0, T) ∈ frames
  bounds : ∀ F ∈ frames, F.2 ≤ T
  laminar : ∀ F ∈ frames, ∀ G ∈ frames,
    (G.1 ≤ F.1 ∧ F.2 ≤ G.2) ∨ (F.1 ≤ G.1 ∧ G.2 ≤ F.2) ∨ F.2 ≤ G.1 ∨ G.2 ≤ F.1

namespace FrameSystem

/-- The interval `F` contains the time `t`. -/
def Contains (F : ℕ × ℕ) (t : ℕ) : Prop := F.1 ≤ t ∧ t < F.2

/-- The interval `F` lies inside the interval `G`. -/
def Within (F G : ℕ × ℕ) : Prop := G.1 ≤ F.1 ∧ F.2 ≤ G.2

instance (F : ℕ × ℕ) (t : ℕ) : Decidable (Contains F t) := by unfold Contains; infer_instance

instance (F G : ℕ × ℕ) : Decidable (Within F G) := by unfold Within; infer_instance

variable (S : FrameSystem)

/-- `t` is an *own time* of `F`: `F` is a frame containing `t` and lies inside every frame containing `t`. -/
def Own (F : ℕ × ℕ) (t : ℕ) : Prop :=
  F ∈ S.frames ∧ Contains F t ∧ ∀ G ∈ S.frames, Contains G t → Within F G

instance (F : ℕ × ℕ) (t : ℕ) : Decidable (S.Own F t) := by unfold Own; infer_instance

variable {S}

/-- Two frames containing a common time are nested. -/
theorem nested_of_contains {F G : ℕ × ℕ} (hF : F ∈ S.frames) (hG : G ∈ S.frames) {t : ℕ}
    (hFt : Contains F t) (hGt : Contains G t) : Within F G ∨ Within G F := by
  rcases S.laminar F hF G hG with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (lt_of_lt_of_le hFt.2 h) (not_lt.mpr hGt.1)
  · exact absurd (lt_of_lt_of_le hGt.2 h) (not_lt.mpr hFt.1)

/-- Every time before `T` has an innermost frame: a shortest frame containing it. -/
theorem exists_own {t : ℕ} (ht : t < S.T) : ∃ F, S.Own F t := by
  classical
  have hne : (S.frames.filter (Contains · t)).Nonempty :=
    ⟨(0, S.T), mem_filter.mpr ⟨S.root_mem, Nat.zero_le _, ht⟩⟩
  obtain ⟨F, hF, hmin⟩ := exists_min_image _ (fun F : ℕ × ℕ => F.2 - F.1) hne
  obtain ⟨hFm, hFt⟩ := mem_filter.mp hF
  refine ⟨F, hFm, hFt, fun G hG hGt => ?_⟩
  rcases nested_of_contains hFm hG hFt hGt with h | h
  · exact h
  · have hle := hmin G (mem_filter.mpr ⟨hG, hGt⟩)
    unfold Contains at hFt hGt
    exact ⟨by unfold Within at h; omega, by unfold Within at h; omega⟩

/-- The innermost frame of a time is unique. -/
theorem Own.unique {F G : ℕ × ℕ} {t : ℕ} (hF : S.Own F t) (hG : S.Own G t) : F = G := by
  have h1 := hF.2.2 G hG.1 hG.2.1
  have h2 := hG.2.2 F hF.1 hF.2.1
  unfold Within at h1 h2
  exact Prod.ext (by omega) (by omega)

variable (S)

/-- The innermost frame of `t` (the root after the horizon). -/
noncomputable def inner (t : ℕ) : ℕ × ℕ :=
  if h : t < S.T then Classical.choose (S.exists_own h) else (0, S.T)

/-- The start of the current segment of `F` at `t`: the last restart point of `F` at or before `t`. The
start of `F` always counts; a point of `R` counts if it is an own time of `F`. -/
noncomputable def segStart (F : ℕ × ℕ) (t : ℕ) : ℕ :=
  (insert F.1 (S.R.filter (fun s => F.1 < s ∧ s ≤ t ∧ S.Own F s))).max' (insert_nonempty _ _)

/-- The running maximum of `F` at `t`: the largest `|x − home|` over the own times of `F` in its
current segment up to `t`. -/
noncomputable def runMax (F : ℕ × ℕ) (t : ℕ) : ℕ :=
  ((Icc (S.segStart F t) t).filter (S.Own F)).sup (fun t' => (S.x t' - S.x (S.segStart F t)).natAbs)

/-- The home of `t`: the value of the walk at the start of the current segment of its innermost frame. -/
noncomputable def home (t : ℕ) : ℤ := S.x (S.segStart (S.inner t) t)

/-- **The band** at `t`: the band of the running maximum of its innermost frame. -/
noncomputable def beta (t : ℕ) : ℕ := band (S.runMax (S.inner t) t)

variable {S}

theorem own_inner {t : ℕ} (ht : t < S.T) : S.Own (S.inner t) t := by
  unfold inner
  simp only [ht, ↓reduceDIte]
  exact Classical.choose_spec (S.exists_own ht)

theorem inner_eq {F : ℕ × ℕ} {t : ℕ} (h : S.Own F t) : S.inner t = F := by
  have ht : t < S.T := lt_of_lt_of_le h.2.1.2 (S.bounds F h.1)
  exact (own_inner ht).unique h

/-! ### Segment starts -/

theorem start_le_segStart (F : ℕ × ℕ) (t : ℕ) : F.1 ≤ S.segStart F t :=
  le_max' _ _ (mem_insert_self _ _)

theorem segStart_mem (F : ℕ × ℕ) (t : ℕ) :
    S.segStart F t = F.1 ∨ (S.segStart F t ∈ S.R ∧ F.1 < S.segStart F t ∧ S.segStart F t ≤ t ∧
      S.Own F (S.segStart F t)) := by
  have h := max'_mem (insert F.1 (S.R.filter (fun s => F.1 < s ∧ s ≤ t ∧ S.Own F s)))
    (insert_nonempty _ _)
  rcases mem_insert.mp h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨(mem_filter.mp h).1, (mem_filter.mp h).2⟩

theorem segStart_le {F : ℕ × ℕ} {t : ℕ} (ht : F.1 ≤ t) : S.segStart F t ≤ t := by
  rcases segStart_mem (S := S) F t with h | h
  · rw [h]; exact ht
  · exact h.2.2.1

/-- No restart point of `F` lies strictly after the segment start, up to `t`. -/
theorem not_restart_of_segStart_lt {F : ℕ × ℕ} {t s : ℕ} (hs : S.segStart F t < s) (hst : s ≤ t)
    (hR : s ∈ S.R) (hown : S.Own F s) : False := by
  have : s ≤ S.segStart F t :=
    le_max' _ _ (mem_insert_of_mem (mem_filter.mpr
      ⟨hR, lt_of_le_of_lt (start_le_segStart F t) hs, hst, hown⟩))
  omega

/-- **Characterization of the segment start.** If `s` is the start of `F` or a restart point that is an
own time of `F`, `s ≤ t`, and no restart point of `F` lies in `(s, t]`, then the segment of `F` at `t`
starts at `s`. -/
theorem segStart_eq {F : ℕ × ℕ} {t s : ℕ} (hs : s = F.1 ∨ (s ∈ S.R ∧ F.1 < s ∧ S.Own F s))
    (hst : s ≤ t) (hno : ∀ s' ∈ S.R, s < s' → s' ≤ t → ¬ S.Own F s') : S.segStart F t = s := by
  refine le_antisymm ?_ ?_
  · rcases segStart_mem (S := S) F t with h | h
    · rw [h]
      rcases hs with hs | hs
      · exact hs.ge
      · exact hs.2.1.le
    · by_contra hlt
      push Not at hlt
      exact hno _ h.1 hlt h.2.2.1 h.2.2.2
  · rcases hs with hs | hs
    · rw [hs]; exact start_le_segStart F t
    · exact le_max' _ _ (mem_insert_of_mem (mem_filter.mpr ⟨hs.1, hs.2.1, hst, hs.2.2⟩))

/-! ### Running maxima -/

/-- An own time of `F` in the current segment up to `t` is within the running maximum of its home. -/
theorem le_runMax {F : ℕ × ℕ} {t t' : ℕ} (hown : S.Own F t') (h1 : S.segStart F t ≤ t')
    (h2 : t' ≤ t) : (S.x t' - S.x (S.segStart F t)).natAbs ≤ S.runMax F t :=
  le_sup (f := fun t' => (S.x t' - S.x (S.segStart F t)).natAbs)
    (mem_filter.mpr ⟨mem_Icc.mpr ⟨h1, h2⟩, hown⟩)

/-- The running maximum is at most any bound on the own times of the current segment. -/
theorem runMax_le {F : ℕ × ℕ} {t M : ℕ}
    (h : ∀ t', S.Own F t' → S.segStart F t ≤ t' → t' ≤ t →
      (S.x t' - S.x (S.segStart F t)).natAbs ≤ M) : S.runMax F t ≤ M :=
  Finset.sup_le fun t' ht' => by
    obtain ⟨hI, hown⟩ := mem_filter.mp ht'
    exact h t' hown (mem_Icc.mp hI).1 (mem_Icc.mp hI).2

/-- The band at `t` is at least the band of the distance of `x t` from its home. -/
theorem band_dist_home_le_beta {t : ℕ} (ht : t < S.T) :
    band (S.x t - S.home t).natAbs ≤ S.beta t := by
  have hown := own_inner (S := S) ht
  exact band_mono (le_runMax hown (segStart_le hown.2.1.1) le_rfl)

/-! ### Intervals and segments -/

/-- A frame containing `t` lies inside any frame around it, which then contains `t`. -/
theorem Contains.of_within {F G : ℕ × ℕ} {t : ℕ} (h : Contains F t) (hw : Within F G) :
    Contains G t :=
  ⟨le_trans hw.1 h.1, lt_of_lt_of_le h.2 hw.2⟩

/-- Every interval lies inside itself. -/
theorem within_refl (F : ℕ × ℕ) : Within F F := ⟨le_rfl, le_rfl⟩

/-- Two intervals inside each other are equal. -/
theorem within_antisymm {F G : ℕ × ℕ} (h1 : Within F G) (h2 : Within G F) : F = G :=
  Prod.ext (le_antisymm h2.1 h1.1) (le_antisymm h1.2 h2.2)

/-- The root contains every time before the horizon. -/
theorem contains_root {t : ℕ} (ht : t < S.T) : Contains (0, S.T) t := ⟨Nat.zero_le _, ht⟩

/-- Own times depend only on the frames containing the time. -/
theorem Own.congr {F : ℕ × ℕ} {t t' : ℕ} (hF : S.Own F t)
    (h : ∀ G ∈ S.frames, Contains G t ↔ Contains G t') : S.Own F t' :=
  ⟨hF.1, (h F hF.1).mp hF.2.1, fun G hG hGt' => hF.2.2 G hG ((h G hG).mpr hGt')⟩

/-- The start of `F`, or a restart of `F`, at or before `t` is at most the segment start. -/
theorem le_segStart {F : ℕ × ℕ} {t s : ℕ} (hs : s = F.1 ∨ (s ∈ S.R ∧ F.1 < s ∧ S.Own F s))
    (hst : s ≤ t) : s ≤ S.segStart F t := by
  rcases hs with rfl | hs
  · exact start_le_segStart _ _
  · exact le_max' _ _ (mem_insert_of_mem (mem_filter.mpr ⟨hs.1, hs.2.1, hst, hs.2.2⟩))

/-- The segment start is monotone in time. -/
theorem segStart_mono {F : ℕ × ℕ} {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    S.segStart F t₁ ≤ S.segStart F t₂ := by
  rcases segStart_mem (S := S) F t₁ with h1 | h1
  · rw [h1]
    exact start_le_segStart F t₂
  · exact le_segStart (Or.inr ⟨h1.1, h1.2.1, h1.2.2.2⟩) (h1.2.2.1.trans h)

end FrameSystem

end BoundedStackDepth

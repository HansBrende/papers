import BoundedStackDepth.Entries
import BoundedStackDepth.Grid

/-!
# View invariance

Fix a frame system `S` (the frames of one head), a grid `h₀, r` and a group `d`. The *view* of the head
above `d` at `t` is
* `headAbove d t`: the values above `d` among its band group and the tops of its *candidates* at `d`
  (entries on the stack with `bot ≤ d < top`);
* `headVisible d t`: its *visible* entries (`d < bot ≤ top`), with their bottoms.

**View invariance** (`view_step`, `view_interval`): the view does not change at a step `t − 1 → t` unless
* a *rise*: the innermost running maximum rises at `t` into a group `g > d` (`RiseAt`), or
* a *last-stint end*: the segment innermost at `t − 1` ends its last stint at `t`, at the floor of a group `g > d`
  within its band (`LastStintAt`),

provided every nonempty non-root frame ends at band `0` (`PopsAtZero`, Lemma W2).

*Proof.* The frames containing `t − 1` or `t` are *common* (both), *popped* (end at `t`) or *pushed*
(start at `t`); popped and pushed frames lie strictly inside every common frame
(`within_of_contains_not`). Let `K` be the innermost common frame (`InnermostCommon`).
* Popped and pushed entries have bottom `0` (`entryBot_popped`, `entryBot_pushed`): they are never
  visible, and they are candidates exactly when their top is above `d`.
* A popped entry is a child of `K` (`parent_eq_of_popped`); a pushed frame is a child of `K` or of a
  pushed frame (`parent_of_pushed`), and then its top is `0` (`entryTop_eq_zero`). A popped or pushed
  child of `K` has top `c`, the group of the frozen band of `K`, and it is an entry iff the segment of
  `K` returns (`Returns`; `popped_child`, `pushed_child`).
* Hence the *local values* `LocalPre` (band group at `t − 1`, tops of popped entries) and `LocalPost`
  (band group at `t`, tops of pushed entries) agree above `d` (`localPre_iff_localPost`): this is where
  (S1) and (S3) enter.
* The bottom of a common entry changes only through the local values, so its maximum with `d` does not
  change (`max_entryBot_eq`).
-/

namespace BoundedStackDepth

namespace FrameSystem

open Finset

variable (S : FrameSystem) (h₀ r : ℕ)

open Classical in
/-- The entries on the stack at `t`. -/
noncomputable def stackEntries (t : ℕ) : Finset (ℕ × ℕ) :=
  S.frames.filter fun F => S.IsEntry F ∧ Contains F t

/-- The head's shown values above `d` at `t`: its band group and the tops of its candidates at `d`. -/
noncomputable def headAbove (d t : ℕ) : Finset ℕ :=
  (insert (S.headGroup h₀ r t) (((S.stackEntries t).filter fun F =>
    S.entryBot h₀ r F t ≤ d ∧ d < S.entryTop h₀ r F).image (S.entryTop h₀ r))).filter (d < ·)

/-- The head's visible entries above `d` at `t`, with their bottoms. -/
noncomputable def headVisible (d t : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((S.stackEntries t).filter fun F =>
    d < S.entryBot h₀ r F t ∧ S.entryBot h₀ r F t ≤ S.entryTop h₀ r F).image
      fun F => (F, S.entryBot h₀ r F t)

/-- A *rise*: the innermost running maximum rises at `t` (an own time, no restart, the frame already open)
into group `g`. -/
def RiseAt (t g : ℕ) : Prop :=
  1 ≤ g ∧ S.Own (S.inner t) t ∧ (S.inner t).1 < t ∧ ¬ S.Restart (S.inner t) t ∧
    band (S.runMax (S.inner t) (t - 1)) < flr h₀ r g ∧ flr h₀ r g ≤ band (S.runMax (S.inner t) t)

/-- A *last-stint end*: the segment innermost at `t − 1` is never innermost again from `t` on, at a floor of group `g`
within its band. -/
def LastStintAt (t g : ℕ) : Prop :=
  1 ≤ g ∧ flr h₀ r g ≤ band (S.runMax (S.inner (t - 1)) (t - 1)) ∧
    ∀ t', t ≤ t' → S.Own (S.inner (t - 1)) t' →
      S.segStart (S.inner (t - 1)) t' ≠ S.segStart (S.inner (t - 1)) (t - 1)

/-- Lemma W2: every nonempty non-root frame ends at band 0. -/
def PopsAtZero : Prop := ∀ F ∈ S.frames, F ≠ (0, S.T) → F.1 < F.2 → S.beta (F.2 - 1) = 0

/-- `K` is the innermost frame containing both `t − 1` and `t` (the innermost *common* frame). -/
def InnermostCommon (K : ℕ × ℕ) (t : ℕ) : Prop :=
  K ∈ S.frames ∧ Contains K (t - 1) ∧ Contains K t ∧
    ∀ G ∈ S.frames, Contains G (t - 1) → Contains G t → Within K G

/-- The segment of `K` current at `t − 1` is innermost again at some time from `t` on. -/
def Returns (K : ℕ × ℕ) (t : ℕ) : Prop :=
  ∃ t', t ≤ t' ∧ S.Own K t' ∧ S.segStart K t' = S.segStart K (t - 1)

/-- The *local values* at `t − 1`: the band group and the tops of the entries popped at `t`. -/
def LocalPre (t y : ℕ) : Prop :=
  y = S.headGroup h₀ r (t - 1) ∨
    ∃ Q, S.IsEntry Q ∧ Contains Q (t - 1) ∧ ¬ Contains Q t ∧ S.entryTop h₀ r Q = y

/-- The *local values* at `t`: the band group and the tops of the entries pushed at `t`. -/
def LocalPost (t y : ℕ) : Prop :=
  y = S.headGroup h₀ r t ∨
    ∃ P, S.IsEntry P ∧ Contains P t ∧ ¬ Contains P (t - 1) ∧ S.entryTop h₀ r P = y

variable {S h₀ r}

/-! ### Intervals -/



/-- A frame containing `s` but not `t` lies strictly inside every frame containing both. -/
theorem within_of_contains_not {F G : ℕ × ℕ} (hF : F ∈ S.frames) (hG : G ∈ S.frames) {s t : ℕ}
    (hFs : Contains F s) (hFt : Contains F t) (hGs : Contains G s) (hGt : ¬ Contains G t) :
    Within G F ∧ G ≠ F := by
  refine ⟨?_, fun h => hGt (by rw [h]; exact hFt)⟩
  rcases nested_of_contains hG hF hGs hFs with h | h
  · exact h
  · exact absurd (hFt.of_within h) hGt

/-- No time of a frame strictly inside `K` is an own time of `K`. -/
theorem not_own_of_within {K G : ℕ × ℕ} {s : ℕ} (hG : G ∈ S.frames) (hGs : Contains G s)
    (hGK : Within G K) (hne : G ≠ K) : ¬ S.Own K s :=
  fun h => hne (within_antisymm hGK (h.2.2 G hG hGs))

/-- A frame containing `t − 1` but not `t` ends at `t`. -/
theorem end_eq_of_pop {G : ℕ × ℕ} {t : ℕ} (h1 : Contains G (t - 1)) (h2 : ¬ Contains G t) :
    G.2 = t := by
  unfold Contains at h1 h2; omega

/-- A frame containing `t` but not `t − 1` starts at `t`. -/
theorem start_eq_of_push {G : ℕ × ℕ} {t : ℕ} (h1 : Contains G t) (h2 : ¬ Contains G (t - 1)) :
    G.1 = t := by
  unfold Contains at h1 h2; omega

/-- The innermost common frame exists (the root is common). -/
theorem exists_innermostCommon {t : ℕ} (htT : t < S.T) : ∃ K, S.InnermostCommon K t := by
  classical
  have hne : (S.frames.filter fun G => Contains G (t - 1) ∧ Contains G t).Nonempty :=
    ⟨(0, S.T), mem_filter.mpr ⟨S.root_mem, contains_root (by omega), contains_root htT⟩⟩
  obtain ⟨K, hK, hmin⟩ := exists_min_image _ (fun G : ℕ × ℕ => G.2 - G.1) hne
  obtain ⟨hKm, hK1, hK2⟩ := mem_filter.mp hK
  refine ⟨K, hKm, hK1, hK2, fun G hG hG1 hG2 => ?_⟩
  rcases nested_of_contains hKm hG hK2 hG2 with h | h
  · exact h
  · have hle : K.2 - K.1 ≤ G.2 - G.1 := hmin G (mem_filter.mpr ⟨hG, hG1, hG2⟩)
    unfold Contains at hK2 hG2
    unfold Within at h ⊢
    omega

/-- **The child of `K` at `s`.** If `s` is a time of `K` but not an own time, a longest frame strictly
inside `K` containing `s` has parent `K`. -/
theorem exists_child {K : ℕ × ℕ} (hK : K ∈ S.frames) {s : ℕ} (hs : Contains K s)
    (hown : ¬ S.Own K s) : ∃ G ∈ S.frames, Contains G s ∧ Within G K ∧ G ≠ K ∧ S.parent G = K := by
  classical
  have hne : (S.frames.filter fun G => Contains G s ∧ Within G K ∧ G ≠ K).Nonempty := by
    by_contra hemp
    refine hown ⟨hK, hs, fun G hG hGs => ?_⟩
    rcases nested_of_contains hK hG hs hGs with h | h
    · exact h
    · by_cases hGK : G = K
      · rw [hGK]; exact within_refl K
      · exact (hemp ⟨G, mem_filter.mpr ⟨hG, hGs, h, hGK⟩⟩).elim
  obtain ⟨G, hG, hmax⟩ := exists_max_image _ (fun G : ℕ × ℕ => G.2 - G.1) hne
  obtain ⟨hGm, hGs, hGK, hGne⟩ := mem_filter.mp hG
  refine ⟨G, hGm, hGs, hGK, hGne, ?_⟩
  have hroot : G ≠ (0, S.T) := by
    rintro rfl
    exact hGne (within_antisymm hGK ⟨Nat.zero_le _, S.bounds K hK⟩)
  have hlt : G.1 < G.2 := lt_of_le_of_lt hGs.1 hGs.2
  have hKa : K ∈ S.above G := mem_filter.mpr ⟨hK, hGK, fun h => hGne h.symm⟩
  obtain ⟨hP, -⟩ := parent_spec hGm hroot
  obtain ⟨hPm, hGP, hPG⟩ := mem_filter.mp hP
  by_contra hPK
  have hle : (S.parent G).2 - (S.parent G).1 ≤ G.2 - G.1 :=
    hmax _ (mem_filter.mpr ⟨hPm, hGs.of_within hGP, parent_within hGm hroot hlt hKa, hPK⟩)
  apply hPG
  unfold Within at hGP
  exact Prod.ext (by omega) (by omega)

/-- **Popped entries are children of `K`**: a popped frame whose parent is popped too is not an entry
(the parent has no own time from `t` on). -/
theorem parent_eq_of_popped {K Q : ℕ × ℕ} {t : ℕ} (hK : S.InnermostCommon K t)
    (hQ : S.IsEntry Q) (hQ1 : Contains Q (t - 1)) (hQ2 : ¬ Contains Q t) : S.parent Q = K := by
  obtain ⟨hKm, hK1, hK2, hKmin⟩ := hK
  obtain ⟨hQm, hroot, hlt, t', ht', hown, -⟩ := hQ
  obtain ⟨hQK, hne⟩ := within_of_contains_not hKm hQm hK1 hK2 hQ1 hQ2
  have hKa : K ∈ S.above Q := mem_filter.mpr ⟨hKm, hQK, fun h => hne h.symm⟩
  obtain ⟨hP, -⟩ := parent_spec hQm hroot
  obtain ⟨hPm, hQP, -⟩ := mem_filter.mp hP
  have hP1 : Contains (S.parent Q) (t - 1) := hQ1.of_within hQP
  have hP2 : Contains (S.parent Q) t := by
    by_contra h
    have h1 := end_eq_of_pop hP1 h
    have h2 := hown.2.1.2
    have h3 := end_eq_of_pop hQ1 hQ2
    omega
  exact within_antisymm (parent_within hQm hroot hlt hKa) (hKmin _ hPm hP1 hP2)

/-- The parent of a pushed frame is `K` or a frame starting at `t`. -/
theorem parent_of_pushed {K P : ℕ × ℕ} {t : ℕ} (hK : S.InnermostCommon K t)
    (hP : P ∈ S.frames) (hP1 : Contains P t) (hP2 : ¬ Contains P (t - 1)) :
    S.parent P = K ∨ (S.parent P).1 = t := by
  obtain ⟨hKm, hK1, hK2, hKmin⟩ := hK
  obtain ⟨hPK, hne⟩ := within_of_contains_not hKm hP hK2 hK1 hP1 hP2
  have hroot : P ≠ (0, S.T) := by
    rintro rfl
    exact hP2 (contains_root (lt_of_le_of_lt (Nat.sub_le t 1) hP1.2))
  have hlt : P.1 < P.2 := lt_of_le_of_lt hP1.1 hP1.2
  have hKa : K ∈ S.above P := mem_filter.mpr ⟨hKm, hPK, fun h => hne h.symm⟩
  obtain ⟨hPa, -⟩ := parent_spec hP hroot
  obtain ⟨hPm, hPP, -⟩ := mem_filter.mp hPa
  have hPt : Contains (S.parent P) t := hP1.of_within hPP
  by_cases h : Contains (S.parent P) (t - 1)
  · exact Or.inl (within_antisymm (parent_within hP hroot hlt hKa) (hKmin _ hPm h hPt))
  · exact Or.inr (start_eq_of_push hPt h)

/-! ### Grid and segment helpers -/

/-- If the group of `b` is below `g`, then `b` is below the floor of `g`. -/
private theorem lt_flr_of_lt_grp (hh : 0 < h₀) {b g : ℕ} (h : grp h₀ r b < g) : b < flr h₀ r g := by
  unfold grp at h
  unfold flr
  have h' := (Nat.div_lt_iff_lt_mul hh).mp h
  rw [Nat.mul_comm] at h'
  omega

/-- Without own times of `F` in `(t₀, t]`, the segment start does not move. -/
theorem segStart_eq_of_no_own {F : ℕ × ℕ} {t₀ t : ℕ} (h0 : F.1 ≤ t₀)
    (hno : ∀ s, t₀ < s → s ≤ t → ¬ S.Own F s) (ht : t₀ ≤ t) :
    S.segStart F t = S.segStart F t₀ := by
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    rw [show S.segStart F (t + 1) = S.segStart F (t + 1 - 1) from
      segStart_succ (by omega) fun h => hno _ (by omega) le_rfl h.2.2]
    exact ih fun s h1 h2 => hno s h1 (by omega)

/-- After a restart of `K` at `t`, its segment of `t − 1` never returns. -/
theorem not_returns_of_restart {K : ℕ × ℕ} {t : ℕ} (ht : 1 ≤ t) (hK : K.1 ≤ t - 1)
    (hres : S.Restart K t) : ¬ S.Returns K t := by
  rintro ⟨t', ht', -, heq⟩
  have h1 := segStart_mono (S := S) (F := K) ht'
  rw [segStart_of_restart hres] at h1
  have h2 := segStart_le (S := S) hK
  omega

/-! ### Children of `K`, band groups and bottoms -/

/-- **The popped child of `K`.** A frame popped at `t` with parent `K` has top `c` (the group of the
frozen band of `K` at `t − 1`), and it is an entry iff the segment of `K` returns. -/
theorem popped_child {K Q : ℕ × ℕ} {t : ℕ} (hK : S.InnermostCommon K t)
    (hQ : Q ∈ S.frames) (hQ1 : Contains Q (t - 1)) (hQ2 : ¬ Contains Q t) (hpar : S.parent Q = K) :
    S.entryTop h₀ r Q = grp h₀ r (band (S.runMax K (t - 1))) ∧ (S.IsEntry Q ↔ S.Returns K t) := by
  have ht : 1 ≤ t := by unfold Contains at hQ1 hQ2; omega
  obtain ⟨hKm, hK1, hK2, -⟩ := hK
  obtain ⟨hQK, hne⟩ := within_of_contains_not hKm hQ hK1 hK2 hQ1 hQ2
  have hend := end_eq_of_pop hQ1 hQ2
  have hno : ∀ s, Q.1 < s → s ≤ t - 1 → ¬ S.Own K s := fun s h1 h2 =>
    not_own_of_within hQ ⟨h1.le, by omega⟩ hQK hne
  have hrun := runMax_frozen hQK.1 hno hQ1.1
  have hseg := segStart_eq_of_no_own hQK.1 hno hQ1.1
  refine ⟨by unfold entryTop; rw [hpar, hrun], ?_⟩
  have hroot : Q ≠ (0, S.T) := by
    rintro rfl
    exact hQ2 (contains_root (lt_of_lt_of_le hK2.2 (S.bounds K hKm)))
  unfold IsEntry Returns
  rw [hpar, ← hseg, hend]
  constructor
  · rintro ⟨-, -, -, h⟩; exact h
  · intro h; exact ⟨hQ, hroot, lt_of_le_of_lt hQ1.1 (by omega), h⟩

/-- **The pushed child of `K`.** A frame pushed at `t` with parent `K` has top `c`, and it is an entry
iff the segment of `K` returns. -/
theorem pushed_child {K P : ℕ × ℕ} {t : ℕ} (hK : S.InnermostCommon K t)
    (hP : P ∈ S.frames) (hP1 : Contains P t) (hP2 : ¬ Contains P (t - 1)) (hpar : S.parent P = K) :
    S.entryTop h₀ r P = grp h₀ r (band (S.runMax K (t - 1))) ∧ (S.IsEntry P ↔ S.Returns K t) := by
  have ht : 1 ≤ t := by unfold Contains at hP1 hP2; omega
  obtain ⟨hKm, hK1, hK2, -⟩ := hK
  obtain ⟨hPK, hne⟩ := within_of_contains_not hKm hP hK2 hK1 hP1 hP2
  have hst := start_eq_of_push hP1 hP2
  have hKt : ¬ S.Own K t := not_own_of_within hP hP1 hPK hne
  have hKlt : K.1 < t := lt_of_le_of_lt hK1.1 (by omega)
  have hrun := runMax_succ_of_not_own hKlt hKt
  have hseg := segStart_succ hKlt fun h => hKt h.2.2
  refine ⟨by unfold entryTop; rw [hpar, hst, hrun], ?_⟩
  have hroot : P ≠ (0, S.T) := by
    rintro rfl
    exact hP2 (contains_root (lt_of_le_of_lt (Nat.sub_le t 1) hP1.2))
  unfold IsEntry Returns
  rw [hpar, hst, hseg]
  constructor
  · rintro ⟨-, -, hlt, t', h1, h2, h3⟩
    exact ⟨t', by omega, h2, h3⟩
  · rintro ⟨t', h1, h2, h3⟩
    refine ⟨hP, hroot, hP1.2, t', ?_, h2, h3⟩
    by_contra h
    exact not_own_of_within hP ⟨by omega, by omega⟩ hPK hne h2

/-- An entry pushed together with its parent has top `0`. -/
theorem entryTop_eq_zero (hr : r < h₀) {P : ℕ × ℕ} (h : (S.parent P).1 = P.1) :
    S.entryTop h₀ r P = 0 := by
  unfold entryTop
  rw [← h, runMax_start, band_zero]
  exact grp_zero hr

/-- **Lemma W2 at a pop.** If some frame ends at `t`, the band group at `t − 1` is `0`. -/
theorem headGroup_pred_eq_zero (hr : r < h₀) (hW : S.PopsAtZero) {t : ℕ} (htT : t < S.T)
    {Q : ℕ × ℕ} (hQ : Q ∈ S.frames) (hQ1 : Contains Q (t - 1)) (hQ2 : ¬ Contains Q t) :
    S.headGroup h₀ r (t - 1) = 0 := by
  have hJ := own_inner (S := S) (show t - 1 < S.T by omega)
  have hJQ := hJ.2.2 Q hQ hQ1
  have hJ2 : ¬ Contains (S.inner (t - 1)) t := fun h =>
    hQ2 ⟨le_trans hQ1.1 (Nat.sub_le t 1), lt_of_lt_of_le h.2 hJQ.2⟩
  have hend := end_eq_of_pop hJ.2.1 hJ2
  have hroot : S.inner (t - 1) ≠ (0, S.T) := fun h => hJ2 (by rw [h]; exact contains_root htT)
  have h0 := hW _ hJ.1 hroot (lt_of_le_of_lt hJ.2.1.1 hJ.2.1.2)
  rw [hend] at h0
  unfold headGroup
  rw [h0]
  exact grp_zero hr

/-- At a push, the band group at `t` is `0`. -/
theorem headGroup_eq_zero_of_push (hr : r < h₀) {t : ℕ} {P : ℕ × ℕ} (hP : P ∈ S.frames)
    (hP1 : Contains P t) (hP2 : ¬ Contains P (t - 1)) : S.headGroup h₀ r t = 0 := by
  have hJ := own_inner (S := S) (lt_of_lt_of_le hP1.2 (S.bounds P hP))
  have hJP := hJ.2.2 P hP hP1
  have hst : (S.inner t).1 = t := by
    have h1 := start_eq_of_push hP1 hP2
    have h2 := hJ.2.1.1
    have h3 := hJP.1
    omega
  have hrun := runMax_start S (S.inner t)
  rw [hst] at hrun
  unfold headGroup beta
  rw [hrun, band_zero]
  exact grp_zero hr

/-- **Popped entries are never visible**: their bottom at `t − 1` is `0`. -/
theorem entryBot_popped (hr : r < h₀) (hW : S.PopsAtZero) {t : ℕ} (htT : t < S.T)
    {Q : ℕ × ℕ} (hQ : Q ∈ S.frames) (hQ1 : Contains Q (t - 1)) (hQ2 : ¬ Contains Q t) :
    S.entryBot h₀ r Q (t - 1) = 0 := by
  classical
  have hend := end_eq_of_pop hQ1 hQ2
  unfold entryBot
  refine Nat.eq_zero_of_le_zero (max_le (headGroup_pred_eq_zero hr hW htT hQ hQ1 hQ2).le
    (Finset.sup_le fun F' hF' => ?_))
  exfalso
  obtain ⟨hF'm, hE, hw, hne, hc⟩ := mem_filter.mp hF'
  obtain ⟨-, hroot, hlt, t', ht', hown, -⟩ := hE
  have hQa : Q ∈ S.above F' := mem_filter.mpr ⟨hQ, hw, fun h => hne h.symm⟩
  have h1 := (parent_within hF'm hroot hlt hQa).2
  have h2 := hown.2.1.2
  have h3 := hc.2
  omega

/-- **Pushed entries are never visible**: their bottom at `t` is `0`. -/
theorem entryBot_pushed (hr : r < h₀) {t : ℕ} {P : ℕ × ℕ} (hP : P ∈ S.frames)
    (hP1 : Contains P t) (hP2 : ¬ Contains P (t - 1)) : S.entryBot h₀ r P t = 0 := by
  classical
  have hst := start_eq_of_push hP1 hP2
  unfold entryBot
  refine Nat.eq_zero_of_le_zero (max_le (headGroup_eq_zero_of_push hr hP hP1 hP2).le
    (Finset.sup_le fun F' hF' => (entryTop_eq_zero hr ?_).le))
  obtain ⟨hF'm, hE, hw, hne, hc⟩ := mem_filter.mp hF'
  obtain ⟨-, hroot, hlt, -⟩ := hE
  have hPa : P ∈ S.above F' := mem_filter.mpr ⟨hP, hw, fun h => hne h.symm⟩
  have h1 := (parent_within hF'm hroot hlt hPa).1
  obtain ⟨hpa, -⟩ := parent_spec hF'm hroot
  have h2 := (mem_filter.mp hpa).2.1.1
  have h3 := hc.1
  have h4 := hw.1
  omega

/-! ### Common entries -/

/-- The bottom of a common entry at `t − 1`, through its common inner entries and the local values. -/
theorem entryBot_pre_le_iff {F : ℕ × ℕ} (hF : F ∈ S.frames) {t z : ℕ} (h1 : Contains F (t - 1))
    (h2 : Contains F t) : S.entryBot h₀ r F (t - 1) ≤ z ↔
      (∀ F', S.IsEntry F' → Within F' F → F' ≠ F → Contains F' (t - 1) → Contains F' t →
        S.entryTop h₀ r F' ≤ z) ∧ ∀ y, S.LocalPre h₀ r t y → y ≤ z := by
  classical
  unfold entryBot
  rw [max_le_iff, Finset.sup_le_iff]
  constructor
  · rintro ⟨hg, hall⟩
    refine ⟨fun F' hE hw hne h1' _ => hall F' (mem_filter.mpr ⟨hE.1, hE, hw, hne, h1'⟩), ?_⟩
    rintro y (rfl | ⟨Q, hE, hQ1, hQ2, rfl⟩)
    · exact hg
    · obtain ⟨hw, hne⟩ := within_of_contains_not hF hE.1 h1 h2 hQ1 hQ2
      exact hall Q (mem_filter.mpr ⟨hE.1, hE, hw, hne, hQ1⟩)
  · rintro ⟨hc, hl⟩
    refine ⟨hl _ (Or.inl rfl), fun F' hF' => ?_⟩
    obtain ⟨-, hE, hw, hne, h1'⟩ := mem_filter.mp hF'
    by_cases h2' : Contains F' t
    · exact hc F' hE hw hne h1' h2'
    · exact hl _ (Or.inr ⟨F', hE, h1', h2', rfl⟩)

/-- The bottom of a common entry at `t`, through its common inner entries and the local values. -/
theorem entryBot_post_le_iff {F : ℕ × ℕ} (hF : F ∈ S.frames) {t z : ℕ} (h1 : Contains F (t - 1))
    (h2 : Contains F t) : S.entryBot h₀ r F t ≤ z ↔
      (∀ F', S.IsEntry F' → Within F' F → F' ≠ F → Contains F' (t - 1) → Contains F' t →
        S.entryTop h₀ r F' ≤ z) ∧ ∀ y, S.LocalPost h₀ r t y → y ≤ z := by
  classical
  unfold entryBot
  rw [max_le_iff, Finset.sup_le_iff]
  constructor
  · rintro ⟨hg, hall⟩
    refine ⟨fun F' hE hw hne _ h2' => hall F' (mem_filter.mpr ⟨hE.1, hE, hw, hne, h2'⟩), ?_⟩
    rintro y (rfl | ⟨P, hE, hP1, hP2, rfl⟩)
    · exact hg
    · obtain ⟨hw, hne⟩ := within_of_contains_not hF hE.1 h2 h1 hP1 hP2
      exact hall P (mem_filter.mpr ⟨hE.1, hE, hw, hne, hP1⟩)
  · rintro ⟨hc, hl⟩
    refine ⟨hl _ (Or.inl rfl), fun F' hF' => ?_⟩
    obtain ⟨-, hE, hw, hne, h2'⟩ := mem_filter.mp hF'
    by_cases h1' : Contains F' (t - 1)
    · exact hc F' hE hw hne h1' h2'
    · exact hl _ (Or.inr ⟨F', hE, h2', h1', rfl⟩)

/-- **Common entries.** If the local values agree above `d`, the bottom of a common entry has the same
maximum with `d` at `t − 1` and at `t`. -/
theorem max_entryBot_eq {t d : ℕ}
    (hkey : ∀ y, d < y → (S.LocalPre h₀ r t y ↔ S.LocalPost h₀ r t y)) {F : ℕ × ℕ}
    (hF : F ∈ S.frames) (h1 : Contains F (t - 1)) (h2 : Contains F t) :
    max d (S.entryBot h₀ r F (t - 1)) = max d (S.entryBot h₀ r F t) := by
  have key : ∀ z, d ≤ z → (S.entryBot h₀ r F (t - 1) ≤ z ↔ S.entryBot h₀ r F t ≤ z) := by
    intro z hz
    rw [entryBot_pre_le_iff hF h1 h2, entryBot_post_le_iff hF h1 h2]
    refine and_congr_right fun _ => ⟨fun hl y hy => ?_, fun hl y hy => ?_⟩
    · by_cases hyd : y ≤ d
      · exact hyd.trans hz
      · exact hl y ((hkey y (not_le.mp hyd)).mpr hy)
    · by_cases hyd : y ≤ d
      · exact hyd.trans hz
      · exact hl y ((hkey y (not_le.mp hyd)).mp hy)
  exact le_antisymm
    (max_le (le_max_left _ _) ((key _ (le_max_left _ _)).mpr (le_max_right _ _)))
    (max_le (le_max_left _ _) ((key _ (le_max_left _ _)).mp (le_max_right _ _)))

/-! ### The local values -/

/-- **Local values at `t − 1`** (above `0`): the group `c` of the band of `K` at `t − 1`, unless the
head pops at `t` and the segment of `K` does not return. -/
theorem localPre_iff (hr : r < h₀) (hW : S.PopsAtZero) {t : ℕ} (htT : t < S.T)
    {K : ℕ × ℕ} (hK : S.InnermostCommon K t) {y : ℕ} (hy : 0 < y) :
    S.LocalPre h₀ r t y ↔
      y = grp h₀ r (band (S.runMax K (t - 1))) ∧ (S.Own K (t - 1) ∨ S.Returns K t) := by
  unfold LocalPre
  by_cases hown : S.Own K (t - 1)
  · have hinner : S.inner (t - 1) = K := inner_eq hown
    simp only [hown, true_or, and_true]
    constructor
    · rintro (h | ⟨Q, hE, hQ1, hQ2, -⟩)
      · rw [h]; unfold headGroup beta; rw [hinner]
      · obtain ⟨hQK, hne⟩ := within_of_contains_not hK.1 hE.1 hK.2.1 hK.2.2.1 hQ1 hQ2
        exact absurd hown (not_own_of_within hE.1 hQ1 hQK hne)
    · intro h; left; rw [h]; unfold headGroup beta; rw [hinner]
  · obtain ⟨Q, hQm, hQ1, hQK, hne, hpar⟩ := exists_child hK.1 hK.2.1 hown
    have hQ2 : ¬ Contains Q t := fun h => hne (within_antisymm hQK (hK.2.2.2 Q hQm hQ1 h))
    have hg := headGroup_pred_eq_zero hr hW htT hQm hQ1 hQ2
    simp only [hown, false_or]
    rw [hg]
    constructor
    · rintro (h | ⟨Q', hE, hQ1', hQ2', rfl⟩)
      · omega
      · obtain ⟨htop, hiff⟩ := popped_child (h₀ := h₀) (r := r) hK hE.1 hQ1' hQ2'
          (parent_eq_of_popped hK hE hQ1' hQ2')
        exact ⟨htop, hiff.mp hE⟩
    · rintro ⟨rfl, hret⟩
      obtain ⟨htop, hiff⟩ := popped_child (h₀ := h₀) (r := r) hK hQm hQ1 hQ2 hpar
      exact Or.inr ⟨Q, hiff.mpr hret, hQ1, hQ2, htop⟩

/-- **Local values at `t`** (above `0`): the group of the band of `K` at `t` if `t` is an own time of
`K`; at a push, the group `c` if the segment of `K` returns, and nothing otherwise. -/
theorem localPost_iff (hr : r < h₀) {t : ℕ} {K : ℕ × ℕ} (hK : S.InnermostCommon K t)
    {y : ℕ} (hy : 0 < y) : S.LocalPost h₀ r t y ↔
      (S.Own K t ∧ y = grp h₀ r (band (S.runMax K t))) ∨
        (¬ S.Own K t ∧ S.Returns K t ∧ y = grp h₀ r (band (S.runMax K (t - 1)))) := by
  unfold LocalPost
  by_cases hown : S.Own K t
  · have hinner : S.inner t = K := inner_eq hown
    simp only [hown, true_and, not_true_eq_false, false_and, or_false]
    constructor
    · rintro (h | ⟨P, hE, hP1, hP2, -⟩)
      · rw [h]; unfold headGroup beta; rw [hinner]
      · obtain ⟨hPK, hne⟩ := within_of_contains_not hK.1 hE.1 hK.2.2.1 hK.2.1 hP1 hP2
        exact absurd hown (not_own_of_within hE.1 hP1 hPK hne)
    · intro h; left; rw [h]; unfold headGroup beta; rw [hinner]
  · obtain ⟨P, hPm, hP1, hPK, hne, hpar⟩ := exists_child hK.1 hK.2.2.1 hown
    have hP2 : ¬ Contains P (t - 1) := fun h => hne (within_antisymm hPK (hK.2.2.2 P hPm h hP1))
    have hg := headGroup_eq_zero_of_push hr hPm hP1 hP2
    simp only [hown, false_and, false_or, not_false_eq_true, true_and]
    rw [hg]
    constructor
    · rintro (h | ⟨P', hE, hP1', hP2', rfl⟩)
      · omega
      · rcases parent_of_pushed hK hE.1 hP1' hP2' with hpar' | hpar'
        · obtain ⟨htop, hiff⟩ := pushed_child (h₀ := h₀) (r := r) hK hE.1 hP1' hP2' hpar'
          exact ⟨hiff.mp hE, htop⟩
        · have h0 := entryTop_eq_zero (h₀ := h₀) hr (P := P')
            (by rw [hpar', start_eq_of_push hP1' hP2'])
          omega
    · rintro ⟨hret, rfl⟩
      obtain ⟨htop, hiff⟩ := pushed_child (h₀ := h₀) (r := r) hK hPm hP1 hP2 hpar
      exact Or.inr ⟨P, hiff.mpr hret, hP1, hP2, htop⟩

/-- **Key claim.** Without rises and last-stint ends above `d` at `t`, the local values agree above
`d`. -/
theorem localPre_iff_localPost (hr : r < h₀) (hW : S.PopsAtZero) {t : ℕ} (ht : 1 ≤ t)
    (htT : t < S.T) {d : ℕ}
    (hno : ∀ g, d + 1 ≤ g → ¬ S.RiseAt h₀ r t g ∧ ¬ S.LastStintAt h₀ r t g) {y : ℕ} (hy : d < y) :
    S.LocalPre h₀ r t y ↔ S.LocalPost h₀ r t y := by
  obtain ⟨K, hK⟩ := exists_innermostCommon (S := S) htT
  have hKlt : K.1 < t := lt_of_le_of_lt hK.2.1.1 (by omega)
  rw [localPre_iff hr hW htT hK (by omega), localPost_iff hr hK (by omega)]
  -- last-stint end: if the segment of `K` innermost at `t − 1` does not return, its group is at most `d`.
  have hlast : S.Own K (t - 1) → ¬ S.Returns K t → grp h₀ r (band (S.runMax K (t - 1))) ≤ d := by
    intro hown hret
    by_contra hc
    have hc' : d + 1 ≤ grp h₀ r (band (S.runMax K (t - 1))) := by omega
    have hinner : S.inner (t - 1) = K := inner_eq hown
    refine (hno _ hc').2 ⟨by omega, ?_, ?_⟩
    · rw [hinner]; exact flr_grp_le h₀ r _
    · intro t' ht' hown' heq
      rw [hinner] at hown' heq
      exact hret ⟨t', ht', hown', heq⟩
  by_cases hpush : S.Own K t
  · have hinner : S.inner t = K := inner_eq hpush
    simp only [hpush, true_and, not_true_eq_false, false_and, or_false]
    by_cases hres : S.Restart K t
    · -- a restart at `t`: the band group drops to `0`, and the old segment never returns
      have hc0 : grp h₀ r (band (S.runMax K t)) = 0 := by
        rw [runMax_of_restart hres, band_zero]; exact grp_zero hr
      have hnret := not_returns_of_restart ht hK.2.1.1 hres
      rw [hc0]
      constructor
      · rintro ⟨rfl, h | h⟩
        · have := hlast h hnret; omega
        · exact absurd h hnret
      · intro h; omega
    · -- an own time without restart: the group can only rise, and a rise above `d` is an event
      have hle : grp h₀ r (band (S.runMax K (t - 1))) ≤ grp h₀ r (band (S.runMax K t)) :=
        grp_mono h₀ r (band_mono (runMax_le_succ hKlt hres))
      have hrise : ∀ g, d < g → grp h₀ r (band (S.runMax K (t - 1))) < g →
          g = grp h₀ r (band (S.runMax K t)) → False := by
        intro g hdg hlt hg
        refine (hno g (by omega)).1 ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hinner]; exact hpush
        · rw [hinner]; exact hKlt
        · rw [hinner]; exact hres
        · rw [hinner]; exact lt_flr_of_lt_grp (by omega) hlt
        · rw [hinner, hg]; exact flr_grp_le h₀ r _
      have hret : S.Own K (t - 1) ∨ S.Returns K t := by
        by_cases h : S.Own K (t - 1)
        · exact Or.inl h
        · exact Or.inr ⟨t, le_rfl, hpush, segStart_succ hKlt hres⟩
      constructor
      · rintro ⟨rfl, -⟩
        by_contra hne
        exact hrise _ (by omega) (lt_of_le_of_ne hle hne) rfl
      · rintro rfl
        refine ⟨?_, hret⟩
        by_contra hne
        exact hrise _ hy (lt_of_le_of_ne hle (Ne.symm hne)) rfl
  · -- a push at `t`: the pushed child of `K` carries `c` exactly when the segment of `K` returns
    simp only [hpush, false_and, false_or, not_false_eq_true, true_and]
    constructor
    · rintro ⟨rfl, h | h⟩
      · by_cases hret : S.Returns K t
        · exact ⟨hret, rfl⟩
        · have := hlast h hret; omega
      · exact ⟨h, rfl⟩
    · rintro ⟨hret, rfl⟩
      exact ⟨rfl, Or.inr hret⟩

/-! ### View invariance -/

/-- Membership in `headAbove`, unfolded. -/
theorem mem_headAbove {d t y : ℕ} : y ∈ S.headAbove h₀ r d t ↔ d < y ∧ (y = S.headGroup h₀ r t ∨
    ∃ F, S.IsEntry F ∧ Contains F t ∧ S.entryBot h₀ r F t ≤ d ∧ d < S.entryTop h₀ r F ∧
      S.entryTop h₀ r F = y) := by
  classical
  unfold headAbove stackEntries
  constructor
  · intro h
    obtain ⟨h, hy⟩ := mem_filter.mp h
    refine ⟨hy, ?_⟩
    rcases mem_insert.mp h with h | h
    · exact Or.inl h
    · obtain ⟨F, hF, rfl⟩ := mem_image.mp h
      obtain ⟨hF, hb, hlt⟩ := mem_filter.mp hF
      obtain ⟨-, hE, hc⟩ := mem_filter.mp hF
      exact Or.inr ⟨F, hE, hc, hb, hlt, rfl⟩
  · rintro ⟨hy, h | ⟨F, hE, hc, hb, hlt, rfl⟩⟩
    · exact mem_filter.mpr ⟨mem_insert.mpr (Or.inl h), hy⟩
    · exact mem_filter.mpr ⟨mem_insert_of_mem (mem_image.mpr
        ⟨F, mem_filter.mpr ⟨mem_filter.mpr ⟨hE.1, hE, hc⟩, hb, hlt⟩, rfl⟩), hy⟩

/-- Membership in `headVisible`, unfolded. -/
theorem mem_headVisible {d t b : ℕ} {F : ℕ × ℕ} : (F, b) ∈ S.headVisible h₀ r d t ↔
    S.IsEntry F ∧ Contains F t ∧ d < S.entryBot h₀ r F t ∧
      S.entryBot h₀ r F t ≤ S.entryTop h₀ r F ∧ S.entryBot h₀ r F t = b := by
  classical
  unfold headVisible stackEntries
  constructor
  · intro h
    obtain ⟨F', hF', heq⟩ := mem_image.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    obtain ⟨hF', hd, hle⟩ := mem_filter.mp hF'
    obtain ⟨-, hE, hc⟩ := mem_filter.mp hF'
    exact ⟨hE, hc, hd, hle, rfl⟩
  · rintro ⟨hE, hc, hd, hle, rfl⟩
    exact mem_image.mpr ⟨F, mem_filter.mpr ⟨mem_filter.mpr ⟨hE.1, hE, hc⟩, hd, hle⟩, rfl⟩

/-- The band group and the candidates at `t − 1`, split into local values and common candidates. -/
theorem above_pre_iff (hr : r < h₀) (hW : S.PopsAtZero) {t : ℕ} (htT : t < S.T) {d y : ℕ}
    (hy : d < y) : (y = S.headGroup h₀ r (t - 1) ∨ ∃ F, S.IsEntry F ∧ Contains F (t - 1) ∧
      S.entryBot h₀ r F (t - 1) ≤ d ∧ d < S.entryTop h₀ r F ∧ S.entryTop h₀ r F = y) ↔
    S.LocalPre h₀ r t y ∨ ∃ F, S.IsEntry F ∧ Contains F (t - 1) ∧ Contains F t ∧
      S.entryBot h₀ r F (t - 1) ≤ d ∧ S.entryTop h₀ r F = y := by
  constructor
  · rintro (h | ⟨F, hE, h1, hb, -, htop⟩)
    · exact Or.inl (Or.inl h)
    · by_cases h2 : Contains F t
      · exact Or.inr ⟨F, hE, h1, h2, hb, htop⟩
      · exact Or.inl (Or.inr ⟨F, hE, h1, h2, htop⟩)
  · rintro ((h | ⟨Q, hE, h1, h2, htop⟩) | ⟨F, hE, h1, -, hb, htop⟩)
    · exact Or.inl h
    · refine Or.inr ⟨Q, hE, h1, ?_, lt_of_lt_of_eq hy htop.symm, htop⟩
      rw [entryBot_popped hr hW htT hE.1 h1 h2]; exact Nat.zero_le d
    · exact Or.inr ⟨F, hE, h1, hb, lt_of_lt_of_eq hy htop.symm, htop⟩

/-- The band group and the candidates at `t`, split into local values and common candidates. -/
theorem above_post_iff (hr : r < h₀) {t : ℕ} {d y : ℕ} (hy : d < y) :
    (y = S.headGroup h₀ r t ∨ ∃ F, S.IsEntry F ∧ Contains F t ∧
      S.entryBot h₀ r F t ≤ d ∧ d < S.entryTop h₀ r F ∧ S.entryTop h₀ r F = y) ↔
    S.LocalPost h₀ r t y ∨ ∃ F, S.IsEntry F ∧ Contains F (t - 1) ∧ Contains F t ∧
      S.entryBot h₀ r F t ≤ d ∧ S.entryTop h₀ r F = y := by
  constructor
  · rintro (h | ⟨F, hE, h2, hb, -, htop⟩)
    · exact Or.inl (Or.inl h)
    · by_cases h1 : Contains F (t - 1)
      · exact Or.inr ⟨F, hE, h1, h2, hb, htop⟩
      · exact Or.inl (Or.inr ⟨F, hE, h2, h1, htop⟩)
  · rintro ((h | ⟨P, hE, h2, h1, htop⟩) | ⟨F, hE, -, h2, hb, htop⟩)
    · exact Or.inl h
    · refine Or.inr ⟨P, hE, h2, ?_, lt_of_lt_of_eq hy htop.symm, htop⟩
      rw [entryBot_pushed hr hE.1 h2 h1]; exact Nat.zero_le d
    · exact Or.inr ⟨F, hE, h2, hb, lt_of_lt_of_eq hy htop.symm, htop⟩

/-- **View invariance, one step.** Without rises and last-stint ends at `t` at the floors of groups above
`d`, the head shows the same values and the same visible entries above `d` at `t − 1` and at `t`. -/
theorem view_step (hr : r < h₀) (hW : S.PopsAtZero) {t : ℕ} (htT : t < S.T) (d : ℕ)
    (hno : ∀ g, d + 1 ≤ g → ¬ S.RiseAt h₀ r t g ∧ ¬ S.LastStintAt h₀ r t g) :
    S.headAbove h₀ r d (t - 1) = S.headAbove h₀ r d t ∧
      S.headVisible h₀ r d (t - 1) = S.headVisible h₀ r d t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact ⟨rfl, rfl⟩
  have hkey : ∀ y, d < y → (S.LocalPre h₀ r t y ↔ S.LocalPost h₀ r t y) :=
    fun y hy => localPre_iff_localPost hr hW ht htT hno hy
  have hmax : ∀ F, S.IsEntry F → Contains F (t - 1) → Contains F t →
      max d (S.entryBot h₀ r F (t - 1)) = max d (S.entryBot h₀ r F t) :=
    fun F hE h1 h2 => max_entryBot_eq hkey hE.1 h1 h2
  constructor
  · ext y
    rw [mem_headAbove, mem_headAbove]
    refine and_congr_right fun hy => ?_
    rw [above_pre_iff hr hW htT hy, above_post_iff hr hy]
    refine or_congr (hkey y hy) (exists_congr fun F => ⟨?_, ?_⟩)
    · rintro ⟨hE, h1, h2, hb, htop⟩
      have := hmax F hE h1 h2
      exact ⟨hE, h1, h2, by omega, htop⟩
    · rintro ⟨hE, h1, h2, hb, htop⟩
      have := hmax F hE h1 h2
      exact ⟨hE, h1, h2, by omega, htop⟩
  · ext ⟨F, b⟩
    rw [mem_headVisible, mem_headVisible]
    constructor
    · rintro ⟨hE, h1, hd, hle, hb⟩
      have h2 : Contains F t := by
        by_contra h2
        rw [entryBot_popped hr hW htT hE.1 h1 h2] at hd
        exact Nat.not_lt_zero d hd
      have := hmax F hE h1 h2
      have heq : S.entryBot h₀ r F t = S.entryBot h₀ r F (t - 1) := by omega
      rw [heq]
      exact ⟨hE, h2, hd, hle, hb⟩
    · rintro ⟨hE, h2, hd, hle, hb⟩
      have h1 : Contains F (t - 1) := by
        by_contra h1
        rw [entryBot_pushed hr hE.1 h2 h1] at hd
        exact Nat.not_lt_zero d hd
      have := hmax F hE h1 h2
      have heq : S.entryBot h₀ r F (t - 1) = S.entryBot h₀ r F t := by omega
      rw [heq]
      exact ⟨hE, h1, hd, hle, hb⟩

/-- **View invariance over an interval.** Without rises and last-stint ends in `(p, u]` at the floors of
groups above `d`, the head's view above `d` is the same at `p` and at `u`. -/
theorem view_interval (hr : r < h₀) (hW : S.PopsAtZero) {p u : ℕ} (hpu : p ≤ u) (huT : u < S.T)
    (d : ℕ)
    (hno : ∀ t, p < t → t ≤ u → ∀ g, d + 1 ≤ g →
      ¬ S.RiseAt h₀ r t g ∧ ¬ S.LastStintAt h₀ r t g) :
    S.headAbove h₀ r d p = S.headAbove h₀ r d u ∧ S.headVisible h₀ r d p = S.headVisible h₀ r d u := by
  induction u, hpu using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ u hpu ih =>
    obtain ⟨h1, h2⟩ := ih (by omega) fun t h1 h2 => hno t h1 (by omega)
    obtain ⟨h3, h4⟩ := view_step hr hW (t := u + 1) huT d (hno (u + 1) (by omega) le_rfl)
    exact ⟨h1.trans h3, h2.trans h4⟩

end FrameSystem

end BoundedStackDepth

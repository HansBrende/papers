import BoundedStackDepth.Excursions
import BoundedStackDepth.FrameDynamics
import BoundedStackDepth.PerExcursion

/-!
# Bands at ladder times (Theorem A; Lemma W2)

Let `x` be a walk (pauses allowed), `S = upperFrames x T hx` the frame system of class U, `τ` a
top with canonical excursion `[a, b] = exc τ`, base `y` and height `H ≥ 1`, and `F = S.inner τ` the
frame that contains the excursion.

* `frame_cases`: every frame contains the interior `[a + 1, b)` of the excursion, misses it, or is
  a frame of a top nested in `τ`. A time is *free* for `τ` (`Free`) if no frame of `τ` or of a top
  nested in `τ` contains it; the ladder times are free (`free_top`, `free_ladL`, `free_ladD`).
* **Own times** (`own_of_free`, `free_of_own`): the own times of `F` in `(a, b)` are exactly the
  free times, among them all ladder times. With pauses a free time need not be a ladder time: the
  walk may pause at its top (`0, 1, 1, 0`).
* **Restarts inside** (`restart_inside`, `passage_spec`): for `a < t < b`, a restart point that is an
  own time of `F` is a passage `D τ (y + 2^e)`, and every passage is one.
* **Start** (`inner_fst_cases`, `own_exc_fst`, `exc_fst_mem_R`, `excStart_spec`): either `F` is the
  descent frame of a top `P` at level `y` with `D P y = a` (the first excursion of a descent
  structure; `F` starts at `a + 1`), or `a` is the start of `F` or a restart of `F`. The segment of
  the excursion starts at `excStart = max (F.1, a)`, with home `y` or `y + 1` (`x_excStart`).
* **End** (`inner_top_bounds`, `inner_snd_cases`, `inner_exc_snd`): `b ≤ F.2`, and `b = F.2` only
  for the last excursion of a hanging structure (`F = hangFrame P y`, `L P y = b`); otherwise the
  innermost frame at `b` is `F` or starts at `b`.
* **Segment starts** (`segStart_eq_excStart`, `segStart_eq_passage`, `segStart_ladD`,
  `segStart_ladD_of_not`): at the climb ladder times and at `τ` the segment starts at `excStart`;
  at `D τ (y + d)` at the passage `D τ (y + 2^e)`, `e = ⌈log₂ d⌉`, if `2^e < H`, else at
  `excStart`. Strictly inside the excursion every segment starts in `[a, t]`
  (`segStart_inner_mem`), so homes lie in `[y, x τ]` and bands are at most `band H`.
* **Bands** (`beta_ladL_bounds`, `beta_ladD_bounds`, `home_mem_exc`, `ladL_lt_segStart_ladD`):
  in the form used by the per-excursion bound.
* `beta_last_eq_zero` (**Lemma W2**): every nonempty suspend frame ends at band `0`.
-/

namespace BoundedStackDepth

open BoundedNesting Finset

open FrameSystem

variable {x : ℕ → ℤ} {T τ : ℕ}

/-! ### The canonical excursion -/

theorem exc_fst_lt (hx : IsWalk x) (hτ : τ ∈ tops x T) : (exc x T τ).1 < τ :=
  ladL_lt hx le_rfl (base_lt hτ)

theorem lt_exc_snd (hx : IsWalk x) (hτ : τ ∈ tops x T) : τ < (exc x T τ).2 :=
  lt_ladD hx le_rfl (base_lt hτ)

theorem exc_snd_lt (hx : IsWalk x) (hτ : τ ∈ tops x T) : (exc x T τ).2 < T :=
  ladD_lt_T hx le_rfl (base_lt hτ)

theorem x_exc_fst (hx : IsWalk x) (hτ : τ ∈ tops x T) : x (exc x T τ).1 = base x T τ :=
  x_ladL hx le_rfl (base_lt hτ)

theorem x_top (x : ℕ → ℤ) (T τ : ℕ) : x τ = base x T τ + height x T τ := by
  unfold base; ring

/-- Strictly inside the canonical excursion the walk is above the base. -/
theorem base_lt_of_mem (hx : IsWalk x) (hτ : τ ∈ tops x T) {t : ℕ} (h1 : (exc x T τ).1 < t)
    (h2 : t < (exc x T τ).2) : base x T τ < x t := by
  have := (isUpperHop_exc hx hτ).above t h1 h2
  rwa [x_exc_fst hx hτ] at this

/-- The cells `y + d`, `d < H`, of the ladder. -/
theorem cell_bounds {d : ℕ} (hd : d < height x T τ) :
    base x T τ ≤ base x T τ + d ∧ base x T τ + d < x τ := by
  have := x_top x T τ
  omega

/-- The first visits after `τ` come earlier for higher cells: `D τ z ≤ D τ z' ↔ z' ≤ z`. -/
theorem ladD_le_ladD_iff (hx : IsWalk x) {z z' : ℤ} (hz1 : base x T τ ≤ z) (hz2 : z < x τ)
    (hz1' : base x T τ ≤ z') (hz2' : z' < x τ) : ladD x T τ z ≤ ladD x T τ z' ↔ z' ≤ z := by
  constructor
  · intro h
    by_contra hlt
    have := (ladL_lt_ladL hx hz1 (not_le.mp hlt) hz2').2
    omega
  · exact fun h => (ladL_le_ladL hx hz1' h hz2).2

/-! ### Frames around an excursion -/

/-- `t` is *free* for `τ`: no frame of `τ`, and no frame of a top whose canonical excursion is
nested in that of `τ`, contains `t`. -/
def Free (x : ℕ → ℤ) (T τ t : ℕ) : Prop :=
  ∀ τ' ∈ tops x T, (exc x T τ).1 ≤ (exc x T τ').1 → (exc x T τ').2 ≤ (exc x T τ).2 →
    ∀ G ∈ framesOf x T τ', ¬ (G.1 ≤ t ∧ t < G.2)

theorem free_top (hx : IsWalk x) (hτ : τ ∈ tops x T) : Free x T τ τ :=
  fun _ hτ' h1 h2 _ hG => ladder_time_not_mem_framesOf hx hτ hτ' h1 h2 (Or.inl rfl) hG

theorem free_ladL (hx : IsWalk x) (hτ : τ ∈ tops x T) {z : ℤ} (hz1 : base x T τ ≤ z)
    (hz2 : z < x τ) : Free x T τ (ladL x T τ z) :=
  fun _ hτ' h1 h2 _ hG =>
    ladder_time_not_mem_framesOf hx hτ hτ' h1 h2 (Or.inr ⟨z, hz1, hz2, Or.inl rfl⟩) hG

theorem free_ladD (hx : IsWalk x) (hτ : τ ∈ tops x T) {z : ℤ} (hz1 : base x T τ ≤ z)
    (hz2 : z < x τ) : Free x T τ (ladD x T τ z) :=
  fun _ hτ' h1 h2 _ hG =>
    ladder_time_not_mem_framesOf hx hτ hτ' h1 h2 (Or.inr ⟨z, hz1, hz2, Or.inr rfl⟩) hG

/-- **Frames around an excursion.** Every frame contains the interior `[a + 1, b)` of the canonical
excursion of `τ`, or misses it, or is a frame of a top nested in `τ` (possibly `τ` itself). -/
theorem frame_cases (hx : IsWalk x) (hτ : τ ∈ tops x T) {G : ℕ × ℕ}
    (hG : G ∈ (upperFrames x T hx).frames) :
    (G.1 ≤ (exc x T τ).1 + 1 ∧ (exc x T τ).2 ≤ G.2) ∨ G.2 ≤ (exc x T τ).1 + 1 ∨
      (exc x T τ).2 ≤ G.1 ∨
      ∃ τ' ∈ tops x T, (exc x T τ).1 ≤ (exc x T τ').1 ∧ (exc x T τ').2 ≤ (exc x T τ).2 ∧
        G ∈ framesOf x T τ' := by
  rcases mem_insert.mp hG with rfl | hG
  · exact Or.inl ⟨Nat.zero_le _, (exc_snd_lt hx hτ).le⟩
  obtain ⟨τ', hτ', hGτ'⟩ := mem_suspendFrames.mp hG
  have hb := framesOf_bounds hx hτ' hGτ'
  rcases exc_laminar hx hτ hτ' with h | h | h | h
  · exact Or.inr (Or.inr (Or.inr ⟨τ', hτ', h.1, h.2, hGτ'⟩))
  · by_cases hne : τ' = τ
    · subst hne
      exact Or.inr (Or.inr (Or.inr ⟨τ', hτ', le_rfl, le_rfl, hGτ'⟩))
    obtain ⟨G₀, hG₀, h1, h2⟩ := exists_framesOf_nested hx hτ' hτ hne h.1 h.2
    rcases framesOf_disjoint hx hGτ' hG₀ with rfl | h' | h'
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inl (by omega))

/-- At a free time inside the excursion, the frames containing it are those containing the
interior of the excursion. -/
theorem contains_iff_of_free (hx : IsWalk x) (hτ : τ ∈ tops x T) {t : ℕ}
    (h1 : (exc x T τ).1 < t) (h2 : t < (exc x T τ).2) (hfree : Free x T τ t) {G : ℕ × ℕ}
    (hG : G ∈ (upperFrames x T hx).frames) :
    Contains G t ↔ G.1 ≤ (exc x T τ).1 + 1 ∧ (exc x T τ).2 ≤ G.2 := by
  refine ⟨fun hGt => ?_, fun h => ⟨by omega, by omega⟩⟩
  have hG1 := hGt.1
  have hG2 := hGt.2
  rcases frame_cases hx hτ hG with h | h | h | ⟨τ', hτ', h1', h2', hGτ'⟩
  · exact h
  · omega
  · omega
  · exact absurd ⟨hG1, hG2⟩ (hfree τ' hτ' h1' h2' G hGτ')

/-- The top is an own time of the frame of its excursion, `F = inner τ`. -/
theorem own_inner_top (hx : IsWalk x) (hτ : τ ∈ tops x T) :
    (upperFrames x T hx).Own ((upperFrames x T hx).inner τ) τ :=
  own_inner (show τ < T by have := top_spec hx hτ; omega)

/-- The frame of the excursion contains its interior `[a + 1, b)`. -/
theorem inner_top_bounds (hx : IsWalk x) (hτ : τ ∈ tops x T) :
    ((upperFrames x T hx).inner τ).1 ≤ (exc x T τ).1 + 1 ∧
      (exc x T τ).2 ≤ ((upperFrames x T hx).inner τ).2 :=
  (contains_iff_of_free hx hτ (exc_fst_lt hx hτ) (lt_exc_snd hx hτ) (free_top hx hτ)
    (own_inner_top hx hτ).1).mp (own_inner_top hx hτ).2.1

/-- **Own times.** A free time inside the excursion is an own time of its frame. -/
theorem own_of_free (hx : IsWalk x) (hτ : τ ∈ tops x T) {t : ℕ} (h1 : (exc x T τ).1 < t)
    (h2 : t < (exc x T τ).2) (hfree : Free x T τ t) :
    (upperFrames x T hx).Own ((upperFrames x T hx).inner τ) t :=
  (own_inner_top hx hτ).congr fun _ hG =>
    (contains_iff_of_free hx hτ (exc_fst_lt hx hτ) (lt_exc_snd hx hτ) (free_top hx hτ) hG).trans
      (contains_iff_of_free hx hτ h1 h2 hfree hG).symm

/-- **Own times.** An own time of the frame of the excursion is free. -/
theorem free_of_own (hx : IsWalk x) (hτ : τ ∈ tops x T) {t : ℕ}
    (hown : (upperFrames x T hx).Own ((upperFrames x T hx).inner τ) t) : Free x T τ t := by
  intro τ' hτ' h1' h2' G hG hGt
  have hw := hown.2.2 G (mem_insert_of_mem (mem_suspendFrames.mpr ⟨τ', hτ', hG⟩)) hGt
  have hFb := inner_top_bounds hx hτ
  have hb := framesOf_bounds hx hτ' hG
  have ha := exc_fst_lt hx hτ
  have hb' := lt_exc_snd hx hτ
  unfold Within at hw
  have he : (exc x T τ).1 = (exc x T τ').1 := by omega
  obtain rfl : τ = τ' := top_eq_of_start (exc_mem hx hτ) (exc_mem hx hτ') he
  exact ladder_time_not_mem_framesOf hx hτ hτ le_rfl le_rfl (Or.inl rfl) hG
    ⟨by omega, by omega⟩

/-- Inside the excursion, the innermost frame is that of the excursion, or a frame strictly inside
the excursion. -/
theorem inner_mem_exc (hx : IsWalk x) (hτ : τ ∈ tops x T) {t : ℕ} (h1 : (exc x T τ).1 < t)
    (h2 : t < (exc x T τ).2) :
    (upperFrames x T hx).inner t = (upperFrames x T hx).inner τ ∨
      ((exc x T τ).1 < ((upperFrames x T hx).inner t).1 ∧
        ((upperFrames x T hx).inner t).2 ≤ (exc x T τ).2) := by
  have hown := own_inner (S := upperFrames x T hx)
    (show t < T by have := exc_snd_lt hx hτ; omega)
  have hG1 := hown.2.1.1
  have hG2 := hown.2.1.2
  rcases frame_cases hx hτ hown.1 with h | h | h | ⟨τ', hτ', h1', h2', hGτ'⟩
  · left
    have hF := own_inner_top hx hτ
    have hFb := inner_top_bounds hx hτ
    have ha := exc_fst_lt hx hτ
    have hb := lt_exc_snd hx hτ
    exact within_antisymm (hown.2.2 _ hF.1 ⟨by omega, by omega⟩)
      (hF.2.2 _ hown.1 ⟨by omega, by omega⟩)
  · omega
  · omega
  · right
    have := framesOf_bounds hx hτ' hGτ'
    omega

/-! ### The start of the excursion -/

/-- The walk does not rise into the end of a nonempty suspend frame. -/
theorem x_end_le (hx : IsWalk x) {G : ℕ × ℕ} (hG : G ∈ suspendFrames x T) (hne : G.1 < G.2) :
    x G.2 ≤ x (G.2 - 1) := by
  obtain ⟨τ', hτ', hGτ'⟩ := mem_suspendFrames.mp hG
  obtain ⟨w, hw, rfl | rfl⟩ := mem_framesOf.mp hGτ' <;> obtain ⟨hw1, hw2⟩ := mem_levels.mp hw
  · change ladL x T τ' (w - 1) + 1 < ladL x T τ' w at hne
    change x (ladL x T τ' w) ≤ x (ladL x T τ' w - 1)
    have h1 := ladL_lt hx hw1.le hw2
    have h2 := lt_ladD hx (show base x T τ' ≤ w - 1 by omega) (by omega)
    have := ladL_above hx (show base x T τ' ≤ w - 1 by omega) (by omega)
      (t := ladL x T τ' w - 1) (by omega) (by omega)
    rw [x_ladL hx hw1.le hw2]
    omega
  · change ladD x T τ' w + 1 < ladD x T τ' (w - 1) at hne
    change x (ladD x T τ' (w - 1)) ≤ x (ladD x T τ' (w - 1) - 1)
    have h1 := lt_ladD hx hw1.le hw2
    have h2 := ladL_lt hx (show base x T τ' ≤ w - 1 by omega) (by omega)
    have := ladL_above hx (show base x T τ' ≤ w - 1 by omega) (by omega)
      (t := ladD x T τ' (w - 1) - 1) (by omega) (by omega)
    rw [x_ladD hx (show base x T τ' ≤ w - 1 by omega) (by omega)]
    omega

/-- **Start.** If the frame of the excursion starts at or before `a`, then `a` is an own time of
it. -/
theorem own_exc_fst (hx : IsWalk x) (hτ : τ ∈ tops x T)
    (h : ((upperFrames x T hx).inner τ).1 ≤ (exc x T τ).1) :
    (upperFrames x T hx).Own ((upperFrames x T hx).inner τ) (exc x T τ).1 := by
  have hF := own_inner_top hx hτ
  have hFb := inner_top_bounds hx hτ
  have ha := exc_fst_lt hx hτ
  have hb := lt_exc_snd hx hτ
  refine ⟨hF.1, ⟨h, by omega⟩, fun G hG hGa => ?_⟩
  have hGa1 := hGa.1
  have hGa2 := hGa.2
  rcases frame_cases hx hτ hG with h' | h' | h' | ⟨τ', hτ', h1', h2', hGτ'⟩
  · exact hF.2.2 G hG ⟨by omega, by omega⟩
  · exfalso
    have hG2 : G.2 = (exc x T τ).1 + 1 := by omega
    rcases mem_insert.mp hG with rfl | hGs
    · have := exc_snd_lt hx hτ
      simp only at hG2
      omega
    · have hle := x_end_le hx hGs (by omega)
      rw [hG2, Nat.add_sub_cancel] at hle
      have := (isUpperHop_exc hx hτ).above ((exc x T τ).1 + 1) (by omega) (by omega)
      omega
  · omega
  · have := framesOf_bounds hx hτ' hGτ'
    omega

/-- **Start.** If the frame of the excursion starts before `a`, then `a` is a restart point: it is
not a descent-ladder time strictly inside another excursion. -/
theorem exc_fst_mem_R (hx : IsWalk x) (hτ : τ ∈ tops x T)
    (h : ((upperFrames x T hx).inner τ).1 < (exc x T τ).1) : (exc x T τ).1 ∈ restartPts x T := by
  refine mem_union_right _ (mem_sdiff.mpr ⟨mem_image_of_mem _ hτ, fun hD => ?_⟩)
  obtain ⟨τ'', hτ'', hD⟩ := mem_biUnion.mp hD
  obtain ⟨w, hw, hwa⟩ := mem_image.mp hD
  obtain ⟨hw1, hw2⟩ := mem_levels.mp hw
  have hl1 : (exc x T τ'').1 < τ'' := exc_fst_lt hx hτ''
  have hl2 := lt_ladD hx hw1.le hw2
  have hl3 : ladD x T τ'' w < (exc x T τ'').2 := (ladL_lt_ladL hx le_rfl hw1 hw2).2
  rw [hwa] at hl2 hl3
  have hF := own_inner_top hx hτ
  have ha := exc_fst_lt hx hτ
  have hb := lt_exc_snd hx hτ
  rcases exc_laminar hx hτ hτ'' with h' | h' | h' | h'
  · omega
  · have hne : τ'' ≠ τ := by
      rintro rfl
      omega
    obtain ⟨G₀, hG₀, hG1, hG2⟩ := exists_framesOf_nested hx hτ'' hτ hne h'.1 h'.2
    have hw' := hF.2.2 G₀ (mem_insert_of_mem (mem_suspendFrames.mpr ⟨τ'', hτ'', hG₀⟩))
      ⟨by omega, by omega⟩
    unfold Within at hw'
    exact ladder_time_not_mem_framesOf hx hτ'' hτ'' le_rfl le_rfl
      (Or.inr ⟨w, hw1.le, hw2, Or.inr hwa.symm⟩) hG₀ ⟨by omega, by omega⟩
  · omega
  · omega

/-- The start of the segment of the canonical excursion of `τ` in its frame `F = inner τ`:
`max (F.1, a)`, that is, `a`, or `a + 1` if `F` starts there. -/
noncomputable def excStart (x : ℕ → ℤ) (T : ℕ) (hx : IsWalk x) (τ : ℕ) : ℕ :=
  max ((upperFrames x T hx).inner τ).1 (exc x T τ).1

theorem excStart_bounds (hx : IsWalk x) (hτ : τ ∈ tops x T) :
    (exc x T τ).1 ≤ excStart x T hx τ ∧ excStart x T hx τ ≤ (exc x T τ).1 + 1 := by
  have := inner_top_bounds hx hτ
  unfold excStart
  omega

/-- **Start.** `excStart` is the start of the frame of the excursion or a restart of it. -/
theorem excStart_spec (hx : IsWalk x) (hτ : τ ∈ tops x T) :
    excStart x T hx τ = ((upperFrames x T hx).inner τ).1 ∨
      (excStart x T hx τ ∈ (upperFrames x T hx).R ∧
        ((upperFrames x T hx).inner τ).1 < excStart x T hx τ ∧
        (upperFrames x T hx).Own ((upperFrames x T hx).inner τ) (excStart x T hx τ)) := by
  unfold excStart
  rcases lt_or_ge ((upperFrames x T hx).inner τ).1 (exc x T τ).1 with h | h
  · right
    rw [max_eq_right h.le]
    exact ⟨exc_fst_mem_R hx hτ h, h, own_exc_fst hx hτ h.le⟩
  · exact Or.inl (max_eq_left h)

/-- The home of the excursion's segment: `y` or `y + 1`. -/
theorem x_excStart (hx : IsWalk x) (hτ : τ ∈ tops x T) :
    base x T τ ≤ x (excStart x T hx τ) ∧ x (excStart x T hx τ) ≤ base x T τ + 1 := by
  have hb := excStart_bounds hx hτ
  have hx0 := x_exc_fst hx hτ
  have ha := exc_fst_lt hx hτ
  have hb' := lt_exc_snd hx hτ
  rcases eq_or_lt_of_le hb.1 with h | h
  · rw [← h, hx0]
    omega
  · rw [show excStart x T hx τ = (exc x T τ).1 + 1 by omega]
    have := (isUpperHop_exc hx hτ).above ((exc x T τ).1 + 1) (by omega) (by omega)
    have := (hx.step (exc x T τ).1).1
    omega

/-- **Start.** The frame of the excursion starts at or before `a`, or it is the descent frame of a
top `P` at level `y = base τ` with `D P y = a` (the first excursion of a descent structure; then it
starts at `a + 1`). -/
theorem inner_fst_cases (hx : IsWalk x) (hτ : τ ∈ tops x T) :
    (∃ P ∈ tops x T, base x T τ ∈ levels x T P ∧
        (upperFrames x T hx).inner τ = descFrame x T P (base x T τ) ∧
        ladD x T P (base x T τ) = (exc x T τ).1) ∨
      ((upperFrames x T hx).inner τ).1 ≤ (exc x T τ).1 := by
  rcases le_or_gt ((upperFrames x T hx).inner τ).1 (exc x T τ).1 with h | h
  · exact Or.inr h
  left
  have hF := own_inner_top hx hτ
  have hFb := inner_top_bounds hx hτ
  have hF1 : ((upperFrames x T hx).inner τ).1 = (exc x T τ).1 + 1 := by omega
  rcases mem_insert.mp hF.1 with hroot | hFs
  · rw [hroot] at hF1
    simp only at hF1
    omega
  obtain ⟨P, hP, hFP⟩ := mem_suspendFrames.mp hFs
  obtain ⟨w, hw, hFw⟩ := mem_framesOf.mp hFP
  obtain ⟨hw1, hw2⟩ := mem_levels.mp hw
  rcases hFw with hFw | hFw
  · rw [← hFw] at hF1
    change ladL x T P (w - 1) + 1 = _ at hF1
    have he : ladL x T P (w - 1) = (exc x T τ).1 := by omega
    have hPτ : P = τ :=
      top_eq_of_start (ladL_mem hx (show base x T P ≤ w - 1 by omega) (by omega)) (exc_mem hx hτ) he
    rw [hPτ] at hFP
    exact absurd hF.2.1 (ladder_time_not_mem_framesOf hx hτ hτ le_rfl le_rfl (Or.inl rfl) hFP)
  · rw [← hFw] at hF1
    change ladD x T P w + 1 = _ at hF1
    have he : ladD x T P w = (exc x T τ).1 := by omega
    have hwy : w = base x T τ := by
      rw [← x_ladD hx hw1.le hw2, he, x_exc_fst hx hτ]
    subst hwy
    exact ⟨P, hP, hw, hFw.symm, he⟩

/-- **End.** The frame of the excursion ends after `b`, or it is the hanging frame of a top `P` at
level `y = base τ` with `L P y = b` (the last excursion of a hanging structure; then it ends at
`b`). -/
theorem inner_snd_cases (hx : IsWalk x) (hτ : τ ∈ tops x T) :
    (∃ P ∈ tops x T, base x T τ ∈ levels x T P ∧
        (upperFrames x T hx).inner τ = hangFrame x T P (base x T τ) ∧
        ladL x T P (base x T τ) = (exc x T τ).2) ∨
      (exc x T τ).2 < ((upperFrames x T hx).inner τ).2 := by
  rcases lt_or_ge (exc x T τ).2 ((upperFrames x T hx).inner τ).2 with h | h
  · exact Or.inr h
  left
  have hF := own_inner_top hx hτ
  have hFb := inner_top_bounds hx hτ
  have hF2 : ((upperFrames x T hx).inner τ).2 = (exc x T τ).2 := by omega
  rcases mem_insert.mp hF.1 with hroot | hFs
  · rw [hroot] at hF2
    simp only at hF2
    have := exc_snd_lt hx hτ
    omega
  obtain ⟨P, hP, hFP⟩ := mem_suspendFrames.mp hFs
  obtain ⟨w, hw, hFw⟩ := mem_framesOf.mp hFP
  obtain ⟨hw1, hw2⟩ := mem_levels.mp hw
  rcases hFw with hFw | hFw
  · rw [← hFw] at hF2
    change ladL x T P w = _ at hF2
    have hwy : w = base x T τ := by
      rw [← x_ladL hx hw1.le hw2, hF2]
      exact x_ladD hx le_rfl (base_lt hτ)
    subst hwy
    exact ⟨P, hP, hw, hFw.symm, hF2⟩
  · rw [← hFw] at hF2
    change ladD x T P (w - 1) = _ at hF2
    have hPτ : P = τ :=
      top_eq_of_end (ladL_mem hx (show base x T P ≤ w - 1 by omega) (by omega)) (exc_mem hx hτ) hF2
    rw [hPτ] at hFP
    exact absurd hF.2.1 (ladder_time_not_mem_framesOf hx hτ hτ le_rfl le_rfl (Or.inl rfl) hFP)

/-! ### Restarts inside the excursion -/

/-- The passages of `τ` are the times `D τ (y + 2^e)` with `2^e < H`. -/
theorem mem_passages {P : ℕ} : P ∈ passages x T τ ↔
    ∃ e, 2 ^ e < height x T τ ∧ P = ladD x T τ (base x T τ + ((2 ^ e : ℕ) : ℤ)) := by
  simp only [passages, mem_image, mem_filter, mem_range, Nat.cast_pow, Nat.cast_ofNat]
  constructor
  · rintro ⟨e, ⟨-, he⟩, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, ⟨Nat.lt_two_pow_self.trans he, he⟩, rfl⟩

/-- A passage of `τ` is a free descent-ladder time after `τ` and a restart point. -/
theorem passage_spec (hx : IsWalk x) (hτ : τ ∈ tops x T) {P : ℕ} (hP : P ∈ passages x T τ) :
    τ < P ∧ P < (exc x T τ).2 ∧ P ∈ restartPts x T ∧ Free x T τ P := by
  obtain ⟨e, he, rfl⟩ := mem_passages.mp hP
  have hpos := Nat.two_pow_pos e
  obtain ⟨hz1, hz2⟩ := cell_bounds (x := x) (T := T) (τ := τ) he
  refine ⟨lt_ladD hx hz1 hz2, (ladL_lt_ladL hx le_rfl (by omega) hz2).2,
    mem_union_left _ (mem_biUnion.mpr ⟨τ, hτ, hP⟩), free_ladD hx hτ hz1 hz2⟩

/-- **Restarts inside.** A free restart point strictly inside the excursion is a passage. -/
theorem restart_inside (hx : IsWalk x) (hτ : τ ∈ tops x T) {t : ℕ} (h1 : (exc x T τ).1 < t)
    (h2 : t < (exc x T τ).2) (hfree : Free x T τ t) (hR : t ∈ restartPts x T) :
    t ∈ passages x T τ := by
  rcases mem_union.mp hR with hP | hS
  · obtain ⟨τ'', hτ'', hP⟩ := mem_biUnion.mp hP
    by_cases hne : τ'' = τ
    · rwa [hne] at hP
    exfalso
    obtain ⟨e, he, rfl⟩ := mem_passages.mp hP
    have hpos := Nat.two_pow_pos e
    obtain ⟨hc1, hc2⟩ := cell_bounds (x := x) (T := T) (τ := τ'') he
    have i1 : (exc x T τ'').1 < ladD x T τ'' (base x T τ'' + ((2 ^ e : ℕ) : ℤ)) :=
      (exc_fst_lt hx hτ'').trans (lt_ladD hx hc1 hc2)
    have i2 : ladD x T τ'' (base x T τ'' + ((2 ^ e : ℕ) : ℤ)) < (exc x T τ'').2 :=
      (ladL_lt_ladL hx le_rfl (by omega) hc2).2
    rcases exc_laminar hx hτ hτ'' with h' | h' | h' | h'
    · obtain ⟨G, hG, hG1, hG2⟩ := exists_framesOf_nested hx hτ hτ'' (Ne.symm hne) h'.1 h'.2
      exact hfree τ hτ le_rfl le_rfl G hG ⟨by omega, by omega⟩
    · obtain ⟨G₀, hG₀, hG1, hG2⟩ := exists_framesOf_nested hx hτ'' hτ hne h'.1 h'.2
      exact ladder_time_not_mem_framesOf hx hτ'' hτ'' le_rfl le_rfl
        (Or.inr ⟨_, hc1, hc2, Or.inr rfl⟩) hG₀ ⟨by omega, by omega⟩
    · omega
    · omega
  · exfalso
    obtain ⟨hI, hnD⟩ := mem_sdiff.mp hS
    obtain ⟨τ'', hτ'', rfl⟩ := mem_image.mp hI
    have hl := (isUpperHop_exc hx hτ'').long
    rcases exc_laminar hx hτ hτ'' with h' | h' | h' | h'
    · by_cases hne : τ = τ''
      · subst hne
        omega
      obtain ⟨w, hw, -, ⟨-, hl1, hl2⟩ | ⟨-, hl1, hl2⟩⟩ := exc_structure hx hτ hτ'' hne h'.1 h'.2
      · exact hfree τ hτ le_rfl le_rfl (hangFrame x T τ w) (mem_framesOf.mpr ⟨w, hw, Or.inl rfl⟩)
          ⟨hl1, show _ < ladL x T τ w by omega⟩
      · rcases eq_or_lt_of_le hl1 with heq | hlt
        · exact hnD (mem_biUnion.mpr ⟨τ, hτ, mem_image.mpr ⟨w, hw, heq⟩⟩)
        · exact hfree τ hτ le_rfl le_rfl (descFrame x T τ w)
            (mem_framesOf.mpr ⟨w, hw, Or.inr rfl⟩)
            ⟨show ladD x T τ w + 1 ≤ _ by omega, show _ < ladD x T τ (w - 1) by omega⟩
    · omega
    · omega
    · omega

/-! ### Segment starts -/

/-- **Segment starts.** Before the first passage, the segment of the frame of the excursion starts
at `excStart`. -/
theorem segStart_eq_excStart (hx : IsWalk x) (hτ : τ ∈ tops x T) {t : ℕ}
    (h1 : excStart x T hx τ ≤ t) (h2 : t < (exc x T τ).2) (hP : ∀ P ∈ passages x T τ, t < P) :
    (upperFrames x T hx).segStart ((upperFrames x T hx).inner τ) t = excStart x T hx τ := by
  have hb := excStart_bounds hx hτ
  refine segStart_eq (excStart_spec hx hτ) h1 fun s hs hlt hle hown => ?_
  have := hP s (restart_inside hx hτ (by omega) (by omega) (free_of_own hx hτ hown) hs)
  omega

/-- **Segment starts.** From a passage `P` to the next one, the segment of the frame of the
excursion starts at `P`. -/
theorem segStart_eq_passage (hx : IsWalk x) (hτ : τ ∈ tops x T) {t P : ℕ}
    (hP : P ∈ passages x T τ) (h1 : P ≤ t) (h2 : t < (exc x T τ).2)
    (hlast : ∀ P' ∈ passages x T τ, P < P' → t < P') :
    (upperFrames x T hx).segStart ((upperFrames x T hx).inner τ) t = P := by
  obtain ⟨hτP, hPb, hPR, hPf⟩ := passage_spec hx hτ hP
  have hFb := inner_top_bounds hx hτ
  have ha := exc_fst_lt hx hτ
  refine segStart_eq (Or.inr ⟨hPR, by omega, own_of_free hx hτ (by omega) hPb hPf⟩) h1
    fun s hs hlt hle hown => ?_
  have := hlast s (restart_inside hx hτ (by omega) (by omega) (free_of_own hx hτ hown) hs) hlt
  omega

/-- **Segment starts.** At `D τ (y + d)`, `1 ≤ d < H`, with `e = ⌈log₂ d⌉` and `2^e < H`, the
segment starts at the passage `D τ (y + 2^e)`. -/
theorem segStart_ladD (hx : IsWalk x) (hτ : τ ∈ tops x T) {d : ℕ} (hd1 : 1 ≤ d)
    (hdH : d < height x T τ) (hpass : 2 ^ Nat.clog 2 d < height x T τ) :
    (upperFrames x T hx).segStart ((upperFrames x T hx).inner τ) (ladD x T τ (base x T τ + d)) =
      ladD x T τ (base x T τ + ((2 ^ Nat.clog 2 d : ℕ) : ℤ)) := by
  have hdc : d ≤ 2 ^ Nat.clog 2 d := Nat.le_pow_clog (by norm_num) d
  obtain ⟨hz1, hz2⟩ := cell_bounds (x := x) (T := T) (τ := τ) hdH
  obtain ⟨hc1, hc2⟩ := cell_bounds (x := x) (T := T) (τ := τ) hpass
  refine segStart_eq_passage hx hτ (mem_passages.mpr ⟨_, hpass, rfl⟩)
    ((ladD_le_ladD_iff hx hc1 hc2 hz1 hz2).mpr (by omega))
    (ladL_lt_ladL hx le_rfl (by omega) hz2).2 fun P' hP' hlt => ?_
  obtain ⟨e', he', rfl⟩ := mem_passages.mp hP'
  obtain ⟨hc1', hc2'⟩ := cell_bounds (x := x) (T := T) (τ := τ) he'
  by_contra hle
  have h1 := (ladD_le_ladD_iff hx hc1' hc2' hz1 hz2).mp (not_lt.mp hle)
  have h2 := (ladD_le_ladD_iff hx hc1 hc2 hc1' hc2').mp hlt.le
  have h3 : Nat.clog 2 d ≤ e' := Nat.clog_le_of_le_pow (by omega)
  have h4 : 2 ^ Nat.clog 2 d ≤ 2 ^ e' := Nat.pow_le_pow_right (by norm_num) h3
  have h5 : 2 ^ e' ≤ 2 ^ Nat.clog 2 d := by omega
  have h6 : 2 ^ e' = 2 ^ Nat.clog 2 d := le_antisymm h5 h4
  rw [h6] at hlt
  exact lt_irrefl _ hlt

/-- **Segment starts.** At `D τ (y + d)`, `1 ≤ d < H`, above the top passage (`2^⌈log₂ d⌉ ≥ H`),
the segment starts at `excStart`. -/
theorem segStart_ladD_of_not (hx : IsWalk x) (hτ : τ ∈ tops x T) {d : ℕ} (hd1 : 1 ≤ d)
    (hdH : d < height x T τ) (hpass : ¬ 2 ^ Nat.clog 2 d < height x T τ) :
    (upperFrames x T hx).segStart ((upperFrames x T hx).inner τ) (ladD x T τ (base x T τ + d)) =
      excStart x T hx τ := by
  obtain ⟨hz1, hz2⟩ := cell_bounds (x := x) (T := T) (τ := τ) hdH
  have hτD := lt_ladD hx hz1 hz2
  have hb := excStart_bounds hx hτ
  have ha := exc_fst_lt hx hτ
  refine segStart_eq_excStart hx hτ (by omega) (ladL_lt_ladL hx le_rfl (by omega) hz2).2
    fun P' hP' => ?_
  obtain ⟨e', he', rfl⟩ := mem_passages.mp hP'
  obtain ⟨hc1', hc2'⟩ := cell_bounds (x := x) (T := T) (τ := τ) he'
  by_contra hle
  have h1 := (ladD_le_ladD_iff hx hc1' hc2' hz1 hz2).mp (not_lt.mp hle)
  have h3 : Nat.clog 2 d ≤ e' := Nat.clog_le_of_le_pow (by omega)
  have h4 : 2 ^ Nat.clog 2 d ≤ 2 ^ e' := Nat.pow_le_pow_right (by norm_num) h3
  omega

/-- Inside the excursion the segment of the innermost frame starts in `[a, t]`. -/
theorem segStart_inner_mem (hx : IsWalk x) (hτ : τ ∈ tops x T) {t : ℕ}
    (h1 : (exc x T τ).1 < t) (h2 : t < (exc x T τ).2) :
    (exc x T τ).1 ≤ (upperFrames x T hx).segStart ((upperFrames x T hx).inner t) t ∧
      (upperFrames x T hx).segStart ((upperFrames x T hx).inner t) t ≤ t := by
  have hown := own_inner (S := upperFrames x T hx)
    (show t < T by have := exc_snd_lt hx hτ; omega)
  refine ⟨?_, segStart_le (S := upperFrames x T hx) hown.2.1.1⟩
  rcases inner_mem_exc hx hτ h1 h2 with h | h
  · rw [h]
    have hb := excStart_bounds hx hτ
    exact hb.1.trans (le_segStart (excStart_spec hx hτ) (by omega))
  · exact h.1.le.trans (start_le_segStart _ _)

/-- **End.** If the frame of the excursion ends after `b`, the innermost frame at `b` is that frame
or a frame starting at `b`. -/
theorem inner_exc_snd (hx : IsWalk x) (hτ : τ ∈ tops x T)
    (h : (exc x T τ).2 < ((upperFrames x T hx).inner τ).2) :
    (upperFrames x T hx).inner (exc x T τ).2 = (upperFrames x T hx).inner τ ∨
      ((upperFrames x T hx).inner (exc x T τ).2).1 = (exc x T τ).2 := by
  have hown := own_inner (S := upperFrames x T hx) (t := (exc x T τ).2) (exc_snd_lt hx hτ)
  have hG1 := hown.2.1.1
  have hG2 := hown.2.1.2
  have ha := exc_fst_lt hx hτ
  have hb := lt_exc_snd hx hτ
  rcases frame_cases hx hτ hown.1 with h' | h' | h' | ⟨τ', hτ', h1', h2', hGτ'⟩
  · left
    have hF := own_inner_top hx hτ
    have hFb := inner_top_bounds hx hτ
    exact within_antisymm (hown.2.2 _ hF.1 ⟨by omega, by omega⟩)
      (hF.2.2 _ hown.1 ⟨by omega, by omega⟩)
  · omega
  · right
    omega
  · have := framesOf_bounds hx hτ' hGτ'
    omega

/-- If the frame of the excursion starts at or before `a` and ends after `b`, the segment of the
innermost frame at any `c ∈ [a, b]` starts in `[a, c]`. -/
theorem segStart_inner_mem_Icc (hx : IsWalk x) (hτ : τ ∈ tops x T)
    (hF1 : ((upperFrames x T hx).inner τ).1 ≤ (exc x T τ).1)
    (hF2 : (exc x T τ).2 < ((upperFrames x T hx).inner τ).2) {c : ℕ} (hc1 : (exc x T τ).1 ≤ c)
    (hc2 : c ≤ (exc x T τ).2) :
    (exc x T τ).1 ≤ (upperFrames x T hx).segStart ((upperFrames x T hx).inner c) c ∧
      (upperFrames x T hx).segStart ((upperFrames x T hx).inner c) c ≤ c := by
  have hown := own_inner (S := upperFrames x T hx)
    (show c < T by have := exc_snd_lt hx hτ; omega)
  refine ⟨?_, segStart_le (S := upperFrames x T hx) hown.2.1.1⟩
  have hb := excStart_bounds hx hτ
  have hsE : excStart x T hx τ = (exc x T τ).1 := max_eq_right hF1
  rcases eq_or_lt_of_le hc1 with rfl | hc1
  · rw [inner_eq (own_exc_fst hx hτ hF1)]
    exact hsE.symm.le.trans (le_segStart (excStart_spec hx hτ) (by omega))
  rcases eq_or_lt_of_le hc2 with rfl | hc2
  · rcases inner_exc_snd hx hτ hF2 with h | h
    · rw [h]
      exact hb.1.trans (le_segStart (excStart_spec hx hτ) (by omega))
    · have := start_le_segStart (S := upperFrames x T hx)
        ((upperFrames x T hx).inner (exc x T τ).2) (exc x T τ).2
      rw [h] at this
      omega
  · exact (segStart_inner_mem hx hτ hc1 hc2).1

/-! ### Bands at ladder times -/

/-- If the segment of the innermost frame at `c ≤ b` starts in the excursion, the running maximum is
at most the height. -/
theorem runMax_le_height (hx : IsWalk x) (hτ : τ ∈ tops x T) {c : ℕ}
    (h1 : (exc x T τ).1 ≤ (upperFrames x T hx).segStart ((upperFrames x T hx).inner c) c)
    (h2 : c ≤ (exc x T τ).2) :
    (upperFrames x T hx).runMax ((upperFrames x T hx).inner c) c ≤ height x T τ := by
  have hle := segStart_le (S := upperFrames x T hx) (own_inner (S := upperFrames x T hx)
    (show c < T by have := exc_snd_lt hx hτ; omega)).2.1.1
  refine runMax_le fun t' _ ht1 ht2 => ?_
  have r1 := exc_range hx hτ (t := t') (by omega) (by omega)
  have r2 := exc_range hx hτ h1 (hle.trans h2)
  have := x_top x T τ
  rw [upperFrames_x]
  omega

/-- **Homes.** Every home active strictly inside the excursion lies in `[y, x τ]`. -/
theorem home_mem_exc (hx : IsWalk x) (hτ : τ ∈ tops x T) {t : ℕ} (h1 : (exc x T τ).1 < t)
    (h2 : t < (exc x T τ).2) :
    base x T τ ≤ (upperFrames x T hx).home t ∧ (upperFrames x T hx).home t ≤ x τ := by
  obtain ⟨hs1, hs2⟩ := segStart_inner_mem hx hτ h1 h2
  exact exc_range hx hτ hs1 (by omega)

/-- Strictly inside the excursion the band is at most `band H`. -/
theorem beta_le_band_height (hx : IsWalk x) (hτ : τ ∈ tops x T) {t : ℕ}
    (h1 : (exc x T τ).1 < t) (h2 : t < (exc x T τ).2) :
    (upperFrames x T hx).beta t ≤ band (height x T τ) :=
  band_mono (runMax_le_height hx hτ (segStart_inner_mem hx hτ h1 h2).1 h2.le)

/-- **The climb.** At `L τ (y + d)`, `1 ≤ d < H`, the band is between `band (d − 1)` and
`band H`. -/
theorem beta_ladL_bounds (hx : IsWalk x) (hτ : τ ∈ tops x T) {d : ℕ} (hd1 : 1 ≤ d)
    (hdH : d < height x T τ) :
    band (d - 1) ≤ (upperFrames x T hx).beta (ladL x T τ (base x T τ + d)) ∧
      (upperFrames x T hx).beta (ladL x T τ (base x T τ + d)) ≤ band (height x T τ) := by
  obtain ⟨hz1, hz2⟩ := cell_bounds (x := x) (T := T) (τ := τ) hdH
  have hL := ladL_lt_ladL hx le_rfl (show base x T τ < base x T τ + d by omega) hz2
  have hL1 : (exc x T τ).1 < ladL x T τ (base x T τ + d) := hL.1
  have hLτ := ladL_lt hx hz1 hz2
  have hτb := lt_exc_snd hx hτ
  refine ⟨?_, beta_le_band_height hx hτ hL1 (by omega)⟩
  have hown := own_of_free hx hτ hL1 (by omega) (free_ladL hx hτ hz1 hz2)
  have hb := excStart_bounds hx hτ
  have hseg := segStart_eq_excStart hx hτ (t := ladL x T τ (base x T τ + d)) (by omega) (by omega)
    fun P hP => hLτ.trans (passage_spec hx hτ hP).1
  have hdist := band_dist_home_le_beta (S := upperFrames x T hx)
    (t := ladL x T τ (base x T τ + d)) (show _ < T by have := exc_snd_lt hx hτ; omega)
  have hhome : (upperFrames x T hx).home (ladL x T τ (base x T τ + d)) =
      x (excStart x T hx τ) := by
    unfold FrameSystem.home
    rw [inner_eq hown, hseg]
    rfl
  rw [hhome, upperFrames_x, x_ladL hx hz1 hz2] at hdist
  refine (band_mono ?_).trans hdist
  have := x_excStart hx hτ
  omega

/-- **The descent.** At `D τ (y + d)`, `1 ≤ d < H`, the band is between `uband H d` and
`band H`: below the top passage the segment started at the passage `D τ (y + 2^⌈log₂ d⌉)`, above it
at `excStart`, and the running maximum has passed `τ`. -/
theorem beta_ladD_bounds (hx : IsWalk x) (hτ : τ ∈ tops x T) {d : ℕ} (hd1 : 1 ≤ d)
    (hdH : d < height x T τ) :
    uband (height x T τ) d ≤ (upperFrames x T hx).beta (ladD x T τ (base x T τ + d)) ∧
      (upperFrames x T hx).beta (ladD x T τ (base x T τ + d)) ≤ band (height x T τ) := by
  obtain ⟨hz1, hz2⟩ := cell_bounds (x := x) (T := T) (τ := τ) hdH
  have hD : ladD x T τ (base x T τ + d) < (exc x T τ).2 :=
    (ladL_lt_ladL hx le_rfl (show base x T τ < base x T τ + d by omega) hz2).2
  have hτD := lt_ladD hx hz1 hz2
  have ha := exc_fst_lt hx hτ
  refine ⟨?_, beta_le_band_height hx hτ (by omega) hD⟩
  have hown := own_of_free hx hτ (by omega) hD (free_ladD hx hτ hz1 hz2)
  have hDT : ladD x T τ (base x T τ + d) < T := by have := exc_snd_lt hx hτ; omega
  unfold uband
  split_ifs with hpass
  · have hp : 2 ^ Nat.clog 2 d < height x T τ := by omega
    have hdc : d ≤ 2 ^ Nat.clog 2 d := Nat.le_pow_clog (by norm_num) d
    obtain ⟨hc1, hc2⟩ := cell_bounds (x := x) (T := T) (τ := τ) hp
    have hdist := band_dist_home_le_beta (S := upperFrames x T hx) hDT
    have hhome : (upperFrames x T hx).home (ladD x T τ (base x T τ + d)) =
        base x T τ + ((2 ^ Nat.clog 2 d : ℕ) : ℤ) := by
      unfold FrameSystem.home
      rw [inner_eq hown, segStart_ladD hx hτ hd1 hdH hp]
      exact x_ladD hx hc1 hc2
    rw [hhome, upperFrames_x, x_ladD hx hz1 hz2] at hdist
    refine (band_mono ?_).trans hdist
    omega
  · have hseg := segStart_ladD_of_not hx hτ hd1 hdH (by omega)
    have hb := excStart_bounds hx hτ
    have hle := le_runMax (S := upperFrames x T hx) (own_inner_top hx hτ)
      (t := ladD x T τ (base x T τ + d)) (by rw [hseg]; omega) hτD.le
    rw [hseg, upperFrames_x] at hle
    unfold FrameSystem.beta
    rw [inner_eq hown]
    refine band_mono (le_trans ?_ hle)
    have := x_excStart hx hτ
    have := x_top x T τ
    omega

/-- **Eventfulness below the top passage.** At `D τ (y + d)` with `2^⌈log₂ d⌉ < H`, the segment
started after `L τ (y + d)`. -/
theorem ladL_lt_segStart_ladD (hx : IsWalk x) (hτ : τ ∈ tops x T) {d : ℕ} (hd1 : 1 ≤ d)
    (hdH : d < height x T τ) (hpass : 2 ^ Nat.clog 2 d < height x T τ) :
    ladL x T τ (base x T τ + d) < (upperFrames x T hx).segStart
      ((upperFrames x T hx).inner (ladD x T τ (base x T τ + d))) (ladD x T τ (base x T τ + d)) := by
  obtain ⟨hz1, hz2⟩ := cell_bounds (x := x) (T := T) (τ := τ) hdH
  obtain ⟨hc1, hc2⟩ := cell_bounds (x := x) (T := T) (τ := τ) hpass
  have hD : ladD x T τ (base x T τ + d) < (exc x T τ).2 :=
    (ladL_lt_ladL hx le_rfl (show base x T τ < base x T τ + d by omega) hz2).2
  have hown := own_of_free hx hτ (by have := exc_fst_lt hx hτ; have := lt_ladD hx hz1 hz2; omega)
    hD (free_ladD hx hτ hz1 hz2)
  rw [inner_eq hown, segStart_ladD hx hτ hd1 hdH hpass]
  exact (ladL_lt hx hz1 hz2).trans (lt_ladD hx hc1 hc2)

/-! ### Lemma W2: every suspend frame ends at band `0`

A *frame of `τ'` at level `w`* is its hanging frame `[L (w − 1) + 1, L w)` or its descent frame
`[D w + 1, D (w − 1))`, for a level `w` of `τ'`. On it the walk is at least `w`; the excursions of
its closed structure have base `w` (`struct_exc`), and a time at level `w` is an own time of it
(`own_of_le_level`). -/

/-- A restart point is a passage, a descent-ladder time `D τ'' z` above the base of `τ''`, or it is
left by an up-step (an excursion start). -/
theorem restartPts_cases (hx : IsWalk x) {s : ℕ} (hs : s ∈ restartPts x T) :
    (∃ τ'' ∈ tops x T, ∃ z, base x T τ'' < z ∧ z < x τ'' ∧ s = ladD x T τ'' z) ∨
      x s < x (s + 1) := by
  rcases mem_union.mp hs with hP | hS
  · obtain ⟨τ'', hτ'', hP⟩ := mem_biUnion.mp hP
    obtain ⟨e, he, rfl⟩ := mem_passages.mp hP
    have hpos := Nat.two_pow_pos e
    obtain ⟨-, hc2⟩ := cell_bounds (x := x) (T := T) (τ := τ'') he
    exact Or.inl ⟨τ'', hτ'', _, by omega, hc2, rfl⟩
  · obtain ⟨hI, -⟩ := mem_sdiff.mp hS
    obtain ⟨τ'', hτ'', rfl⟩ := mem_image.mp hI
    have hl := (isUpperHop_exc hx hτ'').long
    exact Or.inr ((isUpperHop_exc hx hτ'').above _ (by omega) (by omega))

section Levels

variable {τ' : ℕ} {w : ℤ} {G : ℕ × ℕ}

theorem frameAt_mem (hw : w ∈ levels x T τ')
    (hG : G = hangFrame x T τ' w ∨ G = descFrame x T τ' w) : G ∈ framesOf x T τ' :=
  mem_framesOf.mpr ⟨w, hw, hG.imp Eq.symm Eq.symm⟩

/-- On a frame of level `w` the walk is at least `w`; just before its start and at its end it is at
most `w`. -/
theorem frameAt_walk (hx : IsWalk x) (hw : w ∈ levels x T τ')
    (hG : G = hangFrame x T τ' w ∨ G = descFrame x T τ' w) :
    (∀ t, G.1 ≤ t → t < G.2 → w ≤ x t) ∧ 1 ≤ G.1 ∧ x (G.1 - 1) ≤ w ∧ x G.2 ≤ w := by
  obtain ⟨hw1, hw2⟩ := mem_levels.mp hw
  have hc1 : base x T τ' ≤ w - 1 := by omega
  have hc2 : w - 1 < x τ' := by omega
  have hL := ladL_lt hx hc1 hc2
  have hD := lt_ladD hx hc1 hc2
  rcases hG with rfl | rfl
  · have hLw := ladL_lt hx hw1.le hw2
    refine ⟨fun t ht1 ht2 => ?_, ?_, ?_, ?_⟩
    · change ladL x T τ' (w - 1) + 1 ≤ t at ht1
      change t < ladL x T τ' w at ht2
      have := ladL_above hx hc1 hc2 (t := t) (by omega) (by omega)
      omega
    · show 1 ≤ ladL x T τ' (w - 1) + 1
      omega
    · show x (ladL x T τ' (w - 1) + 1 - 1) ≤ w
      rw [Nat.add_sub_cancel, x_ladL hx hc1 hc2]
      omega
    · exact (x_ladL hx hw1.le hw2).le
  · have hDw := lt_ladD hx hw1.le hw2
    refine ⟨fun t ht1 ht2 => ?_, ?_, ?_, ?_⟩
    · change ladD x T τ' w + 1 ≤ t at ht1
      change t < ladD x T τ' (w - 1) at ht2
      have := ladL_above hx hc1 hc2 (t := t) (by omega) (by omega)
      omega
    · show 1 ≤ ladD x T τ' w + 1
      omega
    · show x (ladD x T τ' w + 1 - 1) ≤ w
      rw [Nat.add_sub_cancel]
      exact (x_ladD hx hw1.le hw2).le
    · show x (ladD x T τ' (w - 1)) ≤ w
      rw [x_ladD hx hc1 hc2]
      omega

/-- The level of a frame is unique. -/
theorem frameAt_level_unique (hx : IsWalk x) {w' : ℤ} (hw : w ∈ levels x T τ')
    (hw' : w' ∈ levels x T τ') (hG : G = hangFrame x T τ' w ∨ G = descFrame x T τ' w)
    (hG' : G = hangFrame x T τ' w' ∨ G = descFrame x T τ' w') : w = w' := by
  obtain ⟨hw1, hw2⟩ := mem_levels.mp hw
  obtain ⟨hw1', hw2'⟩ := mem_levels.mp hw'
  rcases hG with rfl | rfl <;> rcases hG' with h | h <;> have h2 := congrArg Prod.snd h
  · change ladL x T τ' w = ladL x T τ' w' at h2
    have e1 := x_ladL hx hw1.le hw2
    rw [h2, x_ladL hx hw1'.le hw2'] at e1
    exact e1.symm
  · change ladL x T τ' w = ladD x T τ' (w' - 1) at h2
    have := ladL_lt hx hw1.le hw2
    have := lt_ladD hx (show base x T τ' ≤ w' - 1 by omega) (by omega)
    omega
  · change ladD x T τ' (w - 1) = ladL x T τ' w' at h2
    have := ladL_lt hx hw1'.le hw2'
    have := lt_ladD hx (show base x T τ' ≤ w - 1 by omega) (by omega)
    omega
  · change ladD x T τ' (w - 1) = ladD x T τ' (w' - 1) at h2
    have e1 := x_ladD hx (show base x T τ' ≤ w - 1 by omega) (show w - 1 < x τ' by omega)
    rw [h2, x_ladD hx (show base x T τ' ≤ w' - 1 by omega) (show w' - 1 < x τ' by omega)] at e1
    omega

/-- A top nested in `τ'` whose canonical excursion has a time of a frame of `τ'` of level `w`
strictly inside has base at least `w` (its excursion lies in the closed structure of that frame). -/
theorem level_le_base (hx : IsWalk x) (hτ' : τ' ∈ tops x T) (hw : w ∈ levels x T τ')
    (hG : G = hangFrame x T τ' w ∨ G = descFrame x T τ' w) {τ'' : ℕ} (hτ'' : τ'' ∈ tops x T)
    (hne : τ' ≠ τ'') (h1 : (exc x T τ').1 ≤ (exc x T τ'').1)
    (h2 : (exc x T τ'').2 ≤ (exc x T τ').2) {t : ℕ} (ht1 : G.1 ≤ t) (ht2 : t < G.2)
    (ht3 : (exc x T τ'').1 < t) (ht4 : t < (exc x T τ'').2) : w ≤ base x T τ'' := by
  obtain ⟨w'', hw'', hwb, hs⟩ := exc_structure hx hτ' hτ'' hne h1 h2
  have key : ∃ G'' : ℕ × ℕ, (G'' = hangFrame x T τ' w'' ∨ G'' = descFrame x T τ' w'') ∧
      G''.1 ≤ t ∧ t < G''.2 := by
    rcases hs with ⟨-, hl1, hl2⟩ | ⟨-, hl1, hl2⟩
    · exact ⟨_, Or.inl rfl, show ladL x T τ' (w'' - 1) + 1 ≤ t by omega,
        show t < ladL x T τ' w'' by omega⟩
    · exact ⟨_, Or.inr rfl, show ladD x T τ' w'' + 1 ≤ t by omega,
        show t < ladD x T τ' (w'' - 1) by omega⟩
  obtain ⟨G'', hG'', h''1, h''2⟩ := key
  rcases framesOf_disjoint hx (frameAt_mem hw hG) (frameAt_mem hw'' hG'') with he | he | he
  · rw [← he] at hG''
    have := frameAt_level_unique hx hw hw'' hG hG''
    omega
  · omega
  · omega

/-- A time of a frame of level `w` at which the walk is at most `w` is an own time of the frame. -/
theorem own_of_le_level (hx : IsWalk x) (hτ' : τ' ∈ tops x T) (hw : w ∈ levels x T τ')
    (hG : G = hangFrame x T τ' w ∨ G = descFrame x T τ' w) {t : ℕ} (ht1 : G.1 ≤ t)
    (ht2 : t < G.2) (hxt : x t ≤ w) : (upperFrames x T hx).Own G t := by
  have hGm := frameAt_mem hw hG
  have hGb := framesOf_bounds hx hτ' hGm
  refine ⟨mem_insert_of_mem (mem_suspendFrames.mpr ⟨τ', hτ', hGm⟩), ⟨ht1, ht2⟩,
    fun G'' hG'' hG''t => ?_⟩
  have h''1 := hG''t.1
  have h''2 := hG''t.2
  rcases frame_cases hx hτ' hG'' with h | h | h | ⟨τ'', hτ'', h1, h2, hG''τ''⟩
  · exact ⟨by omega, by omega⟩
  · omega
  · omega
  · by_cases hne : τ' = τ''
    · rw [← hne] at hG''τ''
      rcases framesOf_disjoint hx hGm hG''τ'' with he | he | he
      · rw [← he]
        exact ⟨le_rfl, le_rfl⟩
      · omega
      · omega
    · have hb'' := framesOf_bounds hx hτ'' hG''τ''
      have := level_le_base hx hτ' hw hG hτ'' hne h1 h2 ht1 ht2 (by omega) (by omega)
      have := base_lt_of_mem hx hτ'' (t := t) (by omega) (by omega)
      omega

/-- **The excursions of a structure.** An upper hop `(p, q)` of cell `w` in the closed structure of
a frame `G` of `τ'` of level `w` is the canonical excursion of its top, whose base is `w` and whose
frame is `G`. -/
theorem struct_exc (hx : IsWalk x) (hτ' : τ' ∈ tops x T) (hw : w ∈ levels x T τ')
    (hG : G = hangFrame x T τ' w ∨ G = descFrame x T τ' w) {p q : ℕ}
    (hpq : (p, q) ∈ upperHops x T) (hxp : x p = w) (hp : G.1 ≤ p + 1) (hq : q ≤ G.2) :
    hopOwner x p q ∈ tops x T ∧ exc x T (hopOwner x p q) = (p, q) ∧
      base x T (hopOwner x p q) = w ∧ (upperFrames x T hx).inner (hopOwner x p q) = G := by
  have hlad : (p, q) ∈ ladder x T (hopOwner x p q) := mem_ladder_hopOwner hpq
  have hE : hopOwner x p q ∈ tops x T := mem_tops.mpr ⟨_, hlad⟩
  generalize hopOwner x p q = τE at hE hlad ⊢
  have hGm := frameAt_mem hw hG
  have hGb := framesOf_bounds hx hτ' hGm
  have hlt : p < τE ∧ τE < q := ladder_lt hlad
  have hτ'G : ¬ (G.1 ≤ τ' ∧ τ' < G.2) :=
    ladder_time_not_mem_framesOf hx hτ' hτ' le_rfl le_rfl (Or.inl rfl) hGm
  have hEa := exc_fst_lt hx hE
  have hEb := lt_exc_snd hx hE
  have ha' := exc_fst_lt hx hτ'
  have hb' := lt_exc_snd hx hτ'
  have hne : τ' ≠ τE := by
    rintro rfl
    exact hτ'G ⟨by omega, by omega⟩
  have hnest : (exc x T τ').1 ≤ (exc x T τE).1 ∧ (exc x T τE).2 ≤ (exc x T τ').2 := by
    have hout := exc_outer hx hE hlad
    simp only at hout
    rcases exc_laminar hx hτ' hE with h | h | h | h
    · exact h
    · exact absurd (top_eq_of_mem hx hE (exc_mem hx hE) (exc_mem hx hτ') h.1 h.2 (by omega)
        (by omega)) (Ne.symm hne)
    · omega
    · omega
  have hbase := level_le_base hx hτ' hw hG hE hne hnest.1 hnest.2 (t := τE) (by omega) (by omega)
    hEa hEb
  have hcell := (ladder_cell_bounds hx hlad).1
  simp only at hcell
  have hbase' : base x T τE = w := by
    unfold base at hbase ⊢
    omega
  have hexc : exc x T τE = (p, q) :=
    ladder_eq_of_cell (exc_mem hx hE) hlad (by rw [x_exc_fst hx hE, hbase']; exact hxp.symm)
  refine ⟨hE, hexc, hbase', ?_⟩
  have hF := own_inner_top hx hE
  have hFb := inner_top_bounds hx hE
  rw [hexc] at hFb
  simp only at hFb
  have hw1 := hF.2.2 G (mem_insert_of_mem (mem_suspendFrames.mpr ⟨τ', hτ', hGm⟩))
    ⟨by omega, by omega⟩
  refine within_antisymm hw1 ?_
  have hFτ1 := hF.2.1.1
  have hFτ2 := hF.2.1.2
  unfold Within at hw1 ⊢
  rcases mem_insert.mp hF.1 with hroot | hFs
  · rw [hroot] at hw1
    simp only at hw1
    have := exc_snd_lt hx hτ'
    omega
  obtain ⟨σ, hσ, hFσ⟩ := mem_suspendFrames.mp hFs
  have hbσ := framesOf_bounds hx hσ hFσ
  by_cases h3 : σ = τ'
  · rw [h3] at hFσ
    rcases framesOf_disjoint hx hFσ hGm with he | he | he
    · rw [he]
      exact ⟨le_rfl, le_rfl⟩
    · omega
    · omega
  rcases exc_laminar hx hτ' hσ with h | h | h | h
  · -- a top nested in `τ'`: its frame cannot contain both `τE` and the start of `E`
    have hlb := level_le_base hx hτ' hw hG hσ (Ne.symm h3) h.1 h.2 (t := τE) (by omega)
      (by omega) (by omega) (by omega)
    have hp' : (exc x T σ).1 = p := by
      by_contra hne'
      have := base_lt_of_mem hx hσ (t := p) (by omega) (by omega)
      omega
    have h4 : σ = τE := top_eq_of_start (exc_mem hx hσ) hlad hp'
    rw [h4] at hFσ
    exact absurd ⟨hFτ1, hFτ2⟩
      (ladder_time_not_mem_framesOf hx hE hE le_rfl le_rfl (Or.inl rfl) hFσ)
  · -- an ancestor of `τ'`: its frame containing `τE` contains `τ'`
    obtain ⟨G₀, hG₀, hG₀1, hG₀2⟩ := exists_framesOf_nested hx hσ hτ' h3 h.1 h.2
    rcases framesOf_disjoint hx hFσ hG₀ with he | he | he
    · rw [he] at hw1
      exact absurd ⟨by omega, by omega⟩ hτ'G
    · omega
    · omega
  · omega
  · omega

/-- **Lemma W2, main case.** If the walk is at the level `w` of a nonempty frame `G` at its last time
`ℓ = G.2 − 1`, the running maximum of `G` at `ℓ` is at most `1`. Either the walk stays at `w` on
`G`, or the structure has a last excursion `E = (p, q)`, `q ≤ ℓ`, after which the walk stays at `w`;
the segment at `ℓ` then started at the last passage `D_E (w + 1)` of `E` (home `w + 1`), or, if `E`
has height `1`, at its start (home `w` or `w + 1`). -/
theorem runMax_last_le_one (hx : IsWalk x) (hτ' : τ' ∈ tops x T) (hw : w ∈ levels x T τ')
    (hG : G = hangFrame x T τ' w ∨ G = descFrame x T τ' w) (hne : G.1 < G.2)
    (hxl : x (G.2 - 1) = w) :
    (upperFrames x T hx).runMax ((upperFrames x T hx).inner (G.2 - 1)) (G.2 - 1) ≤ 1 := by
  have hGm := frameAt_mem hw hG
  have hGs : G ∈ suspendFrames x T := mem_suspendFrames.mpr ⟨τ', hτ', hGm⟩
  have hGb := framesOf_bounds hx hτ' hGm
  have hGT := exc_snd_lt hx hτ'
  obtain ⟨hlev, hG1, hpred, -⟩ := frameAt_walk hx hw hG
  have hend := x_end_le hx hGs hne
  have hown := own_of_le_level hx hτ' hw hG (t := G.2 - 1) (by omega) (by omega) hxl.le
  rw [inner_eq hown]
  by_cases hconst : ∀ t, G.1 ≤ t → t ≤ G.2 - 1 → x t = w
  · have hs1 := start_le_segStart (S := upperFrames x T hx) G (G.2 - 1)
    have hs2 := segStart_le (S := upperFrames x T hx) (F := G) (t := G.2 - 1) (by omega)
    refine runMax_le fun t' _ ht1 ht2 => ?_
    rw [upperFrames_x, hconst t' (by omega) ht2, hconst _ hs1 hs2]
    simp
  push Not at hconst
  obtain ⟨t₀, ht₀1, ht₀2, ht₀3⟩ := hconst
  obtain ⟨c, hcmem, hcmax⟩ := ((Icc G.1 (G.2 - 1)).filter (fun t => x t ≠ w)).exists_max_image id
    ⟨t₀, mem_filter.mpr ⟨mem_Icc.mpr ⟨ht₀1, ht₀2⟩, ht₀3⟩⟩
  obtain ⟨hcI, hcw⟩ := mem_filter.mp hcmem
  obtain ⟨hc1, hc2⟩ := mem_Icc.mp hcI
  have hafter : ∀ t, c < t → t ≤ G.2 - 1 → x t = w := fun t h1 h2 => by
    by_contra hne'
    have := hcmax t (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, h2⟩, hne'⟩)
    simp only [id] at this
    omega
  have hcl : c < G.2 - 1 := by
    rcases eq_or_lt_of_le hc2 with h | h
    · rw [h] at hcw
      exact absurd hxl hcw
    · exact h
  have hxc : x c = w + 1 := by
    have h1 := hlev c hc1 (by omega)
    have h2 := hafter (c + 1) (by omega) (by omega)
    have h3 := (hx.step c).2
    omega
  -- the last excursion `E = (p, c + 1)` of the structure
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ :=
    exists_last_visit hx (a := G.1 - 1) (b := c) (z := w) (by omega) hpred (by omega)
  have hxq := hafter (c + 1) (by omega) (by omega)
  have hHop : IsHop x T p (c + 1) :=
    ⟨by omega, by omega, by rw [hxq, hp3], fun t ht => by
      obtain ⟨h1, h2⟩ := mem_Ioo.mp ht
      rw [hp3]
      exact hp4 t h1 (by omega)⟩
  have hUp : IsUpperHop x p (c + 1) :=
    ⟨by omega, by rw [hxq, hp3], fun t h1 h2 => by
      have := hlev t (by omega) (by omega)
      have := hp4 t h1 (by omega)
      omega⟩
  have hpq : (p, c + 1) ∈ upperHops x T := (mem_upperHops hx).mpr ⟨hHop, hUp⟩
  obtain ⟨hE, hexc, hbase, hinner⟩ := struct_exc hx hτ' hw hG hpq hp3 (by omega) (by omega)
  generalize hopOwner x p (c + 1) = τE at hE hexc hbase hinner
  have hEa : (exc x T τE).1 = p := by rw [hexc]
  have hEb : (exc x T τE).2 = c + 1 := by rw [hexc]
  have hEτ1 := exc_fst_lt hx hE
  have hEτ2 := lt_exc_snd hx hE
  -- no restart point from the end of `E` to `ℓ`
  have hnoR : ∀ s, c + 1 ≤ s → s ≤ G.2 - 1 → s ∉ restartPts x T := by
    intro s hs1 hs2 hsR
    rcases restartPts_cases hx hsR with ⟨σ, hσ, z, hz1, hz2, rfl⟩ | hup
    · have hl := (isUpperHop_ladL hx hz1.le hz2).long
      have hpz := ladL_above hx hz1.le hz2 (t := ladD x T σ z - 1) (by omega) (by omega)
      have hxD := x_ladD hx hz1.le hz2
      rcases eq_or_lt_of_le hs1 with he | hlt
      · have h4 : σ = τE :=
          top_eq_of_end (ladL_mem hx hz1.le hz2) (exc_mem hx hE) (he.symm.trans hEb.symm)
        have hxc1 := hafter (c + 1) (by omega) (by omega)
        rw [he, hxD] at hxc1
        rw [h4, hbase] at hz1
        omega
      · have h1 := hafter (ladD x T σ z - 1) (by omega) (by omega)
        have h2 := hafter (ladD x T σ z) (by omega) hs2
        omega
    · rcases eq_or_lt_of_le hs2 with he | hlt
      · rw [he, show G.2 - 1 + 1 = G.2 by omega] at hup
        omega
      · have h1 := hafter (s + 1) (by omega) (by omega)
        have h2 := hafter s (by omega) hs2
        omega
  have hb := excStart_bounds hx hE
  rcases Nat.lt_or_ge (height x T τE) 2 with hH | hH
  · -- `E` has height `1`: the segment started at `excStart E`, on `[w, w + 1]`
    have hH1 : height x T τE = 1 := by have := one_le_height hE; omega
    have hspec := excStart_spec hx hE
    rw [hinner] at hspec
    have hseg : (upperFrames x T hx).segStart G (G.2 - 1) = excStart x T hx τE := by
      refine segStart_eq hspec (by omega) fun s hs hlt hle hown' => ?_
      rcases lt_or_ge s (c + 1) with h | h
      · rw [← hinner] at hown'
        obtain ⟨e, he, -⟩ :=
          mem_passages.mp (restart_inside hx hE (by omega) (by omega) (free_of_own hx hE hown') hs)
        have := Nat.two_pow_pos e
        omega
      · exact hnoR s h hle hs
    refine runMax_le fun t' _ ht1 ht2 => ?_
    rw [hseg] at ht1
    rw [hseg, upperFrames_x]
    have hxs := x_excStart hx hE
    have hxτ := x_top x T τE
    rcases le_or_gt t' (c + 1) with h | h
    · have := exc_range hx hE (t := t') (by omega) (by omega)
      omega
    · rw [hafter t' (by omega) ht2]
      omega
  · -- `E` has height `≥ 2`: the segment started at its last passage `P = D_E (w + 1)`
    have hxτ := x_top x T τE
    have hw1 : base x T τE ≤ w + 1 := by omega
    have hw2 : w + 1 < x τE := by omega
    have hPmem : ladD x T τE (w + 1) ∈ passages x T τE := by
      refine mem_passages.mpr ⟨0, by norm_num; omega, ?_⟩
      rw [hbase]
      norm_num
    obtain ⟨hτP, hPb, hPR, hPf⟩ := passage_spec hx hE hPmem
    have hPown : (upperFrames x T hx).Own G (ladD x T τE (w + 1)) := by
      rw [← hinner]
      exact own_of_free hx hE (by omega) hPb hPf
    have hxP := x_ladD hx hw1 hw2
    have hseg : (upperFrames x T hx).segStart G (G.2 - 1) = ladD x T τE (w + 1) := by
      refine segStart_eq (Or.inr ⟨hPR, by omega, hPown⟩) (by omega) fun s hs hlt hle hown' => ?_
      rcases lt_or_ge s (c + 1) with h | h
      · rw [← hinner] at hown'
        obtain ⟨e, he, rfl⟩ :=
          mem_passages.mp (restart_inside hx hE (by omega) (by omega) (free_of_own hx hE hown') hs)
        have := Nat.two_pow_pos e
        obtain ⟨hc1', hc2'⟩ := cell_bounds (x := x) (T := T) (τ := τE) he
        have := (ladD_le_ladD_iff hx hc1' hc2' hw1 hw2).mpr (by omega)
        omega
      · exact hnoR s h hle hs
    refine runMax_le fun t' hown' ht1 ht2 => ?_
    rw [hseg] at ht1
    rw [hseg, upperFrames_x, hxP]
    rcases lt_or_ge t' (c + 1) with h | h
    · rcases eq_or_lt_of_le ht1 with he | hlt
      · rw [← he, hxP]
        simp
      · exfalso
        rw [← hinner] at hown'
        have hlev' : w + 1 ∈ levels x T τE := mem_levels.mpr ⟨by omega, hw2⟩
        have hEb' : ladD x T τE (base x T τE) = c + 1 := hEb
        refine free_of_own hx hE hown' τE hE le_rfl le_rfl (descFrame x T τE (w + 1))
          (mem_framesOf.mpr ⟨_, hlev', Or.inr rfl⟩) ⟨show ladD x T τE (w + 1) + 1 ≤ t' by omega, ?_⟩
        show t' < ladD x T τE (w + 1 - 1)
        rw [add_sub_cancel_right, ← hbase, hEb']
        exact h
    · rw [hafter t' (by omega) ht2]
      omega

/-- **Lemma W2.** Every nonempty suspend frame ends at band `0`: at its last time `ℓ` the running
maximum of the innermost frame is at most `1`. If the walk is at the level of the frame at `ℓ`, this
is `runMax_last_le_one`. Otherwise `ℓ` is one step before the end of the last excursion `E` of a
hanging structure: a time of `E` of height `1`, the last passage `D_E (base_E + 1)` (a restart), or
the last time of the descent frame of `E` at level `base_E + 1`, where the walk is at that level. -/
theorem beta_last_eq_zero (hx : IsWalk x) {G : ℕ × ℕ} (hG : G ∈ suspendFrames x T)
    (hne : G.1 < G.2) : (upperFrames x T hx).beta (G.2 - 1) = 0 := by
  suffices h : (upperFrames x T hx).runMax ((upperFrames x T hx).inner (G.2 - 1)) (G.2 - 1) ≤ 1 by
    have h1 := band_mono h
    rw [show band 1 = 0 from Nat.log_one_right 2] at h1
    exact Nat.eq_zero_of_le_zero h1
  obtain ⟨τ', hτ', hGτ'⟩ := mem_suspendFrames.mp hG
  obtain ⟨w, hw, hG'⟩ := mem_framesOf.mp hGτ'
  have hG'' : G = hangFrame x T τ' w ∨ G = descFrame x T τ' w := hG'.imp Eq.symm Eq.symm
  obtain ⟨hlev, hG1, hpred, hxend⟩ := frameAt_walk hx hw hG''
  have hGb := framesOf_bounds hx hτ' hGτ'
  have hGT := exc_snd_lt hx hτ'
  have hl1 := hlev (G.2 - 1) (by omega) (by omega)
  have hst := hx.step (G.2 - 1)
  rw [show G.2 - 1 + 1 = G.2 by omega] at hst
  rcases eq_or_lt_of_le hl1 with hxl | hxl
  · exact runMax_last_le_one hx hτ' hw hG'' hne hxl.symm
  -- `x ℓ = w + 1`: the last excursion `E = (p, G.2)` ends at the end of `G`
  have hxl' : x (G.2 - 1) = w + 1 := by omega
  have hxe : x G.2 = w := by omega
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ :=
    exists_last_visit hx (a := G.1 - 1) (b := G.2 - 1) (z := w) (by omega) hpred (by omega)
  have hHop : IsHop x T p G.2 :=
    ⟨by omega, by omega, by rw [hxe, hp3], fun t ht => by
      obtain ⟨h1, h2⟩ := mem_Ioo.mp ht
      rw [hp3]
      exact hp4 t h1 (by omega)⟩
  have hUp : IsUpperHop x p G.2 :=
    ⟨by omega, by rw [hxe, hp3], fun t h1 h2 => by
      have := hlev t (by omega) (by omega)
      have := hp4 t h1 (by omega)
      omega⟩
  have hpq : (p, G.2) ∈ upperHops x T := (mem_upperHops hx).mpr ⟨hHop, hUp⟩
  obtain ⟨hE, hexc, hbase, hinner⟩ := struct_exc hx hτ' hw hG'' hpq hp3 (by omega) le_rfl
  generalize hopOwner x p G.2 = τE at hE hexc hbase hinner
  have hEa : (exc x T τE).1 = p := by rw [hexc]
  have hEb : (exc x T τE).2 = G.2 := by rw [hexc]
  have hxτ := x_top x T τE
  rcases Nat.lt_or_ge (height x T τE) 2 with hH | hH
  · -- `E` has height `1`: the running maximum is at most the height
    exact (runMax_le_height hx hE (segStart_inner_mem hx hE (by omega) (by omega)).1
      (by omega)).trans (by omega)
  have hw1 : base x T τE ≤ w + 1 := by omega
  have hw2 : w + 1 < x τE := by omega
  have hPmem : ladD x T τE (w + 1) ∈ passages x T τE := by
    refine mem_passages.mpr ⟨0, by norm_num; omega, ?_⟩
    rw [hbase]
    norm_num
  obtain ⟨hτP, hPb, hPR, hPf⟩ := passage_spec hx hE hPmem
  rcases eq_or_lt_of_le (show ladD x T τE (w + 1) ≤ G.2 - 1 by omega) with hP | hP
  · -- `ℓ` is the last passage of `E`: a restart
    have hEτ1 := exc_fst_lt hx hE
    have hown := own_of_free hx hE (by omega) hPb hPf
    rw [hinner, hP] at hown
    rw [inner_eq hown, runMax_of_restart ⟨by rw [← hP]; exact hPR, by omega, hown⟩]
    omega
  · -- `ℓ` is the last time of the descent frame of `E` at level `w + 1`
    have hlev' : w + 1 ∈ levels x T τE := mem_levels.mpr ⟨by omega, hw2⟩
    have hEb' : ladD x T τE (base x T τE) = G.2 := hEb
    have h2 : (descFrame x T τE (w + 1)).2 = G.2 := by
      show ladD x T τE (w + 1 - 1) = G.2
      rw [add_sub_cancel_right, ← hbase, hEb']
    have h1 : (descFrame x T τE (w + 1)).1 = ladD x T τE (w + 1) + 1 := rfl
    have := runMax_last_le_one hx hE hlev' (Or.inr rfl) (by omega) (by rw [h2]; exact hxl')
    rwa [h2] at this

end Levels

end BoundedStackDepth

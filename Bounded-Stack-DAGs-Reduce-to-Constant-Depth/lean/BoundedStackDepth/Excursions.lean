import BoundedStackDepth.FramesU

/-!
# Excursions and the laminarity of the frames of class U

Let `x` be a walk (pauses allowed) and `T` a horizon. The ladder hops, canonical excursions and
suspend frames of class U are defined in `FramesU.lean`; write `L = ladL`, `D = ladD`.

* `ladL_mem`, `x_ladL`, `x_ladD`, `ladL_lt`, `lt_ladD`, `ladD_lt_T`, `ladL_above`, `le_ladL`,
  `ladD_le`, `ladL_lt_ladL`, `ladL_le_ladL`: for `base τ ≤ z < x τ`, `(L τ z, D τ z)` is the
  hop of the ladder of `τ` at cell `z`. It spans `τ`, the walk is strictly above `z` inside,
  `L τ z` is the last visit to `z` up to `τ` and `D τ z` the first visit from `τ` on; a higher
  cell gives a later `L` and an earlier `D`. `not_lt_ladL_lt`, `not_lt_ladD_lt`: an upper hop
  that ends by `τ` (starts from `τ` on) cannot straddle `L τ z` (`D τ z`).
* `exc_mem`, `exc_outer`, `exc_range`: the canonical excursion
  `exc τ = (L τ (base τ), D τ (base τ))` of a top is a hop of its ladder, contains all the others,
  and the walk stays in `[base τ, x τ]` on its closed interval.
* `top_eq_of_start`, `top_eq_of_end`, `top_eq_of_mem`: ladder hops with the same start or the same
  end have the same top, and a top lies in no closed hop of another top nested in one of its hops.
* `upper_laminar`, `exc_laminar`: upper hops, hence canonical excursions, are nested or meet in at
  most one endpoint.
* `exc_structure` (**structures**): an excursion of another top
  nested in `exc τ` lies in a closed hanging structure `[L τ (w − 1) + 1, L τ w]` (before `τ`) or a
  closed descent structure `[D τ w, D τ (w − 1) − 1]` (after `τ`), at a level `w ≤` its base.
* `framesOf_bounds`, `framesOf_disjoint`, `exists_framesOf_nested`, `frames_laminar`: the frames of
  one top lie strictly inside its excursion and are pairwise disjoint, the excursion of a
  descendant lies inside one of them, so the root and the suspend frames form a laminar family.
* `upperFrames`: the frame system of class U.
* `ladder_time_not_mem_framesOf`: the ladder times of `τ` lie in no frame of `τ` and in no frame
  of a descendant of `τ`.
-/

namespace BoundedStackDepth

open BoundedNesting Finset

variable {x : ℕ → ℤ} {T τ τ' : ℕ} {z z' w : ℤ} {e e' : ℕ × ℕ}

/-! ### Ladder hops -/

theorem ladderHop_spec (hx : IsWalk x) (hz1 : base x T τ ≤ z) (hz2 : z < x τ) :
    ladderHop x T τ z ∈ ladder x T τ ∧ x (ladderHop x T τ z).1 = z := by
  have h : ∃ e ∈ ladder x T τ, x e.1 = z := (ladder_cell_iff hx).mpr ⟨hz1, hz2⟩
  rw [ladderHop, dite_eq_left h]
  exact h.choose_spec

/-- For `base τ ≤ z < x τ`, `(L τ z, D τ z)` is the hop of the ladder of `τ` at cell `z`. -/
theorem ladL_mem (hx : IsWalk x) (hz1 : base x T τ ≤ z) (hz2 : z < x τ) :
    (ladL x T τ z, ladD x T τ z) ∈ ladder x T τ :=
  (ladderHop_spec hx hz1 hz2).1

theorem x_ladL (hx : IsWalk x) (hz1 : base x T τ ≤ z) (hz2 : z < x τ) : x (ladL x T τ z) = z :=
  (ladderHop_spec hx hz1 hz2).2

theorem isUpperHop_ladL (hx : IsWalk x) (hz1 : base x T τ ≤ z) (hz2 : z < x τ) :
    IsUpperHop x (ladL x T τ z) (ladD x T τ z) :=
  ((mem_ladder hx).mp (ladL_mem hx hz1 hz2)).2.1

theorem x_ladD (hx : IsWalk x) (hz1 : base x T τ ≤ z) (hz2 : z < x τ) : x (ladD x T τ z) = z :=
  (isUpperHop_ladL hx hz1 hz2).eq.trans (x_ladL hx hz1 hz2)

theorem ladL_lt (hx : IsWalk x) (hz1 : base x T τ ≤ z) (hz2 : z < x τ) : ladL x T τ z < τ :=
  (ladder_lt (ladL_mem hx hz1 hz2)).1

theorem lt_ladD (hx : IsWalk x) (hz1 : base x T τ ≤ z) (hz2 : z < x τ) : τ < ladD x T τ z :=
  (ladder_lt (ladL_mem hx hz1 hz2)).2

theorem ladD_lt_T (hx : IsWalk x) (hz1 : base x T τ ≤ z) (hz2 : z < x τ) : ladD x T τ z < T :=
  (isHop_of_mem_ladder (ladL_mem hx hz1 hz2)).2.1

/-- The walk is strictly above `z` strictly between `L τ z` and `D τ z`. -/
theorem ladL_above (hx : IsWalk x) (hz1 : base x T τ ≤ z) (hz2 : z < x τ) {t : ℕ}
    (h1 : ladL x T τ z < t) (h2 : t < ladD x T τ z) : z < x t := by
  have := (isUpperHop_ladL hx hz1 hz2).above t h1 h2
  rwa [x_ladL hx hz1 hz2] at this

/-- `L τ z` is the last visit to `z` up to `τ`. -/
theorem le_ladL (hx : IsWalk x) (hz1 : base x T τ ≤ z) (hz2 : z < x τ) {t : ℕ} (ht : t ≤ τ)
    (hxt : x t = z) : t ≤ ladL x T τ z :=
  ladder_last_visit hx (ladL_mem hx hz1 hz2) ht (hxt.trans (x_ladL hx hz1 hz2).symm)

/-- `D τ z` is the first visit to `z` from `τ` on. -/
theorem ladD_le (hx : IsWalk x) (hz1 : base x T τ ≤ z) (hz2 : z < x τ) {t : ℕ} (ht : τ ≤ t)
    (hxt : x t = z) : ladD x T τ z ≤ t :=
  ladder_first_visit hx (ladL_mem hx hz1 hz2) ht (hxt.trans (x_ladL hx hz1 hz2).symm)

/-- A higher cell gives a later `L` and an earlier `D`. -/
theorem ladL_lt_ladL (hx : IsWalk x) (hz1 : base x T τ ≤ z) (hzz : z < z') (hz2 : z' < x τ) :
    ladL x T τ z < ladL x T τ z' ∧ ladD x T τ z' < ladD x T τ z :=
  ladder_nested hx (ladL_mem hx hz1 (hzz.trans hz2)) (ladL_mem hx (hz1.trans hzz.le) hz2)
    (show x (ladL x T τ z) < x (ladL x T τ z') by
      rw [x_ladL hx hz1 (hzz.trans hz2), x_ladL hx (hz1.trans hzz.le) hz2]; exact hzz)

theorem ladL_le_ladL (hx : IsWalk x) (hz1 : base x T τ ≤ z) (hzz : z ≤ z') (hz2 : z' < x τ) :
    ladL x T τ z ≤ ladL x T τ z' ∧ ladD x T τ z' ≤ ladD x T τ z := by
  rcases eq_or_lt_of_le hzz with rfl | h
  · exact ⟨le_rfl, le_rfl⟩
  · exact ⟨(ladL_lt_ladL hx hz1 h hz2).1.le, (ladL_lt_ladL hx hz1 h hz2).2.le⟩

/-- **No straddling a last visit.** An upper hop that ends by `τ` does not contain `L τ z`
strictly inside. -/
theorem not_lt_ladL_lt (hx : IsWalk x) (hz1 : base x T τ ≤ z) (hz2 : z < x τ) {p u : ℕ}
    (h : IsUpperHop x p u) (hu : u ≤ τ) : ¬ (p < ladL x T τ z ∧ ladL x T τ z < u) :=
  fun ⟨h1, h2⟩ =>
    upper_no_cross h (isUpperHop_ladL hx hz1 hz2) ⟨h1, h2, hu.trans_lt (lt_ladD hx hz1 hz2)⟩

/-- **No straddling a first visit.** An upper hop that starts from `τ` on does not contain
`D τ z` strictly inside. -/
theorem not_lt_ladD_lt (hx : IsWalk x) (hz1 : base x T τ ≤ z) (hz2 : z < x τ) {p u : ℕ}
    (h : IsUpperHop x p u) (hp : τ ≤ p) : ¬ (p < ladD x T τ z ∧ ladD x T τ z < u) :=
  fun ⟨h1, h2⟩ =>
    upper_no_cross (isUpperHop_ladL hx hz1 hz2) h ⟨(ladL_lt hx hz1 hz2).trans_le hp, h1, h2⟩

theorem mem_levels : w ∈ levels x T τ ↔ base x T τ < w ∧ w < x τ := mem_Ioo

/-! ### The canonical excursion -/

theorem base_lt (hτ : τ ∈ tops x T) : base x T τ < x τ := by
  have := one_le_height hτ
  unfold base
  omega

theorem exc_fst : (exc x T τ).1 = ladL x T τ (base x T τ) := rfl

theorem exc_snd : (exc x T τ).2 = ladD x T τ (base x T τ) := rfl

/-- The canonical excursion of a top is a hop of its ladder. -/
theorem exc_mem (hx : IsWalk x) (hτ : τ ∈ tops x T) : exc x T τ ∈ ladder x T τ :=
  ladL_mem hx le_rfl (base_lt hτ)

theorem isUpperHop_exc (hx : IsWalk x) (hτ : τ ∈ tops x T) :
    IsUpperHop x (exc x T τ).1 (exc x T τ).2 :=
  ((mem_ladder hx).mp (exc_mem hx hτ)).2.1

theorem isOwner_exc (hx : IsWalk x) (hτ : τ ∈ tops x T) : IsOwner x (exc x T τ).1 (exc x T τ).2 τ :=
  ((mem_ladder hx).mp (exc_mem hx hτ)).2.2

/-- On the closed interval of a ladder hop of `τ`, the walk is between its cell and `x τ`. -/
theorem ladder_range (hx : IsWalk x) (he : e ∈ ladder x T τ) {t : ℕ} (h1 : e.1 ≤ t)
    (h2 : t ≤ e.2) : x e.1 ≤ x t ∧ x t ≤ x τ := by
  obtain ⟨-, hu, ho⟩ := (mem_ladder hx).mp he
  have hc := ladder_cell_lt hx he
  rcases eq_or_lt_of_le h1 with rfl | h1
  · exact ⟨le_rfl, hc.le⟩
  rcases eq_or_lt_of_le h2 with rfl | h2
  · rw [hu.eq]; exact ⟨le_rfl, hc.le⟩
  · exact ⟨(hu.above t h1 h2).le, ho.max t h1 h2⟩

/-- The canonical excursion of a top contains every hop of its ladder. -/
theorem exc_outer (hx : IsWalk x) (hτ : τ ∈ tops x T) (he : e ∈ ladder x T τ) :
    (exc x T τ).1 ≤ e.1 ∧ e.2 ≤ (exc x T τ).2 := by
  obtain ⟨e₀, he₀, hc, hout⟩ := exists_ladder_outer hx hτ
  obtain rfl : e₀ = exc x T τ := ladder_eq_of_cell he₀ (exc_mem hx hτ)
    (hc.trans (x_ladL hx le_rfl (base_lt hτ)).symm)
  exact hout e he

/-- On the closed interval of the canonical excursion of `τ`, the walk stays in `[base τ, x τ]`. -/
theorem exc_range (hx : IsWalk x) (hτ : τ ∈ tops x T) {t : ℕ} (h1 : (exc x T τ).1 ≤ t)
    (h2 : t ≤ (exc x T τ).2) : base x T τ ≤ x t ∧ x t ≤ x τ := by
  have := ladder_range hx (exc_mem hx hτ) h1 h2
  rwa [exc_fst, x_ladL hx le_rfl (base_lt hτ)] at this

/-! ### Distinct tops -/

/-- Ladder hops with the same start have the same top. -/
theorem top_eq_of_start (he : e ∈ ladder x T τ) (he' : e' ∈ ladder x T τ') (h : e.1 = e'.1) :
    τ = τ' := by
  have hh' := isHop_of_mem_ladder he'
  rw [← h] at hh'
  obtain rfl : e = e' := Prod.ext h (hop_start_unique (isHop_of_mem_ladder he) hh')
  exact eq_of_mem_ladder he he'

/-- Ladder hops with the same end have the same top. -/
theorem top_eq_of_end (he : e ∈ ladder x T τ) (he' : e' ∈ ladder x T τ') (h : e.2 = e'.2) :
    τ = τ' := by
  have hh' := isHop_of_mem_ladder he'
  rw [← h] at hh'
  obtain rfl : e = e' := Prod.ext (hop_end_unique (isHop_of_mem_ladder he) hh') h
  exact eq_of_mem_ladder he he'

/-- A top `τ` in the closed interval of a hop of `τ'` nested in a hop of `τ` is `τ'`: it is the
first argmax of that hop. -/
theorem top_eq_of_mem (hx : IsWalk x) (hτ : τ ∈ tops x T) (he : e ∈ ladder x T τ)
    (he' : e' ∈ ladder x T τ') (h1 : e.1 ≤ e'.1) (h2 : e'.2 ≤ e.2) (ht1 : e'.1 ≤ τ)
    (ht2 : τ ≤ e'.2) : τ = τ' := by
  have hs := top_ne_start hx hτ (mem_upperHops_of_mem_ladder he')
  have hn := top_ne_end hx hτ (mem_upperHops_of_mem_ladder he')
  have ho := ((mem_ladder hx).mp he).2.2
  have hown : IsOwner x e'.1 e'.2 τ :=
    ⟨by omega, by omega, fun t ht1 ht2 => ho.max t (by omega) (by omega),
      fun t ht1 ht2 => ho.first t (by omega) ht2⟩
  exact hown.unique ((mem_ladder hx).mp he').2.2

/-! ### Laminarity of the excursions -/

/-- Two upper hops are nested or meet in at most one endpoint. -/
theorem upper_laminar {p u p' u' : ℕ} (h : IsUpperHop x p u) (h' : IsUpperHop x p' u') :
    (p ≤ p' ∧ u' ≤ u) ∨ (p' ≤ p ∧ u ≤ u') ∨ u ≤ p' ∨ u' ≤ p := by
  have := upper_no_cross h h'
  have := upper_no_cross h' h
  omega

/-- **Excursions are laminar.** The closed intervals of two canonical excursions are nested or
meet in at most one endpoint. -/
theorem exc_laminar (hx : IsWalk x) (hτ : τ ∈ tops x T) (hτ' : τ' ∈ tops x T) :
    ((exc x T τ).1 ≤ (exc x T τ').1 ∧ (exc x T τ').2 ≤ (exc x T τ).2) ∨
      ((exc x T τ').1 ≤ (exc x T τ).1 ∧ (exc x T τ).2 ≤ (exc x T τ').2) ∨
      (exc x T τ).2 ≤ (exc x T τ').1 ∨ (exc x T τ').2 ≤ (exc x T τ).1 :=
  upper_laminar (isUpperHop_exc hx hτ) (isUpperHop_exc hx hτ')

/-! ### Structures -/

/-- A predicate false at `a` and true at `b ≥ a` switches on at some `w ∈ (a, b]`. -/
theorem exists_switch {P : ℤ → Prop} {a b : ℤ} (hab : a ≤ b) (ha : ¬ P a) (hb : P b) :
    ∃ w, a < w ∧ w ≤ b ∧ ¬ P (w - 1) ∧ P w := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  clear hab
  induction n with
  | zero => exact absurd (by simpa using hb) ha
  | succ n ih =>
    by_cases h : P (a + n)
    · obtain ⟨w, h1, h2, h3, h4⟩ := ih h
      exact ⟨w, h1, by push_cast; omega, h3, h4⟩
    · refine ⟨a + n + 1, by omega, by push_cast; omega, by simpa using h, ?_⟩
      have e : a + ((n + 1 : ℕ) : ℤ) = a + n + 1 := by push_cast; ring
      rwa [e] at hb

/-- **Structures.** If the canonical excursion of a top
`τ' ≠ τ` lies in the closed interval of that of `τ`, there is a level `w` of `τ` with
`w ≤ base τ'` such that either `τ' < τ` and `exc τ'` lies in the closed hanging structure
`[L τ (w − 1) + 1, L τ w]`, or `τ < τ'` and `exc τ'` lies in the closed descent structure
`[D τ w, D τ (w − 1) − 1]`. -/
theorem exc_structure (hx : IsWalk x) (hτ : τ ∈ tops x T) (hτ' : τ' ∈ tops x T) (hne : τ ≠ τ')
    (h1 : (exc x T τ).1 ≤ (exc x T τ').1) (h2 : (exc x T τ').2 ≤ (exc x T τ).2) :
    ∃ w ∈ levels x T τ, w ≤ base x T τ' ∧
      ((τ' < τ ∧ ladL x T τ (w - 1) + 1 ≤ (exc x T τ').1 ∧ (exc x T τ').2 ≤ ladL x T τ w) ∨
        (τ < τ' ∧ ladD x T τ w ≤ (exc x T τ').1 ∧ (exc x T τ').2 + 1 ≤ ladD x T τ (w - 1))) := by
  have hE := exc_mem hx hτ
  have hE' := exc_mem hx hτ'
  have hu' := isUpperHop_exc hx hτ'
  have ho' := isOwner_exc hx hτ'
  have hlong := hu'.long
  have h1' : ladL x T τ (base x T τ) ≤ (exc x T τ').1 := h1
  have h2' : (exc x T τ').2 ≤ ladD x T τ (base x T τ) := h2
  have hP' : x (exc x T τ').1 = base x T τ' := x_ladL hx le_rfl (base_lt hτ')
  have hU' : x (exc x T τ').2 = base x T τ' := hu'.eq.trans hP'
  -- the base of `τ'` lies in `[base τ, x τ)`
  have r1 := exc_range hx hτ h1 (by omega : (exc x T τ').1 ≤ (exc x T τ).2)
  have r2 := exc_range hx hτ (t := (exc x T τ').1 + 1) (by omega) (by omega)
  have a2 := hu'.above ((exc x T τ').1 + 1) (by omega) (by omega)
  have hy1 : base x T τ ≤ base x T τ' := by omega
  have hy2 : base x T τ' < x τ := by omega
  -- `τ` is not in the closed interval of `exc τ'`
  have hnot : ¬ ((exc x T τ').1 ≤ τ ∧ τ ≤ (exc x T τ').2) := fun h =>
    hne (top_eq_of_mem hx hτ hE hE' h1 h2 h.1 h.2)
  rcases lt_or_ge (exc x T τ').2 τ with hc | hc
  · -- before `τ`: a hanging structure
    have hs : ∃ w, base x T τ < w ∧ w ≤ base x T τ' ∧
        ¬ ((exc x T τ').1 ≤ ladL x T τ (w - 1)) ∧ (exc x T τ').1 ≤ ladL x T τ w :=
      exists_switch (P := fun z => (exc x T τ').1 ≤ ladL x T τ z) hy1
        (fun h => hne (top_eq_of_start hE hE'
          (show ladL x T τ (base x T τ) = (exc x T τ').1 by omega)))
        (le_ladL hx hy1 hy2 (by omega) hP')
    obtain ⟨w, hw1, hw2, hw3, hw4⟩ := hs
    have hwx : w < x τ := lt_of_le_of_lt hw2 hy2
    have hne' : ladL x T τ w ≠ (exc x T τ').1 := fun h =>
      hne (top_eq_of_start (ladL_mem hx hw1.le hwx) hE' h)
    have hU : (exc x T τ').2 ≤ ladL x T τ w := by
      by_contra hcon
      exact not_lt_ladL_lt hx hw1.le hwx hu' hc.le ⟨by omega, by omega⟩
    exact ⟨w, mem_levels.mpr ⟨hw1, hwx⟩, hw2, Or.inl ⟨by have := ho'.lt; omega, by omega, hU⟩⟩
  · -- after `τ`: a descent structure
    have hc' : τ < (exc x T τ').1 := by
      by_contra hcon
      exact hnot ⟨by omega, hc⟩
    have hs : ∃ w, base x T τ < w ∧ w ≤ base x T τ' ∧
        ¬ (ladD x T τ (w - 1) ≤ (exc x T τ').2) ∧ ladD x T τ w ≤ (exc x T τ').2 :=
      exists_switch (P := fun z => ladD x T τ z ≤ (exc x T τ').2) hy1
        (fun h => hne (top_eq_of_end hE hE'
          (show ladD x T τ (base x T τ) = (exc x T τ').2 by omega)))
        (ladD_le hx hy1 hy2 hc hU')
    obtain ⟨w, hw1, hw2, hw3, hw4⟩ := hs
    have hwx : w < x τ := lt_of_le_of_lt hw2 hy2
    have hne' : ladD x T τ w ≠ (exc x T τ').2 := fun h =>
      hne (top_eq_of_end (ladL_mem hx hw1.le hwx) hE' h)
    have hP : ladD x T τ w ≤ (exc x T τ').1 := by
      by_contra hcon
      exact not_lt_ladD_lt hx hw1.le hwx hu' hc'.le ⟨by omega, by omega⟩
    exact ⟨w, mem_levels.mpr ⟨hw1, hwx⟩, hw2, Or.inr ⟨by have := ho'.gt; omega, hP, by omega⟩⟩

/-! ### The frames of one top -/

/-- The frames of the top `τ`: its hanging and descent frames at its levels. -/
noncomputable def framesOf (x : ℕ → ℤ) (T τ : ℕ) : Finset (ℕ × ℕ) :=
  (levels x T τ).image (hangFrame x T τ) ∪ (levels x T τ).image (descFrame x T τ)

theorem suspendFrames_eq_biUnion (x : ℕ → ℤ) (T : ℕ) :
    suspendFrames x T = (tops x T).biUnion (framesOf x T) := rfl

theorem mem_suspendFrames {F : ℕ × ℕ} :
    F ∈ suspendFrames x T ↔ ∃ τ ∈ tops x T, F ∈ framesOf x T τ := by
  rw [suspendFrames_eq_biUnion, mem_biUnion]

theorem mem_framesOf {F : ℕ × ℕ} :
    F ∈ framesOf x T τ ↔ ∃ w ∈ levels x T τ, hangFrame x T τ w = F ∨ descFrame x T τ w = F := by
  simp only [framesOf, mem_union, mem_image]
  constructor
  · rintro (⟨w, hw, h⟩ | ⟨w, hw, h⟩)
    · exact ⟨w, hw, Or.inl h⟩
    · exact ⟨w, hw, Or.inr h⟩
  · rintro ⟨w, hw, h | h⟩
    · exact Or.inl ⟨w, hw, h⟩
    · exact Or.inr ⟨w, hw, h⟩

/-- A frame of `τ` lies strictly inside its canonical excursion. -/
theorem framesOf_bounds (hx : IsWalk x) (hτ : τ ∈ tops x T) {F : ℕ × ℕ}
    (hF : F ∈ framesOf x T τ) : (exc x T τ).1 < F.1 ∧ F.2 ≤ (exc x T τ).2 := by
  obtain ⟨w, hw, rfl | rfl⟩ := mem_framesOf.mp hF <;> obtain ⟨hw1, hw2⟩ := mem_levels.mp hw
  · have h1 := (ladL_le_ladL hx le_rfl (show base x T τ ≤ w - 1 by omega) (by omega)).1
    have h2 := ladL_lt hx hw1.le hw2
    have h3 := lt_ladD hx (le_refl (base x T τ)) (base_lt hτ)
    show ladL x T τ (base x T τ) < ladL x T τ (w - 1) + 1 ∧
      ladL x T τ w ≤ ladD x T τ (base x T τ)
    omega
  · have h1 := (ladL_le_ladL hx le_rfl (show base x T τ ≤ w - 1 by omega) (by omega)).2
    have h2 := lt_ladD hx hw1.le hw2
    have h3 := ladL_lt hx (le_refl (base x T τ)) (base_lt hτ)
    show ladL x T τ (base x T τ) < ladD x T τ w + 1 ∧
      ladD x T τ (w - 1) ≤ ladD x T τ (base x T τ)
    omega

theorem framesOf_le_T (hx : IsWalk x) (hτ : τ ∈ tops x T) {F : ℕ × ℕ}
    (hF : F ∈ framesOf x T τ) : F.2 ≤ T :=
  (framesOf_bounds hx hτ hF).2.trans (ladD_lt_T hx le_rfl (base_lt hτ)).le

/-- Two frames of one top are equal or disjoint: they are consecutive ladder intervals. -/
theorem framesOf_disjoint (hx : IsWalk x) {F G : ℕ × ℕ} (hF : F ∈ framesOf x T τ)
    (hG : G ∈ framesOf x T τ) : F = G ∨ F.2 ≤ G.1 ∨ G.2 ≤ F.1 := by
  obtain ⟨w, hw, rfl | rfl⟩ := mem_framesOf.mp hF <;>
    obtain ⟨w', hw', rfl | rfl⟩ := mem_framesOf.mp hG <;>
    obtain ⟨hw1, hw2⟩ := mem_levels.mp hw <;> obtain ⟨hw1', hw2'⟩ := mem_levels.mp hw'
  · rcases lt_trichotomy w w' with h | rfl | h
    · have := (ladL_le_ladL hx hw1.le (show w ≤ w' - 1 by omega) (by omega)).1
      right; left
      show ladL x T τ w ≤ ladL x T τ (w' - 1) + 1
      omega
    · exact Or.inl rfl
    · have := (ladL_le_ladL hx hw1'.le (show w' ≤ w - 1 by omega) (by omega)).1
      right; right
      show ladL x T τ w' ≤ ladL x T τ (w - 1) + 1
      omega
  · have := ladL_lt hx hw1.le hw2
    have := lt_ladD hx hw1'.le hw2'
    right; left
    show ladL x T τ w ≤ ladD x T τ w' + 1
    omega
  · have := lt_ladD hx hw1.le hw2
    have := ladL_lt hx hw1'.le hw2'
    right; right
    show ladL x T τ w' ≤ ladD x T τ w + 1
    omega
  · rcases lt_trichotomy w w' with h | rfl | h
    · have := (ladL_le_ladL hx hw1.le (show w ≤ w' - 1 by omega) (by omega)).2
      right; right
      show ladD x T τ (w' - 1) ≤ ladD x T τ w + 1
      omega
    · exact Or.inl rfl
    · have := (ladL_le_ladL hx hw1'.le (show w' ≤ w - 1 by omega) (by omega)).2
      right; left
      show ladD x T τ (w - 1) ≤ ladD x T τ w' + 1
      omega

/-- The canonical excursion of a top `τ' ≠ τ` nested in that of `τ` lies in a frame of `τ`, with
its interior `[(exc τ').1 + 1, (exc τ').2)`. -/
theorem exists_framesOf_nested (hx : IsWalk x) (hτ : τ ∈ tops x T) (hτ' : τ' ∈ tops x T)
    (hne : τ ≠ τ') (h1 : (exc x T τ).1 ≤ (exc x T τ').1) (h2 : (exc x T τ').2 ≤ (exc x T τ).2) :
    ∃ F ∈ framesOf x T τ, F.1 ≤ (exc x T τ').1 + 1 ∧ (exc x T τ').2 ≤ F.2 := by
  obtain ⟨w, hw, -, ⟨-, ha, hb⟩ | ⟨-, ha, hb⟩⟩ := exc_structure hx hτ hτ' hne h1 h2
  · exact ⟨hangFrame x T τ w, mem_framesOf.mpr ⟨w, hw, Or.inl rfl⟩,
      show ladL x T τ (w - 1) + 1 ≤ (exc x T τ').1 + 1 by omega, hb⟩
  · exact ⟨descFrame x T τ w, mem_framesOf.mpr ⟨w, hw, Or.inr rfl⟩,
      show ladD x T τ w + 1 ≤ (exc x T τ').1 + 1 by omega,
      show (exc x T τ').2 ≤ ladD x T τ (w - 1) by omega⟩

/-- Frames of two tops whose canonical excursions are nested are laminar. -/
theorem framesOf_laminar_of_nested (hx : IsWalk x) (hτ : τ ∈ tops x T) (hτ' : τ' ∈ tops x T)
    (h1 : (exc x T τ).1 ≤ (exc x T τ').1) (h2 : (exc x T τ').2 ≤ (exc x T τ).2) {F G : ℕ × ℕ}
    (hF : F ∈ framesOf x T τ) (hG : G ∈ framesOf x T τ') :
    (G.1 ≤ F.1 ∧ F.2 ≤ G.2) ∨ (F.1 ≤ G.1 ∧ G.2 ≤ F.2) ∨ F.2 ≤ G.1 ∨ G.2 ≤ F.1 := by
  by_cases hne : τ = τ'
  · subst hne
    rcases framesOf_disjoint hx hF hG with rfl | h | h
    · exact Or.inl ⟨le_rfl, le_rfl⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · obtain ⟨H, hH, hH1, hH2⟩ := exists_framesOf_nested hx hτ hτ' hne h1 h2
    have hG' := framesOf_bounds hx hτ' hG
    rcases framesOf_disjoint hx hF hH with rfl | h | h
    · right; left; omega
    · right; right; left; omega
    · right; right; right; omega

/-- **Frame laminarity.** The root `[0, T)` and the suspend frames form a laminar family. -/
theorem frames_laminar (hx : IsWalk x) :
    ∀ F ∈ insert (0, T) (suspendFrames x T), ∀ G ∈ insert (0, T) (suspendFrames x T),
      (G.1 ≤ F.1 ∧ F.2 ≤ G.2) ∨ (F.1 ≤ G.1 ∧ G.2 ≤ F.2) ∨ F.2 ≤ G.1 ∨ G.2 ≤ F.1 := by
  intro F hF G hG
  rcases mem_insert.mp hF with rfl | hF <;> rcases mem_insert.mp hG with rfl | hG
  · exact Or.inl ⟨le_rfl, le_rfl⟩
  · obtain ⟨τ', hτ', hGτ'⟩ := mem_suspendFrames.mp hG
    exact Or.inr (Or.inl ⟨Nat.zero_le _, framesOf_le_T hx hτ' hGτ'⟩)
  · obtain ⟨τ, hτ, hFτ⟩ := mem_suspendFrames.mp hF
    exact Or.inl ⟨Nat.zero_le _, framesOf_le_T hx hτ hFτ⟩
  · obtain ⟨τ, hτ, hFτ⟩ := mem_suspendFrames.mp hF
    obtain ⟨τ', hτ', hGτ'⟩ := mem_suspendFrames.mp hG
    have hbF := framesOf_bounds hx hτ hFτ
    have hbG := framesOf_bounds hx hτ' hGτ'
    rcases exc_laminar hx hτ hτ' with h | h | h | h
    · exact framesOf_laminar_of_nested hx hτ hτ' h.1 h.2 hFτ hGτ'
    · have := framesOf_laminar_of_nested hx hτ' hτ h.1 h.2 hGτ' hFτ
      omega
    · right; right; left; omega
    · right; right; right; omega

/-! ### The frame system of class U -/

/-- **The frame system of class U** for one walk: the root `[0, T)` and the suspend frames, with
the restart points of class U. -/
noncomputable def upperFrames (x : ℕ → ℤ) (T : ℕ) (hx : IsWalk x) : FrameSystem where
  T := T
  x := x
  frames := insert (0, T) (suspendFrames x T)
  R := restartPts x T
  root_mem := mem_insert_self _ _
  bounds := fun F hF => by
    rcases mem_insert.mp hF with rfl | hF
    · exact le_rfl
    · obtain ⟨τ, hτ, hFτ⟩ := mem_suspendFrames.mp hF
      exact framesOf_le_T hx hτ hFτ
  laminar := frames_laminar hx

@[simp] theorem upperFrames_T (hx : IsWalk x) : (upperFrames x T hx).T = T := rfl

@[simp] theorem upperFrames_x (hx : IsWalk x) : (upperFrames x T hx).x = x := rfl

/-! ### Ladder times -/

/-- **Ladder times are not suspended.** A ladder time of a top `τ` (`τ`, or `L τ z` or `D τ z`
with `base τ ≤ z < x τ`) lies in no frame of a top `τ'` whose canonical excursion is nested in
that of `τ`: neither in a frame of `τ` itself nor in a frame of a descendant. -/
theorem ladder_time_not_mem_framesOf (hx : IsWalk x) (hτ : τ ∈ tops x T) (hτ' : τ' ∈ tops x T)
    (h1 : (exc x T τ).1 ≤ (exc x T τ').1) (h2 : (exc x T τ').2 ≤ (exc x T τ).2) {t : ℕ}
    (ht : t = τ ∨ ∃ z, base x T τ ≤ z ∧ z < x τ ∧ (t = ladL x T τ z ∨ t = ladD x T τ z))
    {F : ℕ × ℕ} (hF : F ∈ framesOf x T τ') : ¬ (F.1 ≤ t ∧ t < F.2) := by
  rintro ⟨hF1, hF2⟩
  by_cases hne : τ = τ'
  · subst hne
    obtain ⟨w, hw, rfl | rfl⟩ := mem_framesOf.mp hF <;> obtain ⟨hw1, hw2⟩ := mem_levels.mp hw
    · -- the hanging frame `[L (w - 1) + 1, L w)`
      have hLw := ladL_lt hx hw1.le hw2
      change ladL x T τ (w - 1) + 1 ≤ t at hF1
      change t < ladL x T τ w at hF2
      rcases ht with rfl | ⟨z, hz1, hz2, rfl | rfl⟩
      · omega
      · rcases le_or_gt z (w - 1) with h | h
        · have := (ladL_le_ladL hx hz1 h (by omega)).1
          omega
        · have := (ladL_le_ladL hx hw1.le (show w ≤ z by omega) hz2).1
          omega
      · have := lt_ladD hx hz1 hz2
        omega
    · -- the descent frame `[D w + 1, D (w - 1))`
      have hDw := lt_ladD hx hw1.le hw2
      change ladD x T τ w + 1 ≤ t at hF1
      change t < ladD x T τ (w - 1) at hF2
      rcases ht with rfl | ⟨z, hz1, hz2, rfl | rfl⟩
      · omega
      · have := ladL_lt hx hz1 hz2
        omega
      · rcases le_or_gt z (w - 1) with h | h
        · have := (ladL_le_ladL hx hz1 h (by omega)).2
          omega
        · have := (ladL_le_ladL hx hw1.le (show w ≤ z by omega) hz2).2
          omega
  · -- a descendant: `t` lies strictly inside `exc τ'`, which avoids `τ`
    have hb := framesOf_bounds hx hτ' hF
    have hu' := isUpperHop_exc hx hτ'
    have hnot : ¬ ((exc x T τ').1 ≤ τ ∧ τ ≤ (exc x T τ').2) := fun h =>
      hne (top_eq_of_mem hx hτ (exc_mem hx hτ) (exc_mem hx hτ') h1 h2 h.1 h.2)
    rcases ht with rfl | ⟨z, hz1, hz2, rfl | rfl⟩
    · exact hnot ⟨by omega, by omega⟩
    · have := ladL_lt hx hz1 hz2
      exact not_lt_ladL_lt hx hz1 hz2 hu' (by omega) ⟨by omega, by omega⟩
    · have := lt_ladD hx hz1 hz2
      exact not_lt_ladD_lt hx hz1 hz2 hu' (by omega) ⟨by omega, by omega⟩

end BoundedStackDepth

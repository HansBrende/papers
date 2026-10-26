import BoundedNesting.OneWalk

/-!
# Nested strips for one arbitrary walk (the head-0 part of Theorem M)

Fix widths `W i ≥ 2` with `W i ∣ W j` for `i ≤ j`, and a residue `ρ`. The level-`i` lines are the
cells congruent to `ρ` modulo `W i` (`LineAt`), and the level-`i` strips are the sets of cells
strictly between consecutive level-`i` lines (`stripAt`). Every level-`j` line is a level-`i` line
for `i ≤ j` (`LineAt.mono`).

For a walk `x0`, the level-`0` counter of a strip `S` counts the visits to `S` (`visits`), and the
level-`i` counter, `i ≥ 1`, counts the entries into `S` from a level-`i` line (`entries`). The
counter of level `i` at time `t` is that of the strip of `x0 t` (`lcnt`).

* `strip_const`: a walk segment that avoids the lines of a level stays in one strip of that level.
* `lcnt_chord_eq`, `lcnt_chord_lt`: for a chord `(p, u)` at a cell that is not a line, of deciding level
  `lev` (`chordLevel`), the counters above `lev` do not change from `p` to `u`, and the counter of
  level `lev` rises.
* `lcnt_window_eq`: if the walk visits no level-`i` line strictly between two times at which it is
  not on a line, the counters of levels `≥ i` do not change.
* `lcnt_state_zero`, `lcnt_state_pos`: along a state edge between non-line times, the level-`0` counter
  rises by one and the others do not change.
* `card_chords_span_le`: at most `W i - 1` chords at cells of one level-`i` strip span a given time.
-/

namespace BoundedNesting

open Finset

/-! ### Strips along a walk -/

/-- A walk segment that avoids the lines stays in one strip. -/
theorem strip_const {x : ℕ → ℤ} (hx : IsWalk x) {w : ℕ} (hw : 2 ≤ w) {ρ : ℤ}
    (hρ : 0 ≤ ρ ∧ ρ < w) {a b : ℕ} (hnl : ∀ t, a ≤ t → t ≤ b → ¬ IsLine w ρ (x t)) :
    ∀ t, a ≤ t → t ≤ b → strip w ρ (x t) = strip w ρ (x a) := by
  intro t hat htb
  induction t, hat using Nat.le_induction with
  | base => rfl
  | succ t hat ih =>
    rw [← ih (by omega)]
    have hstep := hx.step t
    have h1 := hnl t hat (by omega)
    have h2 := hnl (t + 1) (by omega) htb
    rcases (show x (t + 1) = x t ∨ x (t + 1) = x t + 1 ∨ x t = x (t + 1) + 1 by omega)
      with e | e | e
    · rw [e]
    · exact (strip_eq_of_adj hw hρ e h2).symm
    · exact strip_eq_of_adj hw hρ e h1

/-- At most `w - 1` hops of a walk at cells of one strip span a given time. -/
theorem card_hops_span_strip_le (x : ℕ → ℤ) (T : ℕ) {w : ℕ} (hw : 2 ≤ w) {ρ : ℤ}
    (hρ : 0 ≤ ρ ∧ ρ < w) (τ : ℕ) (S : ℤ) :
    ((hops x T).filter fun e => ¬ IsLine w ρ (x e.1) ∧ strip w ρ (x e.1) = S ∧
      e.1 < τ ∧ τ ≤ e.2).card ≤ w - 1 := by
  calc ((hops x T).filter fun e => ¬ IsLine w ρ (x e.1) ∧ strip w ρ (x e.1) = S ∧
        e.1 < τ ∧ τ ≤ e.2).card ≤ (Ico 1 w).card := by
        refine card_le_card_of_injOn (fun e => ((x e.1 - ρ) % w).toNat) (fun e he => ?_)
          (fun e he e' he' h => ?_)
        · obtain ⟨-, hnl, -, -, -⟩ := mem_filter.mp (Finset.mem_coe.mp he)
          have ho := offset_spec hw hρ hnl
          have h0 : 0 ≤ (x e.1 - ρ) % w := by omega
          refine Finset.mem_coe.mpr (mem_Ico.mpr ⟨?_, (Int.toNat_lt h0).mpr ho.2.1⟩)
          have h3 := Int.toNat_of_nonneg h0
          have h4 := ho.1
          rw [← h3] at h4
          exact_mod_cast h4
        · obtain ⟨hh, hnl, hS, hτ1, hτ2⟩ := mem_filter.mp (Finset.mem_coe.mp he)
          obtain ⟨hh', hnl', hS', hτ1', hτ2'⟩ := mem_filter.mp (Finset.mem_coe.mp he')
          simp only at h
          have ho := offset_spec hw hρ hnl
          have ho' := offset_spec hw hρ hnl'
          have hoff : (x e.1 - ρ) % w = (x e'.1 - ρ) % w := by
            rw [← Int.toNat_of_nonneg (show 0 ≤ (x e.1 - ρ) % w by omega),
              ← Int.toNat_of_nonneg (show 0 ≤ (x e'.1 - ρ) % w by omega), h]
          have hcell : x e.1 = x e'.1 := by rw [ho.2.2, ho'.2.2, hS, hS', hoff]
          obtain ⟨hp, hu⟩ := hop_unique (mem_hops.mp hh) (mem_hops.mp hh') hcell ⟨hτ1, hτ2⟩
            ⟨hτ1', hτ2'⟩
          exact Prod.ext hp hu
    _ = w - 1 := Nat.card_Ico 1 w

/-! ### Levels -/

section Levels

variable (W : ℕ → ℕ) (ρ : ℕ)

/-- The residue of `ρ` at level `i`. -/
def res (i : ℕ) : ℤ := ((ρ % W i : ℕ) : ℤ)

/-- Level-`i` lines: the cells congruent to `ρ` modulo `W i`. -/
def LineAt (i : ℕ) (c : ℤ) : Prop := IsLine (W i) (res W ρ i) c

instance (i : ℕ) (c : ℤ) : Decidable (LineAt W ρ i c) := by unfold LineAt; infer_instance

/-- The level-`i` strip of a cell. -/
def stripAt (i : ℕ) (c : ℤ) : ℤ := strip (W i) (res W ρ i) c

variable {W ρ}

theorem res_bounds (hW : ∀ i, 2 ≤ W i) (i : ℕ) : 0 ≤ res W ρ i ∧ res W ρ i < W i := by
  unfold res
  have := Nat.mod_lt ρ (show 0 < W i by have := hW i; omega)
  exact ⟨by positivity, by exact_mod_cast this⟩

/-- Every level-`j` line is a level-`i` line for `i ≤ j`. -/
theorem LineAt.mono (hdiv : ∀ i j, i ≤ j → W i ∣ W j) {i j : ℕ} (hij : i ≤ j) {c : ℤ}
    (h : LineAt W ρ j c) : LineAt W ρ i c := by
  unfold LineAt IsLine res at *
  have hd : (W i : ℤ) ∣ (W j : ℤ) := by exact_mod_cast hdiv i j hij
  have e1 : c % (W i : ℤ) = (c % (W j : ℤ)) % (W i : ℤ) := (Int.emod_emod_of_dvd c hd).symm
  have e2 : ((ρ % W i : ℕ) : ℤ) = (((ρ % W j : ℕ) : ℤ)) % (W i : ℤ) := by
    have : (ρ % W j) % W i = ρ % W i := Nat.mod_mod_of_dvd ρ (hdiv i j hij)
    rw [← this]
    push_cast
    rfl
  rw [e1, h, e2]

end Levels

/-! ### Counters -/

section Counters

variable (x0 : ℕ → ℤ) (W : ℕ → ℕ) (ρ : ℕ)

/-- The level-`0` counter of the strip `S`: the visits to `S` up to time `t`. -/
def visits (S : ℤ) (t : ℕ) : ℕ :=
  ((range (t + 1)).filter fun s => ¬ LineAt W ρ 0 (x0 s) ∧ stripAt W ρ 0 (x0 s) = S).card

/-- The level-`i` counter of the strip `S`: the entries into `S` from a level-`i` line up to `t`. -/
def entries' (i : ℕ) (S : ℤ) (t : ℕ) : ℕ :=
  ((range (t + 1)).filter fun s => 1 ≤ s ∧ ¬ LineAt W ρ i (x0 s) ∧ stripAt W ρ i (x0 s) = S ∧
    LineAt W ρ i (x0 (s - 1))).card

/-- The counter of level `i` at time `t`: that of the strip of `x0 t`. -/
def lcnt (i t : ℕ) : ℕ :=
  if i = 0 then visits x0 W ρ (stripAt W ρ 0 (x0 t)) t
  else entries' x0 W ρ i (stripAt W ρ i (x0 t)) t

/-- The deciding level of a chord `(p, u)`: the largest level `i ≤ q` whose lines the walk visits
strictly between `p` and `u`, or `0`. -/
def chordLevel (q p u : ℕ) : ℕ :=
  ((range (q + 1)).filter fun i => ∃ t ∈ Ioo p u, LineAt W ρ i (x0 t)).sup id

variable {x0 W ρ}

theorem visits_mono (S : ℤ) {t t' : ℕ} (h : t ≤ t') : visits x0 W ρ S t ≤ visits x0 W ρ S t' :=
  card_le_card fun s hs => by
    obtain ⟨h1, h2⟩ := mem_filter.mp hs
    exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp h1; omega), h2⟩

theorem entries'_mono (i : ℕ) (S : ℤ) {t t' : ℕ} (h : t ≤ t') :
    entries' x0 W ρ i S t ≤ entries' x0 W ρ i S t' :=
  card_le_card fun s hs => by
    obtain ⟨h1, h2⟩ := mem_filter.mp hs
    exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp h1; omega), h2⟩

theorem chordLevel_le (q p u : ℕ) : chordLevel x0 W ρ q p u ≤ q := by
  unfold chordLevel
  refine Finset.sup_le fun i hi => ?_
  have := mem_range.mp (mem_filter.mp hi).1
  simp only [id]
  omega

/-- Above the deciding level the excursion visits no line. -/
theorem not_line_of_gt_chordLevel {q p u i : ℕ} (hi : chordLevel x0 W ρ q p u < i) (hiq : i ≤ q)
    {t : ℕ} (ht : t ∈ Ioo p u) : ¬ LineAt W ρ i (x0 t) := by
  intro h
  have hmem : i ∈ (range (q + 1)).filter fun i => ∃ t ∈ Ioo p u, LineAt W ρ i (x0 t) :=
    mem_filter.mpr ⟨mem_range.mpr (by omega), t, ht, h⟩
  have := Finset.le_sup (f := id) hmem
  simp only [id] at this
  unfold chordLevel at hi
  omega

/-- At a positive deciding level the excursion visits a line of that level. -/
theorem exists_line_of_chordLevel {q p u : ℕ} (hpos : 1 ≤ chordLevel x0 W ρ q p u) :
    ∃ t ∈ Ioo p u, LineAt W ρ (chordLevel x0 W ρ q p u) (x0 t) := by
  unfold chordLevel at *
  set s := (range (q + 1)).filter fun i => ∃ t ∈ Ioo p u, LineAt W ρ i (x0 t)
  have hne : s.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sup_empty] at hpos
    simp at hpos
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup s hne id
  rw [he]
  exact (mem_filter.mp hi).2

end Counters

/-! ### The counters along chords, hops and state edges -/

section Analysis

variable {x0 : ℕ → ℤ} {W : ℕ → ℕ} {ρ : ℕ}
variable (hx0 : IsWalk x0) (hW : ∀ i, 2 ≤ W i) (hdiv : ∀ i j, i ≤ j → W i ∣ W j)

theorem not_lineAt_of_not_line0 {i : ℕ} {c : ℤ} (hdiv : ∀ i j, i ≤ j → W i ∣ W j)
    (h : ¬ LineAt W ρ 0 c) : ¬ LineAt W ρ i c := fun h' => h (h'.mono hdiv (Nat.zero_le i))

include hx0 hW in
/-- If the walk visits no level-`i` line at the times `a, …, b`, it stays in one level-`i` strip. -/
theorem stripAt_const {i a b : ℕ} (hnl : ∀ t, a ≤ t → t ≤ b → ¬ LineAt W ρ i (x0 t)) :
    ∀ t, a ≤ t → t ≤ b → stripAt W ρ i (x0 t) = stripAt W ρ i (x0 a) :=
  strip_const hx0 (hW i) (res_bounds hW i) hnl

include hdiv in
/-- **Chords above their level.** For a chord `(p, u)` at a cell that is not a line, the counters of
the levels above the deciding level do not change from `p` to `u`. -/
theorem lcnt_chord_eq {T q p u : ℕ} (hγ : IsHop x0 T p u) (hc : ¬ LineAt W ρ 0 (x0 p)) {i : ℕ}
    (hi : chordLevel x0 W ρ q p u < i) (hiq : i ≤ q) : lcnt x0 W ρ i u = lcnt x0 W ρ i p := by
  have hi0 : i ≠ 0 := by omega
  have hcu : x0 u = x0 p := hγ.2.2.1
  unfold lcnt
  simp only [hi0, ↓reduceIte, hcu]
  unfold entries'
  congr 1
  ext s
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨hs, h1, h2, h3, h4⟩
    refine ⟨?_, h1, h2, h3, h4⟩
    by_contra hsp
    have hs1 : s - 1 < u := by omega
    rcases Nat.eq_or_lt_of_le (show p ≤ s - 1 by omega) with he | hlt
    · rw [← he] at h4
      exact not_lineAt_of_not_line0 hdiv hc h4
    · exact not_line_of_gt_chordLevel hi hiq (mem_Ioo.mpr ⟨hlt, hs1⟩) h4
  · rintro ⟨hs, h1⟩
    have := hγ.1
    exact ⟨by omega, h1⟩

include hx0 hW hdiv in
/-- **Chords at their level.** For a chord `(p, u)` at a cell that is not a line, the counter of
the deciding level rises from `p` to `u`: at level `0` by the visit at `u`, at a positive level by
the entry after the last visit to a line of that level. -/
theorem lcnt_chord_lt {T q p u : ℕ} (hγ : IsHop x0 T p u) (hc : ¬ LineAt W ρ 0 (x0 p)) :
    lcnt x0 W ρ (chordLevel x0 W ρ q p u) p < lcnt x0 W ρ (chordLevel x0 W ρ q p u) u := by
  classical
  have hcu : x0 u = x0 p := hγ.2.2.1
  have hlong := hγ.1
  set i := chordLevel x0 W ρ q p u
  by_cases hi0 : i = 0
  · unfold lcnt
    simp only [hi0, ↓reduceIte, hcu]
    unfold visits
    refine card_lt_card ⟨fun s hs => ?_, fun hsub => ?_⟩
    · obtain ⟨h1, h2⟩ := mem_filter.mp hs
      exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp h1; omega), h2⟩
    · have := mem_filter.mp (hsub (mem_filter.mpr ⟨mem_range.mpr (by omega : u < u + 1), by
        rw [hcu]; exact hc, by rw [hcu]⟩))
      have := mem_range.mp this.1
      omega
  · -- the last visit to a level-`i` line inside the chord
    obtain ⟨t0, ht0, hl0⟩ := exists_line_of_chordLevel (x0 := x0) (W := W) (ρ := ρ) (q := q)
      (p := p) (u := u) (by omega)
    set L := (Ioo p u).filter fun t => LineAt W ρ i (x0 t)
    have hne : L.Nonempty := ⟨t0, mem_filter.mpr ⟨ht0, hl0⟩⟩
    set t1 := L.max' hne
    obtain ⟨ht1, hl1⟩ := mem_filter.mp (L.max'_mem hne)
    obtain ⟨ht1a, ht1b⟩ := mem_Ioo.mp ht1
    have hnl : ∀ t, t1 + 1 ≤ t → t ≤ u → ¬ LineAt W ρ i (x0 t) := by
      intro t h1 h2 hl
      rcases Nat.eq_or_lt_of_le h2 with he | hlt
      · rw [he, hcu] at hl
        exact not_lineAt_of_not_line0 hdiv hc hl
      · have := L.le_max' t (mem_filter.mpr ⟨mem_Ioo.mpr ⟨by omega, hlt⟩, hl⟩)
        omega
    have hstrip := stripAt_const hx0 hW hnl
    unfold lcnt
    simp only [hi0, ↓reduceIte, hcu]
    unfold entries'
    refine card_lt_card ⟨fun s hs => ?_, fun hsub => ?_⟩
    · obtain ⟨h1, h2⟩ := mem_filter.mp hs
      exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp h1; omega), h2⟩
    · have hmem := hsub (mem_filter.mpr ⟨mem_range.mpr (by omega : t1 + 1 < u + 1), by omega,
        hnl (t1 + 1) le_rfl (by omega), by
          rw [hstrip (t1 + 1) le_rfl (by omega), ← hstrip u (by omega) le_rfl, hcu],
        by simpa using hl1⟩)
      have := mem_range.mp (mem_filter.mp hmem).1
      omega

include hx0 hW hdiv in
/-- **Hops without line visits.** If the walk visits no level-`i` line strictly between `p < u`,
and is not on a line at `p` and `u`, the counters of all levels `≥ i ≥ 1` do not change. -/
theorem lcnt_window_eq {p u i : ℕ} (hpu : p < u) (hi1 : 1 ≤ i) (hp : ¬ LineAt W ρ 0 (x0 p))
    (hu : ¬ LineAt W ρ 0 (x0 u)) (hnl : ∀ t ∈ Ioo p u, ¬ LineAt W ρ i (x0 t)) {i' : ℕ}
    (hii : i ≤ i') : lcnt x0 W ρ i' u = lcnt x0 W ρ i' p := by
  have hi0 : i' ≠ 0 := by omega
  have hnl' : ∀ t, p ≤ t → t ≤ u → ¬ LineAt W ρ i' (x0 t) := by
    intro t h1 h2 hl
    rcases Nat.eq_or_lt_of_le h1 with he | hlt
    · rw [← he] at hl; exact not_lineAt_of_not_line0 hdiv hp hl
    rcases Nat.eq_or_lt_of_le h2 with he' | hlt'
    · rw [he'] at hl; exact not_lineAt_of_not_line0 hdiv hu hl
    exact hnl t (mem_Ioo.mpr ⟨hlt, hlt'⟩) (hl.mono hdiv hii)
  have hstrip := stripAt_const hx0 hW hnl'
  unfold lcnt
  simp only [hi0, ↓reduceIte]
  rw [hstrip u hpu.le le_rfl]
  unfold entries'
  congr 1
  ext s
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨hs, h1, h2, h3, h4⟩
    refine ⟨?_, h1, h2, h3, h4⟩
    by_contra hsp
    exact hnl' (s - 1) (by omega) (by omega) h4
  · rintro ⟨hs, h1⟩
    exact ⟨by omega, h1⟩

include hx0 hW in
/-- **State edges, level `0`.** Between non-line times the level-`0` counter rises by one. -/
theorem lcnt_state_zero {t : ℕ} (ht : 1 ≤ t) (h1 : ¬ LineAt W ρ 0 (x0 t))
    (h2 : ¬ LineAt W ρ 0 (x0 (t - 1))) : lcnt x0 W ρ 0 t = lcnt x0 W ρ 0 (t - 1) + 1 := by
  have hS : stripAt W ρ 0 (x0 t) = stripAt W ρ 0 (x0 (t - 1)) :=
    stripAt_const hx0 hW (a := t - 1) (b := t) (fun s hs1 hs2 => by
      rcases (show s = t - 1 ∨ s = t by omega) with rfl | rfl
      · exact h2
      · exact h1) t (by omega) le_rfl
  unfold lcnt
  simp only [↓reduceIte]
  rw [hS]
  unfold visits
  conv_lhs => rw [show t + 1 = (t - 1 + 1) + 1 by omega, range_add_one, filter_insert]
  simp only [show t - 1 + 1 = t by omega, h1, not_false_eq_true, true_and, hS, ↓reduceIte]
  rw [card_insert_of_notMem (by simp)]

include hx0 hW hdiv in
/-- **State edges, positive levels.** Between non-line times the counters of positive levels do not
change. -/
theorem lcnt_state_pos {t i : ℕ} (ht : 1 ≤ t) (hi : 1 ≤ i) (h1 : ¬ LineAt W ρ 0 (x0 t))
    (h2 : ¬ LineAt W ρ 0 (x0 (t - 1))) : lcnt x0 W ρ i t = lcnt x0 W ρ i (t - 1) := by
  have := lcnt_window_eq hx0 hW hdiv (p := t - 1) (u := t) (i := i) (by omega) hi h2 h1
    (fun s hs => by have := mem_Ioo.mp hs; omega) le_rfl
  rw [this]

end Analysis

end BoundedNesting

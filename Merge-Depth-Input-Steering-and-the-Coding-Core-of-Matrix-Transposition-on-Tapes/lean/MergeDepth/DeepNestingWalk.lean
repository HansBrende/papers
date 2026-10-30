import MergeDepth.BlockPairsBlindness

/-!
# The deep-nesting walk `U(s₀, m, 1)` and its turns (the eighth paper's Section 2.5)

The walk `U = U(s₀, m, 1)` of the eighth paper (Section 2.5, after the fourth paper's
Definition 5.3), with `Λ = 2^{s₀}`, `R_i = 2^{s₀ - i}`, `Π_i = (m - i + 1) R_i` and `P = 4Π₀`
(`scaleR`, `strokeLen`, `dnpPeriod` of the tenth paper's library). A level-`m` stroke of direction
`σ` is `R_m` steps `σ`; for `i < m` a level-`i` stroke of direction `σ` is a segment of `R_i` steps
`σ` followed by a V of level `i + 1`: a back stroke of level `i + 1` and direction `-σ`, then a
forward stroke of level `i + 1` and direction `σ`. `U` is `P`-periodic, `U(0) = 0`, and over one
period its steps are those of four level-`0` strokes of directions `1, -1, -1, 1`.

* `strokePos s0 m i o`: the displacement after `o` steps of a level-`i` stroke of direction `+1`,
  with its recursion (`strokePos_seg`, `strokePos_back`, `strokePos_fwd`, `strokePos_end`) and range
  (`strokePos_mem`, `strokePos_mem_V`); `strokeDir`: its steps, `±1` (`strokeDir_pm`), and
  `strokeDir_ne_iff`: the offsets where the step changes inside a stroke are those of
  `strokeTurns` (`BlockPairsBlindness`).
* **`dnpWalk s0 m : ℤ → ℤ`**, the walk `U`; `dnpWalk_stroke`: on the `q`-th level-`0` stroke of a
  period it is `zeroStart q + zeroSign q * strokePos 0 o`; `dnpWalk_add_mul_period`; `dnpStep_pm`:
  no pauses.
* `IsTurnZ x t`: a turn of a walk (`x(t+1) - x(t) ≠ x(t) - x(t-1)`). **`isTurnZ_dnpWalk_iff`**: the
  turns of `U` are exactly the times whose residue lies in `periodTurns` (the apex and valley times
  of the V's of levels `1, …, m` and the tips `Π₀`, `3Π₀`), the fourth paper's Lemma 5.4 as quoted
  in the eighth paper's Section 2.5.
* `IsTurnOfLevel s0 m τ l`: `τ` is a turn of level `l` (the level of its V, `0` at the tips);
  `isTurnZ_iff_exists_level`, `IsTurnOfLevel.unique`, `isTurnOfLevel_apex`,
  `isTurnOfLevel_valley`, `isTurnOfLevel_tip`, and `isTurnOfLevel_ge_of_span`: turns in the span of a
  level-`k` V have levels `≥ k` (from `vApicesAux_nest`).
* `dnpWalk_parent`, **`dnpWalk_V`**: the apices `periodVApices s0 m k` are the apex times of the
  level-`k` V's of `U`: the walk arrives along a segment of `R_{k-1}` steps of some direction `σ`,
  then makes a back stroke of level `k` and direction `-σ` and a forward stroke of level `k` and
  direction `σ`.
-/

namespace MergeDepth

open Finset DirectedReciprocity

/-! ### Strokes -/

/-- The displacement after `o` steps of a stroke of level `i` and direction `+1` with remaining
nesting depth `d` (`d = m - i`). -/
def strokePosAux (s0 m : ℕ) : ℕ → ℕ → ℕ → ℤ
  | _, 0, o => o
  | i, d + 1, o =>
    if o < scaleR s0 i then o
    else if o - scaleR s0 i < strokeLen s0 m (i + 1) then
      scaleR s0 i - strokePosAux s0 m (i + 1) d (o - scaleR s0 i)
    else scaleR s0 (i + 1) +
      strokePosAux s0 m (i + 1) d (o - scaleR s0 i - strokeLen s0 m (i + 1))

/-- The displacement after `o` steps of a level-`i` stroke of direction `+1` of `U(s₀, m, 1)`. -/
def strokePos (s0 m i o : ℕ) : ℤ := strokePosAux s0 m i (m - i) o

theorem strokePos_of_le {s0 m i : ℕ} (hi : m ≤ i) (o : ℕ) : strokePos s0 m i o = o := by
  unfold strokePos; rw [Nat.sub_eq_zero_of_le hi]; rfl

theorem strokePos_of_lt {s0 m i : ℕ} (hi : i < m) (o : ℕ) :
    strokePos s0 m i o =
      if o < scaleR s0 i then (o : ℤ)
      else if o - scaleR s0 i < strokeLen s0 m (i + 1) then
        scaleR s0 i - strokePos s0 m (i + 1) (o - scaleR s0 i)
      else scaleR s0 (i + 1) +
        strokePos s0 m (i + 1) (o - scaleR s0 i - strokeLen s0 m (i + 1)) := by
  unfold strokePos
  rw [show m - i = (m - (i + 1)) + 1 by omega]
  rfl

theorem strokePos_zero (s0 m i : ℕ) : strokePos s0 m i 0 = 0 := by
  rcases le_or_gt m i with hi | hi
  · rw [strokePos_of_le hi]; simp
  · rw [strokePos_of_lt hi]; simp [scaleR_pos s0 i]

theorem strokePos_seg {s0 m i o : ℕ} (ho : o ≤ scaleR s0 i) : strokePos s0 m i o = o := by
  rcases le_or_gt m i with hi | hi
  · exact strokePos_of_le hi o
  · rw [strokePos_of_lt hi]
    rcases lt_or_eq_of_le ho with h | h
    · simp [h]
    · subst h
      simp [strokeLen_pos, strokePos_zero]

theorem strokePos_end {s0 m : ℕ} (hms : m ≤ s0) :
    ∀ d i, i + d = m → strokePos s0 m i (strokeLen s0 m i) = scaleR s0 i := by
  intro d
  induction d with
  | zero =>
    intro i hi
    rw [strokePos_of_le (by omega)]
    unfold strokeLen; rw [show m - i + 1 = 1 by omega]; simp
  | succ d ih =>
    intro i hi
    have hsp := strokeLen_succ (s0 := s0) (m := m) (i := i) (by omega) hms
    have hR := scaleR_succ (s0 := s0) (i := i) (by omega)
    have hp := strokeLen_pos s0 m (i + 1)
    rw [strokePos_of_lt (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      show strokeLen s0 m i - scaleR s0 i - strokeLen s0 m (i + 1) = strokeLen s0 m (i + 1) by omega,
      ih (i + 1) (by omega)]
    push_cast [hR]; ring

theorem strokePos_back {s0 m i o : ℕ} (hi : i < m) (hms : m ≤ s0)
    (ho : o ≤ strokeLen s0 m (i + 1)) :
    strokePos s0 m i (scaleR s0 i + o) = scaleR s0 i - strokePos s0 m (i + 1) o := by
  rw [strokePos_of_lt hi, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  rcases lt_or_eq_of_le ho with h | h
  · rw [ite_eq_left h]
  · subst h
    rw [ite_eq_right (by omega), strokePos_end hms (m - (i + 1)) (i + 1) (by omega),
      show strokeLen s0 m (i + 1) - strokeLen s0 m (i + 1) = 0 by omega, strokePos_zero,
      scaleR_succ (s0 := s0) (i := i) (by omega)]
    push_cast; ring

theorem strokePos_fwd {s0 m i : ℕ} (hi : i < m) (o : ℕ) :
    strokePos s0 m i (scaleR s0 i + strokeLen s0 m (i + 1) + o) =
      scaleR s0 (i + 1) + strokePos s0 m (i + 1) o := by
  rw [strokePos_of_lt hi, ite_eq_right (by omega), ite_eq_right (by omega),
    show scaleR s0 i + strokeLen s0 m (i + 1) + o - scaleR s0 i - strokeLen s0 m (i + 1) = o by
      omega]

/-- A stroke of level `i` stays in `[0, R_i]`, and its V in `[R_{i+1}, R_i]`. -/
theorem strokePos_mem {s0 m : ℕ} (hms : m ≤ s0) :
    ∀ d i, i + d = m → ∀ o ≤ strokeLen s0 m i,
      0 ≤ strokePos s0 m i o ∧ strokePos s0 m i o ≤ scaleR s0 i := by
  intro d
  induction d with
  | zero =>
    intro i hi o ho
    rw [strokePos_of_le (by omega)]
    unfold strokeLen at ho; rw [show m - i + 1 = 1 by omega, one_mul] at ho
    exact ⟨by positivity, by exact_mod_cast ho⟩
  | succ d ih =>
    intro i hi o ho
    have hsp := strokeLen_succ (s0 := s0) (m := m) (i := i) (by omega) hms
    have hR := scaleR_succ (s0 := s0) (i := i) (by omega)
    rcases le_or_gt o (scaleR s0 i) with h1 | h1
    · rw [strokePos_seg h1]; exact ⟨by positivity, by exact_mod_cast h1⟩
    rcases le_or_gt o (scaleR s0 i + strokeLen s0 m (i + 1)) with h2 | h2
    · obtain ⟨o', rfl⟩ : ∃ o', o = scaleR s0 i + o' := ⟨o - scaleR s0 i, by omega⟩
      rw [strokePos_back (by omega) hms (by omega)]
      obtain ⟨a, b⟩ := ih (i + 1) (by omega) o' (by omega)
      push_cast [hR] at b ⊢; constructor <;> linarith
    · obtain ⟨o', rfl⟩ : ∃ o', o = scaleR s0 i + strokeLen s0 m (i + 1) + o' :=
        ⟨o - scaleR s0 i - strokeLen s0 m (i + 1), by omega⟩
      rw [strokePos_fwd (by omega)]
      obtain ⟨a, b⟩ := ih (i + 1) (by omega) o' (by omega)
      push_cast [hR] at b ⊢; constructor <;> linarith

/-- The V of a stroke of level `i < m` stays in `[R_{i+1}, R_i]`. -/
theorem strokePos_mem_V {s0 m i o : ℕ} (hms : m ≤ s0) (hi : i < m) (ho1 : scaleR s0 i ≤ o)
    (ho2 : o ≤ strokeLen s0 m i) :
    (scaleR s0 (i + 1) : ℤ) ≤ strokePos s0 m i o ∧ strokePos s0 m i o ≤ scaleR s0 i := by
  have hsp := strokeLen_succ (s0 := s0) (m := m) (i := i) hi hms
  have hR := scaleR_succ (s0 := s0) (i := i) (by omega)
  rcases le_or_gt o (scaleR s0 i + strokeLen s0 m (i + 1)) with h2 | h2
  · obtain ⟨o', rfl⟩ : ∃ o', o = scaleR s0 i + o' := ⟨o - scaleR s0 i, by omega⟩
    rw [strokePos_back hi hms (by omega)]
    obtain ⟨a, b⟩ := strokePos_mem hms (m - (i + 1)) (i + 1) (by omega) o' (by omega)
    push_cast [hR] at b ⊢; constructor <;> linarith
  · obtain ⟨o', rfl⟩ : ∃ o', o = scaleR s0 i + strokeLen s0 m (i + 1) + o' :=
      ⟨o - scaleR s0 i - strokeLen s0 m (i + 1), by omega⟩
    rw [strokePos_fwd hi]
    obtain ⟨a, b⟩ := strokePos_mem hms (m - (i + 1)) (i + 1) (by omega) o' (by omega)
    push_cast [hR] at b ⊢; constructor <;> linarith

/-! ### Steps and turns inside a stroke -/

/-- The step `o → o + 1` of a level-`i` stroke of direction `+1`. -/
def strokeDir (s0 m i o : ℕ) : ℤ := strokePos s0 m i (o + 1) - strokePos s0 m i o

theorem strokeDir_seg {s0 m i o : ℕ} (ho : o < scaleR s0 i) : strokeDir s0 m i o = 1 := by
  unfold strokeDir
  rw [strokePos_seg (by omega), strokePos_seg (by omega)]; push_cast; ring

theorem strokeDir_back {s0 m i o : ℕ} (hi : i < m) (hms : m ≤ s0)
    (ho : o < strokeLen s0 m (i + 1)) :
    strokeDir s0 m i (scaleR s0 i + o) = -strokeDir s0 m (i + 1) o := by
  unfold strokeDir
  rw [show scaleR s0 i + o + 1 = scaleR s0 i + (o + 1) by ring, strokePos_back hi hms (by omega),
    strokePos_back hi hms (by omega)]
  ring

theorem strokeDir_fwd {s0 m i : ℕ} (hi : i < m) (o : ℕ) :
    strokeDir s0 m i (scaleR s0 i + strokeLen s0 m (i + 1) + o) = strokeDir s0 m (i + 1) o := by
  unfold strokeDir
  rw [show scaleR s0 i + strokeLen s0 m (i + 1) + o + 1 =
    scaleR s0 i + strokeLen s0 m (i + 1) + (o + 1) by ring, strokePos_fwd hi, strokePos_fwd hi]
  ring

theorem strokeDir_zero (s0 m i : ℕ) : strokeDir s0 m i 0 = 1 :=
  strokeDir_seg (scaleR_pos s0 i)

theorem strokeDir_last {s0 m : ℕ} (hms : m ≤ s0) :
    ∀ d i, i + d = m → strokeDir s0 m i (strokeLen s0 m i - 1) = 1 := by
  intro d
  induction d with
  | zero =>
    intro i hi
    apply strokeDir_seg
    unfold strokeLen; rw [show m - i + 1 = 1 by omega, one_mul]
    have := scaleR_pos s0 i; omega
  | succ d ih =>
    intro i hi
    have hsp := strokeLen_succ (s0 := s0) (m := m) (i := i) (by omega) hms
    have hp := strokeLen_pos s0 m (i + 1)
    rw [show strokeLen s0 m i - 1 = scaleR s0 i + strokeLen s0 m (i + 1) +
      (strokeLen s0 m (i + 1) - 1) by omega, strokeDir_fwd (by omega)]
    exact ih (i + 1) (by omega)

theorem strokeDir_pm {s0 m : ℕ} (hms : m ≤ s0) :
    ∀ d i, i + d = m → ∀ o < strokeLen s0 m i, strokeDir s0 m i o = 1 ∨ strokeDir s0 m i o = -1 := by
  intro d
  induction d with
  | zero =>
    intro i hi o ho
    left; apply strokeDir_seg
    unfold strokeLen at ho; rw [show m - i + 1 = 1 by omega, one_mul] at ho; exact ho
  | succ d ih =>
    intro i hi o ho
    have hsp := strokeLen_succ (s0 := s0) (m := m) (i := i) (by omega) hms
    rcases lt_or_ge o (scaleR s0 i) with h1 | h1
    · exact Or.inl (strokeDir_seg h1)
    rcases lt_or_ge o (scaleR s0 i + strokeLen s0 m (i + 1)) with h2 | h2
    · obtain ⟨o', rfl⟩ : ∃ o', o = scaleR s0 i + o' := ⟨o - scaleR s0 i, by omega⟩
      rw [strokeDir_back (by omega) hms (by omega)]
      rcases ih (i + 1) (by omega) o' (by omega) with h | h <;> rw [h] <;> simp
    · obtain ⟨o', rfl⟩ : ∃ o', o = scaleR s0 i + strokeLen s0 m (i + 1) + o' :=
        ⟨o - scaleR s0 i - strokeLen s0 m (i + 1), by omega⟩
      rw [strokeDir_fwd (by omega)]
      exact ih (i + 1) (by omega) o' (by omega)

/-- The offsets of the turns inside a stroke are those of `strokeTurns`. -/
theorem strokeDir_ne_iff {s0 m : ℕ} (hms : m ≤ s0) :
    ∀ d i, i + d = m → ∀ o, 0 < o → o < strokeLen s0 m i →
      (strokeDir s0 m i o ≠ strokeDir s0 m i (o - 1) ↔ ∃ l, (o, l) ∈ strokeTurns s0 m i d) := by
  intro d
  induction d with
  | zero =>
    intro i hi o ho0 ho
    have hRm : o < scaleR s0 i := by
      unfold strokeLen at ho; rw [show m - i + 1 = 1 by omega, one_mul] at ho; exact ho
    simp [strokeTurns, strokeDir_seg hRm, strokeDir_seg (show o - 1 < scaleR s0 i by omega)]
  | succ d ih =>
    intro i hi o ho0 ho
    have hsp := strokeLen_succ (s0 := s0) (m := m) (i := i) (by omega) hms
    have hp := strokeLen_pos s0 m (i + 1)
    have hR1 := scaleR_pos s0 (i + 1)
    set R := scaleR s0 i
    set Q := strokeLen s0 m (i + 1)
    have hbd : ∀ x ∈ strokeTurns s0 m (i + 1) d, scaleR s0 (i + 1) ≤ x.1 ∧ x.1 < Q := by
      intro x hx
      obtain ⟨h1, -, -, h4, -⟩ := strokeTurns_gap hms d (i + 1) (by omega) x hx
      have := scaleR_pos s0 x.2
      exact ⟨h1, by omega⟩
    have hmem : ∀ l, (o, l) ∈ strokeTurns s0 m i (d + 1) ↔
        (o = R ∧ l = i + 1) ∨ (o = R + Q ∧ l = i + 1) ∨
        (∃ x ∈ strokeTurns s0 m (i + 1) d, o = R + x.1 ∧ l = x.2) ∨
        (∃ x ∈ strokeTurns s0 m (i + 1) d, o = R + Q + x.1 ∧ l = x.2) := by
      intro l
      simp only [strokeTurns, mem_union, mem_insert, mem_singleton, mem_image, Prod.mk.injEq]
      constructor
      · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨x, hx, h1, h2⟩) | ⟨x, hx, h1, h2⟩)
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨x, hx, h1.symm, h2.symm⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨x, hx, h1.symm, h2.symm⟩))
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨x, hx, h1, h2⟩ | ⟨x, hx, h1, h2⟩)
        · exact Or.inl (Or.inl (Or.inl ⟨h1, h2⟩))
        · exact Or.inl (Or.inl (Or.inr ⟨h1, h2⟩))
        · exact Or.inl (Or.inr ⟨x, hx, h1.symm, h2.symm⟩)
        · exact Or.inr ⟨x, hx, h1.symm, h2.symm⟩
    simp only [hmem]
    rcases lt_or_ge o R with h1 | h1
    · -- the segment
      rw [strokeDir_seg h1, strokeDir_seg (show o - 1 < R by omega)]
      simp only [ne_eq, not_true_eq_false, false_iff, not_exists, not_or, not_and]
      intro l
      refine ⟨fun h => by omega, fun h => by omega, fun x hx h => by have := hbd x hx; omega,
        fun x hx h => by have := hbd x hx; omega⟩
    rcases eq_or_lt_of_le h1 with h1 | h1
    · -- the apex
      subst h1
      rw [show R = R + 0 by ring, strokeDir_back (by omega) hms hp, strokeDir_zero,
        show R + 0 - 1 = R - 1 by omega, strokeDir_seg (show R - 1 < R by omega)]
      simp only [add_zero]
      exact ⟨fun _ => ⟨i + 1, by simp⟩, fun _ => by norm_num⟩
    rcases lt_or_ge o (R + Q) with h2 | h2
    · -- inside the back stroke
      obtain ⟨o', rfl⟩ : ∃ o', o = R + o' := ⟨o - R, by omega⟩
      rw [strokeDir_back (by omega) hms (by omega), show R + o' - 1 = R + (o' - 1) by omega,
        strokeDir_back (by omega) hms (by omega), ne_eq, neg_inj, ← ne_eq,
        ih (i + 1) (by omega) o' (by omega) (by omega)]
      constructor
      · rintro ⟨l, hl⟩; exact ⟨l, Or.inr (Or.inr (Or.inl ⟨(o', l), hl, rfl, rfl⟩))⟩
      · rintro ⟨l, h | h | ⟨x, hx, h, hl⟩ | ⟨x, hx, h, hl⟩⟩
        · omega
        · omega
        · have : x = (o', l) := Prod.ext (by omega) hl.symm
          exact ⟨l, this ▸ hx⟩
        · have := hbd x hx; omega
    rcases eq_or_lt_of_le h2 with h2 | h2
    · -- the valley
      rw [← h2, show R + Q = R + Q + 0 by ring, strokeDir_fwd (by omega), strokeDir_zero,
        show R + Q + 0 - 1 = R + (Q - 1) by omega, strokeDir_back (by omega) hms (by omega),
        strokeDir_last hms d (i + 1) (by omega)]
      simp only [add_zero]
      exact ⟨fun _ => ⟨i + 1, by simp⟩, fun _ => by norm_num⟩
    · -- inside the forward stroke
      obtain ⟨o', rfl⟩ : ∃ o', o = R + Q + o' := ⟨o - R - Q, by omega⟩
      rw [strokeDir_fwd (by omega), show R + Q + o' - 1 = R + Q + (o' - 1) by omega,
        strokeDir_fwd (by omega), ih (i + 1) (by omega) o' (by omega) (by omega)]
      constructor
      · rintro ⟨l, hl⟩; exact ⟨l, Or.inr (Or.inr (Or.inr ⟨(o', l), hl, rfl, rfl⟩))⟩
      · rintro ⟨l, h | h | ⟨x, hx, h, hl⟩ | ⟨x, hx, h, hl⟩⟩
        · omega
        · omega
        · have := hbd x hx; omega
        · have : x = (o', l) := Prod.ext (by omega) hl.symm
          exact ⟨l, this ▸ hx⟩

/-! ### The walk -/

/-- The sign of the `q`-th level-`0` stroke of a period: the directions are `1, -1, -1, 1`. -/
def zeroSign (q : ℕ) : ℤ := if q = 1 ∨ q = 2 then -1 else 1

/-- The starting cell of the `q`-th level-`0` stroke of a period: `0, Λ, 0, -Λ`. -/
def zeroStart (s0 q : ℕ) : ℤ :=
  if q = 1 then (scaleR s0 0 : ℤ) else if q = 3 then -(scaleR s0 0 : ℤ) else 0

/-- **The deep-nesting walk** `U = U(s₀, m, 1)` on `ℤ` (the eighth paper's Section 2.5): it is
`P`-periodic, `U(0) = 0`, and over one period its steps are those of four level-`0` strokes of
directions `1, -1, -1, 1`. -/
def dnpWalk (s0 m : ℕ) (t : ℤ) : ℤ :=
  zeroStart s0 ((t % (dnpPeriod s0 m : ℤ)).toNat / strokeLen s0 m 0) +
    zeroSign ((t % (dnpPeriod s0 m : ℤ)).toNat / strokeLen s0 m 0) *
      strokePos s0 m 0 ((t % (dnpPeriod s0 m : ℤ)).toNat % strokeLen s0 m 0)

theorem dnpWalk_add_mul_period (s0 m : ℕ) (t n : ℤ) :
    dnpWalk s0 m (t + n * dnpPeriod s0 m) = dnpWalk s0 m t := by
  unfold dnpWalk; rw [Int.add_mul_emod_self_right]

theorem dnpWalk_of_lt {s0 m q o : ℕ} (hq : q < 4) (ho : o < strokeLen s0 m 0) :
    dnpWalk s0 m ((q * strokeLen s0 m 0 + o : ℕ) : ℤ) =
      zeroStart s0 q + zeroSign q * strokePos s0 m 0 o := by
  have hpi := strokeLen_pos s0 m 0
  have hlt : q * strokeLen s0 m 0 + o < dnpPeriod s0 m := by unfold dnpPeriod; nlinarith
  unfold dnpWalk
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt), Int.toNat_natCast]
  have h1 : (q * strokeLen s0 m 0 + o) / strokeLen s0 m 0 = q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpi, Nat.div_eq_of_lt ho, zero_add]
  have h2 : (q * strokeLen s0 m 0 + o) % strokeLen s0 m 0 = o := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ho]
  rw [h1, h2]

theorem dnpWalk_stroke {s0 m : ℕ} (hms : m ≤ s0) {q o : ℕ} (hq : q < 4)
    (ho : o ≤ strokeLen s0 m 0) :
    dnpWalk s0 m ((q * strokeLen s0 m 0 + o : ℕ) : ℤ) =
      zeroStart s0 q + zeroSign q * strokePos s0 m 0 o := by
  rcases lt_or_eq_of_le ho with ho | rfl
  · exact dnpWalk_of_lt hq ho
  rw [strokePos_end hms m 0 (by omega)]
  have hpi := strokeLen_pos s0 m 0
  rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [show 0 * strokeLen s0 m 0 + strokeLen s0 m 0 = 1 * strokeLen s0 m 0 + 0 by ring,
      dnpWalk_of_lt (by norm_num) hpi, strokePos_zero]
    simp [zeroStart, zeroSign]
  · rw [show 1 * strokeLen s0 m 0 + strokeLen s0 m 0 = 2 * strokeLen s0 m 0 + 0 by ring,
      dnpWalk_of_lt (by norm_num) hpi, strokePos_zero]
    simp [zeroStart, zeroSign]
  · rw [show 2 * strokeLen s0 m 0 + strokeLen s0 m 0 = 3 * strokeLen s0 m 0 + 0 by ring,
      dnpWalk_of_lt (by norm_num) hpi, strokePos_zero]
    simp [zeroStart, zeroSign]
  · have e : ((3 * strokeLen s0 m 0 + strokeLen s0 m 0 : ℕ) : ℤ) =
        ((0 * strokeLen s0 m 0 + 0 : ℕ) : ℤ) + 1 * dnpPeriod s0 m := by
      unfold dnpPeriod; push_cast; ring
    rw [e, dnpWalk_add_mul_period, dnpWalk_of_lt (by norm_num) hpi, strokePos_zero]
    simp [zeroStart, zeroSign]

theorem zeroSign_pm (q : ℕ) : zeroSign q = 1 ∨ zeroSign q = -1 := by
  unfold zeroSign; split_ifs <;> simp

/-- Every integer time is `q Π₀ + o` modulo `P`. -/
theorem time_decomp (s0 m : ℕ) (t : ℤ) : ∃ q o : ℕ, ∃ n : ℤ, q < 4 ∧ o < strokeLen s0 m 0 ∧
    t = ((q * strokeLen s0 m 0 + o : ℕ) : ℤ) + n * dnpPeriod s0 m ∧
    (t % (dnpPeriod s0 m : ℤ)).toNat = q * strokeLen s0 m 0 + o := by
  have hpi := strokeLen_pos s0 m 0
  have hP : (0 : ℤ) < dnpPeriod s0 m := by exact_mod_cast dnpPeriod_pos s0 m
  set r := (t % (dnpPeriod s0 m : ℤ)).toNat with hr
  have hr0 : ((r : ℕ) : ℤ) = t % (dnpPeriod s0 m : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hP.ne')
  have hrP : r < dnpPeriod s0 m := by
    have := Int.emod_lt_of_pos t hP; omega
  refine ⟨r / strokeLen s0 m 0, r % strokeLen s0 m 0, t / dnpPeriod s0 m, ?_, Nat.mod_lt _ hpi, ?_, ?_⟩
  · unfold dnpPeriod at hrP; exact Nat.div_lt_of_lt_mul (by linarith)
  · have h1 := Nat.div_add_mod r (strokeLen s0 m 0)
    have h2 := Int.emod_add_mul_ediv t (dnpPeriod s0 m)
    have h3 : ((r / strokeLen s0 m 0 * strokeLen s0 m 0 + r % strokeLen s0 m 0 : ℕ) : ℤ) = r := by
      rw [Nat.mul_comm]; exact_mod_cast h1
    rw [h3, hr0]; linarith
  · have h1 := Nat.div_add_mod r (strokeLen s0 m 0)
    rw [Nat.mul_comm] at h1; exact h1.symm

/-! ### Turns of `U` -/

/-- A **turn** of a walk `x : ℤ → ℤ` without pauses: a time `t` with
`x(t + 1) - x(t) ≠ x(t) - x(t - 1)`. -/
def IsTurnZ (x : ℤ → ℤ) (t : ℤ) : Prop := x (t + 1) - x t ≠ x t - x (t - 1)

/-- The step `t → t + 1` of `U`. -/
def dnpStep (s0 m : ℕ) (t : ℤ) : ℤ := dnpWalk s0 m (t + 1) - dnpWalk s0 m t

theorem dnpStep_add_mul_period (s0 m : ℕ) (t n : ℤ) :
    dnpStep s0 m (t + n * dnpPeriod s0 m) = dnpStep s0 m t := by
  unfold dnpStep
  rw [show t + n * dnpPeriod s0 m + 1 = (t + 1) + n * dnpPeriod s0 m by ring,
    dnpWalk_add_mul_period, dnpWalk_add_mul_period]

theorem dnpStep_offset {s0 m : ℕ} (hms : m ≤ s0) {q o : ℕ} (hq : q < 4)
    (ho : o < strokeLen s0 m 0) :
    dnpStep s0 m ((q * strokeLen s0 m 0 + o : ℕ) : ℤ) = zeroSign q * strokeDir s0 m 0 o := by
  unfold dnpStep
  rw [show ((q * strokeLen s0 m 0 + o : ℕ) : ℤ) + 1 = ((q * strokeLen s0 m 0 + (o + 1) : ℕ) : ℤ) by
    push_cast; ring, dnpWalk_stroke hms hq (by omega), dnpWalk_stroke hms hq ho.le]
  unfold strokeDir; ring

/-- `U` has no pauses: every step is `±1`. -/
theorem dnpStep_pm {s0 m : ℕ} (hms : m ≤ s0) (t : ℤ) : dnpStep s0 m t = 1 ∨ dnpStep s0 m t = -1 := by
  obtain ⟨q, o, n, hq, ho, rfl, -⟩ := time_decomp s0 m t
  rw [dnpStep_add_mul_period, dnpStep_offset hms hq ho]
  rcases zeroSign_pm q with h | h <;> rcases strokeDir_pm hms m 0 (by omega) o ho with h' | h' <;>
    simp [h, h']

theorem isTurnZ_dnpWalk_iff_step (s0 m : ℕ) (t : ℤ) :
    IsTurnZ (dnpWalk s0 m) t ↔ dnpStep s0 m t ≠ dnpStep s0 m (t - 1) := by
  unfold IsTurnZ dnpStep; rw [sub_add_cancel]

/-- The converse of `strokeTurnJumpAux_support`: the turns of a stroke are the apices and valleys of
its inner V's. -/
theorem strokeTurns_vApices {s0 m : ℕ} : ∀ d i o l, (o, l) ∈ strokeTurns s0 m i d →
    ∃ d' < d, l = i + 1 + d' ∧ (o ∈ vApicesAux s0 m i d' ∨
      ∃ β ∈ vApicesAux s0 m i d', o = β + strokeLen s0 m (i + 1 + d')) := by
  intro d
  induction d with
  | zero => intro i o l h; simp [strokeTurns] at h
  | succ d ih =>
    intro i o l h
    simp only [strokeTurns, mem_union, mem_insert, mem_singleton, mem_image, Prod.mk.injEq] at h
    rcases h with (((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨x, hx, h1, h2⟩) | ⟨x, hx, h1, h2⟩)
    · exact ⟨0, by omega, by ring, Or.inl (by simp [vApicesAux])⟩
    · exact ⟨0, by omega, by ring, Or.inr ⟨scaleR s0 i, by simp [vApicesAux], by ring⟩⟩
    · obtain ⟨d'', hd'', hl, hmem⟩ := ih (i + 1) x.1 x.2 hx
      refine ⟨d'' + 1, by omega, by omega, ?_⟩
      rcases hmem with hm | ⟨β, hβ, hβe⟩
      · left; rw [vApicesAux, mem_union, mem_image]; exact Or.inl ⟨x.1, hm, h1⟩
      · right; refine ⟨scaleR s0 i + β, ?_, ?_⟩
        · rw [vApicesAux, mem_union, mem_image]; exact Or.inl ⟨β, hβ, rfl⟩
        · rw [show i + 1 + (d'' + 1) = i + 1 + 1 + d'' by ring]; omega
    · obtain ⟨d'', hd'', hl, hmem⟩ := ih (i + 1) x.1 x.2 hx
      refine ⟨d'' + 1, by omega, by omega, ?_⟩
      rcases hmem with hm | ⟨β, hβ, hβe⟩
      · left; rw [vApicesAux, mem_union, mem_image, mem_image]; exact Or.inr ⟨x.1, hm, h1⟩
      · right; refine ⟨scaleR s0 i + strokeLen s0 m (i + 1) + β, ?_, ?_⟩
        · rw [vApicesAux, mem_union, mem_image, mem_image]; exact Or.inr ⟨β, hβ, rfl⟩
        · rw [show i + 1 + (d'' + 1) = i + 1 + 1 + d'' by ring]; omega

theorem mem_periodTurnsLevels_of_strokeTurns {s0 m q : ℕ} (hq : q < 4) {x : ℕ × ℕ}
    (hx : x ∈ strokeTurns s0 m 0 m) :
    (q * strokeLen s0 m 0 + x.1, x.2) ∈ periodTurnsLevels s0 m := by
  obtain ⟨d', hd', hl, hmem⟩ := strokeTurns_vApices m 0 x.1 x.2 hx
  unfold periodTurnsLevels
  rw [mem_biUnion]
  refine ⟨x.2, mem_Icc.mpr ⟨by omega, by omega⟩,
    mem_image.mpr ⟨q * strokeLen s0 m 0 + x.1, ?_, rfl⟩⟩
  have hk : x.2 - 1 = d' := by omega
  rcases hmem with hm | ⟨β, hβ, hβe⟩
  · apply mem_union_left; unfold periodVApices; rw [mem_biUnion]
    exact ⟨q, mem_range.mpr hq, mem_image.mpr ⟨x.1, by rw [hk]; exact hm, rfl⟩⟩
  · apply mem_union_right; rw [mem_image]
    refine ⟨q * strokeLen s0 m 0 + β, ?_, ?_⟩
    · unfold periodVApices; rw [mem_biUnion]
      exact ⟨q, mem_range.mpr hq, mem_image.mpr ⟨β, by rw [hk]; exact hβ, rfl⟩⟩
    · rw [hβe, hl]; ring

theorem mem_periodTurns_iff_levels {s0 m r : ℕ} :
    r ∈ periodTurns s0 m ↔ (r = strokeLen s0 m 0 ∨ r = 3 * strokeLen s0 m 0) ∨
      ∃ l, (r, l) ∈ periodTurnsLevels s0 m := by
  unfold periodTurns periodTurnsLevels
  simp only [mem_union, mem_biUnion, mem_insert, mem_singleton, mem_image, Prod.mk.injEq]
  constructor
  · rintro (⟨l, hl, h⟩ | h | h)
    · exact Or.inr ⟨l, l, hl, r, h, rfl, rfl⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
  · rintro ((h | h) | ⟨l, l', hl', τ, hτ, h1, h2⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · subst h1; exact Or.inl ⟨l', hl', hτ⟩

theorem periodTurns_iff_offset {s0 m : ℕ} (hms : m ≤ s0) {q o : ℕ} (hq : q < 4)
    (ho : o < strokeLen s0 m 0) :
    q * strokeLen s0 m 0 + o ∈ periodTurns s0 m ↔
      (o = 0 ∧ (q = 1 ∨ q = 3)) ∨ (0 < o ∧ ∃ l, (o, l) ∈ strokeTurns s0 m 0 m) := by
  have hpi := strokeLen_pos s0 m 0
  constructor
  · intro h
    rcases mem_periodTurns_cases h with h | h | ⟨q', hq', x, hx, h⟩
    · left; interval_cases q <;> omega
    · left; interval_cases q <;> omega
    · obtain ⟨h1, -, -, h4, -⟩ := strokeTurns_gap hms m 0 (by omega) x hx
      have := scaleR_pos s0 x.2
      have hR0 := scaleR_pos s0 0
      have hxo : x.1 = o := by interval_cases q <;> interval_cases q' <;> omega
      right; exact ⟨by omega, x.2, by rw [← hxo]; exact hx⟩
  · rintro (⟨rfl, rfl | rfl⟩ | ⟨ho0, l, hl⟩)
    · rw [mem_periodTurns_iff_levels]; left; left; ring
    · rw [mem_periodTurns_iff_levels]; left; right; ring
    · rw [mem_periodTurns_iff_levels]; right
      exact ⟨l, mem_periodTurnsLevels_of_strokeTurns hq (x := (o, l)) hl⟩

theorem isTurnZ_dnpWalk_offset {s0 m : ℕ} (hms : m ≤ s0) {q o : ℕ} (hq : q < 4)
    (ho : o < strokeLen s0 m 0) :
    IsTurnZ (dnpWalk s0 m) ((q * strokeLen s0 m 0 + o : ℕ) : ℤ) ↔
      (o = 0 ∧ (q = 1 ∨ q = 3)) ∨ (0 < o ∧ ∃ l, (o, l) ∈ strokeTurns s0 m 0 m) := by
  have hpi := strokeLen_pos s0 m 0
  rw [isTurnZ_dnpWalk_iff_step, dnpStep_offset hms hq ho]
  rcases Nat.eq_zero_or_pos o with rfl | ho0
  · rw [strokeDir_zero]
    have hprev : dnpStep s0 m (((q * strokeLen s0 m 0 + 0 : ℕ) : ℤ) - 1) =
        if q = 0 then 1 else zeroSign (q - 1) := by
      rcases Nat.eq_zero_or_pos q with rfl | hq0
      · have e : ((0 * strokeLen s0 m 0 + 0 : ℕ) : ℤ) - 1 =
            ((3 * strokeLen s0 m 0 + (strokeLen s0 m 0 - 1) : ℕ) : ℤ) + (-1) * dnpPeriod s0 m := by
          unfold dnpPeriod; push_cast [Nat.cast_sub (show 1 ≤ strokeLen s0 m 0 by omega)]; ring
        rw [e, dnpStep_add_mul_period, dnpStep_offset hms (by norm_num) (by omega),
          strokeDir_last hms m 0 (by omega)]
        simp [zeroSign]
      · have e : ((q * strokeLen s0 m 0 + 0 : ℕ) : ℤ) - 1 =
            (((q - 1) * strokeLen s0 m 0 + (strokeLen s0 m 0 - 1) : ℕ) : ℤ) := by
          have : (q - 1) * strokeLen s0 m 0 + strokeLen s0 m 0 = q * strokeLen s0 m 0 := by
            rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hq0]
          push_cast [Nat.cast_sub (show 1 ≤ strokeLen s0 m 0 by omega)]
          have h2 : (((q - 1) * strokeLen s0 m 0 : ℕ) : ℤ) + strokeLen s0 m 0 = q * strokeLen s0 m 0 := by
            exact_mod_cast this
          push_cast at h2; linarith
        rw [e, dnpStep_offset hms (by omega) (by omega), strokeDir_last hms m 0 (by omega),
          ite_eq_right (by omega)]
        ring
    rw [hprev]
    interval_cases q <;> simp [zeroSign]
  · have e : ((q * strokeLen s0 m 0 + o : ℕ) : ℤ) - 1 = ((q * strokeLen s0 m 0 + (o - 1) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub (show 1 ≤ o by omega)]; ring
    rw [e, dnpStep_offset hms hq (by omega)]
    have hz : zeroSign q ≠ 0 := by rcases zeroSign_pm q with h | h <;> rw [h] <;> norm_num
    rw [ne_eq, mul_right_inj' hz, ← ne_eq, strokeDir_ne_iff hms m 0 (by omega) o ho0 ho]
    constructor
    · intro h; exact Or.inr ⟨ho0, h⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · omega
      · exact h

/-- **The turns of `U`** are the times whose residue modulo `P` lies in `periodTurns`: the apex and
valley times of the V's of levels `1, …, m` and the tips `Π₀`, `3Π₀` (the fourth paper's Lemma 5.4,
as quoted in the eighth paper's Section 2.5). -/
theorem isTurnZ_dnpWalk_iff {s0 m : ℕ} (hms : m ≤ s0) (t : ℤ) :
    IsTurnZ (dnpWalk s0 m) t ↔ (t % (dnpPeriod s0 m : ℤ)).toNat ∈ periodTurns s0 m := by
  obtain ⟨q, o, n, hq, ho, rfl, hr⟩ := time_decomp s0 m t
  rw [hr, periodTurns_iff_offset hms hq ho, ← isTurnZ_dnpWalk_offset hms hq ho,
    isTurnZ_dnpWalk_iff_step, isTurnZ_dnpWalk_iff_step, dnpStep_add_mul_period,
    show ((q * strokeLen s0 m 0 + o : ℕ) : ℤ) + n * dnpPeriod s0 m - 1 =
      (((q * strokeLen s0 m 0 + o : ℕ) : ℤ) - 1) + n * dnpPeriod s0 m by ring, dnpStep_add_mul_period]

/-! ### Levels of turns -/

/-- `τ` is a **turn of `U` of level `l`**: its residue modulo `P` is the apex or the valley time of a
V of level `l ∈ [1, m]` (`periodTurnsLevels`), or `l = 0` and it is one of the tips `Π₀`, `3Π₀`. -/
def IsTurnOfLevel (s0 m : ℕ) (τ : ℤ) (l : ℕ) : Prop :=
  ((τ % (dnpPeriod s0 m : ℤ)).toNat, l) ∈ periodTurnsLevels s0 m ∨
    (l = 0 ∧ ((τ % (dnpPeriod s0 m : ℤ)).toNat = strokeLen s0 m 0 ∨
      (τ % (dnpPeriod s0 m : ℤ)).toNat = 3 * strokeLen s0 m 0))

instance (s0 m : ℕ) (τ : ℤ) (l : ℕ) : Decidable (IsTurnOfLevel s0 m τ l) := by
  unfold IsTurnOfLevel; infer_instance

theorem isTurnOfLevel_add_mul_period {s0 m : ℕ} (τ n : ℤ) (l : ℕ) :
    IsTurnOfLevel s0 m (τ + n * dnpPeriod s0 m) l ↔ IsTurnOfLevel s0 m τ l := by
  unfold IsTurnOfLevel; rw [Int.add_mul_emod_self_right]

/-- Every turn of `U` has a level, and only turns have levels. -/
theorem isTurnZ_iff_exists_level {s0 m : ℕ} (hms : m ≤ s0) (τ : ℤ) :
    IsTurnZ (dnpWalk s0 m) τ ↔ ∃ l, IsTurnOfLevel s0 m τ l := by
  rw [isTurnZ_dnpWalk_iff hms, mem_periodTurns_iff_levels]
  unfold IsTurnOfLevel
  constructor
  · rintro (h | ⟨l, hl⟩)
    · exact ⟨0, Or.inr ⟨rfl, h⟩⟩
    · exact ⟨l, Or.inl hl⟩
  · rintro ⟨l, hl | ⟨-, h⟩⟩
    · exact Or.inr ⟨l, hl⟩
    · exact Or.inl h

theorem IsTurnOfLevel.isTurnZ {s0 m : ℕ} (hms : m ≤ s0) {τ : ℤ} {l : ℕ}
    (h : IsTurnOfLevel s0 m τ l) : IsTurnZ (dnpWalk s0 m) τ :=
  (isTurnZ_iff_exists_level hms τ).2 ⟨l, h⟩

theorem IsTurnOfLevel.le_m {s0 m : ℕ} {τ : ℤ} {l : ℕ} (h : IsTurnOfLevel s0 m τ l) : l ≤ m := by
  rcases h with h | ⟨rfl, -⟩
  · obtain ⟨l', hl', h⟩ := mem_biUnion.mp h
    obtain ⟨τ', -, he⟩ := mem_image.mp h
    simp only [Prod.mk.injEq] at he
    rw [← he.2]; exact (mem_Icc.mp hl').2
  · omega

/-- **The level of a turn is unique.** -/
theorem IsTurnOfLevel.unique {s0 m : ℕ} (hms : m ≤ s0) {τ : ℤ} {l l' : ℕ}
    (h : IsTurnOfLevel s0 m τ l) (h' : IsTurnOfLevel s0 m τ l') : l = l' := by
  have hpi := strokeLen_pos s0 m 0
  have hR0 := scaleR_pos s0 0
  have key : ∀ {r l : ℕ}, (r, l) ∈ periodTurnsLevels s0 m →
      ∃ q < 4, ∃ y ∈ strokeTurns s0 m 0 m, r = q * strokeLen s0 m 0 + y.1 ∧ y.2 = l ∧
        scaleR s0 0 ≤ y.1 ∧ y.1 < strokeLen s0 m 0 := by
    intro r l hrl
    obtain ⟨-, -, -, q, hq, y, hy, h1, h2⟩ := mem_periodTurnsLevels hrl
    obtain ⟨k1, -, -, k4, -⟩ := strokeTurns_gap hms m 0 (by omega) y hy
    have := scaleR_pos s0 y.2
    exact ⟨q, hq, y, hy, h1, h2, k1, by omega⟩
  rcases h with h | ⟨rfl, ht⟩ <;> rcases h' with h' | ⟨rfl, ht'⟩
  · obtain ⟨q, hq, y, hy, h1, h2, h3, h4⟩ := key h
    obtain ⟨q', hq', y', hy', h1', h2', h3', h4'⟩ := key h'
    rw [← h2, ← h2']
    exact period_level_unique hms hq' hq hy' hy (h1'.symm.trans h1)
  · obtain ⟨q, hq, y, hy, h1, h2, h3, h4⟩ := key h
    exfalso; rcases ht' with ht' | ht' <;> rw [ht'] at h1 <;> interval_cases q <;> omega
  · obtain ⟨q, hq, y, hy, h1, h2, h3, h4⟩ := key h'
    exfalso; rcases ht with ht | ht <;> rw [ht] at h1 <;> interval_cases q <;> omega
  · rfl

theorem periodVApices_lt {s0 m l : ℕ} (hms : m ≤ s0) (hl1 : 1 ≤ l) (hlm : l ≤ m) {α : ℕ}
    (hα : α ∈ periodVApices s0 m l) : α + strokeLen s0 m l < dnpPeriod s0 m := by
  have := periodVApices_span_subset hl1 hlm hms hα
  have := strokeLen_pos s0 m l
  omega

theorem isTurnOfLevel_apex {s0 m l : ℕ} (hms : m ≤ s0) (hl1 : 1 ≤ l) (hlm : l ≤ m) {α : ℕ}
    (hα : α ∈ periodVApices s0 m l) (n : ℤ) :
    IsTurnOfLevel s0 m ((α : ℤ) + n * dnpPeriod s0 m) l := by
  rw [isTurnOfLevel_add_mul_period]
  have := periodVApices_lt hms hl1 hlm hα
  left
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (show α < dnpPeriod s0 m by omega)),
    Int.toNat_natCast]
  unfold periodTurnsLevels
  exact mem_biUnion.mpr ⟨l, mem_Icc.mpr ⟨hl1, hlm⟩, mem_image.mpr ⟨α, mem_union_left _ hα, rfl⟩⟩

theorem isTurnOfLevel_valley {s0 m l : ℕ} (hms : m ≤ s0) (hl1 : 1 ≤ l) (hlm : l ≤ m) {α : ℕ}
    (hα : α ∈ periodVApices s0 m l) (n : ℤ) :
    IsTurnOfLevel s0 m ((α : ℤ) + strokeLen s0 m l + n * dnpPeriod s0 m) l := by
  rw [isTurnOfLevel_add_mul_period]
  have := periodVApices_lt hms hl1 hlm hα
  left
  rw [show (α : ℤ) + strokeLen s0 m l = ((α + strokeLen s0 m l : ℕ) : ℤ) by push_cast; ring,
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast this), Int.toNat_natCast]
  unfold periodTurnsLevels
  exact mem_biUnion.mpr ⟨l, mem_Icc.mpr ⟨hl1, hlm⟩,
    mem_image.mpr ⟨α + strokeLen s0 m l, mem_union_right _ (mem_image.mpr ⟨α, hα, rfl⟩), rfl⟩⟩

theorem isTurnOfLevel_tip {s0 m : ℕ} (j : ℕ) (hj : j = 1 ∨ j = 3) (n : ℤ) :
    IsTurnOfLevel s0 m ((j * strokeLen s0 m 0 : ℕ) + n * dnpPeriod s0 m) 0 := by
  rw [isTurnOfLevel_add_mul_period]
  have hpi := strokeLen_pos s0 m 0
  right
  have hlt : j * strokeLen s0 m 0 < dnpPeriod s0 m := by
    unfold dnpPeriod; rcases hj with rfl | rfl <;> omega
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt), Int.toNat_natCast]
  rcases hj with rfl | rfl <;> simp

/-! ### Nesting of the V's -/

/-- A V of a coarser level never has its apex or valley inside the span of a V of a finer level. -/
theorem vApicesAux_nest {s0 m : ℕ} (hms : m ≤ s0) : ∀ d' i d, i + 1 + d ≤ m → d' < d →
    ∀ β' ∈ vApicesAux s0 m i d', ∀ β ∈ vApicesAux s0 m i d,
      (β' < β ∨ β + 2 * strokeLen s0 m (i + 1 + d) ≤ β') ∧
      (β' + strokeLen s0 m (i + 1 + d') < β ∨
        β + 2 * strokeLen s0 m (i + 1 + d) ≤ β' + strokeLen s0 m (i + 1 + d')) := by
  intro d'
  induction d' with
  | zero =>
    intro i d hd hd' β' hβ' β hβ
    rw [vApicesAux, mem_singleton] at hβ'
    subst hβ'
    obtain ⟨d, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have hsp := strokeLen_succ (s0 := s0) (m := m) (i := i) (by omega) hms
    rw [vApicesAux, mem_union, mem_image, mem_image] at hβ
    rw [show i + 1 + (d + 1) = i + 1 + 1 + d by ring, add_zero]
    rcases hβ with ⟨γ, hγ, rfl⟩ | ⟨γ, hγ, rfl⟩
    · obtain ⟨h1, h2⟩ := vApicesAux_span hms d (i + 1) (by omega) γ hγ
      have := scaleR_pos s0 (i + 1)
      exact ⟨Or.inl (by omega), Or.inr (by omega)⟩
    · obtain ⟨h1, h2⟩ := vApicesAux_span hms d (i + 1) (by omega) γ hγ
      have := scaleR_pos s0 (i + 1)
      exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
  | succ d' ih =>
    intro i d hd hd' β' hβ' β hβ
    obtain ⟨d, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have hsp := strokeLen_succ (s0 := s0) (m := m) (i := i) (by omega) hms
    rw [vApicesAux, mem_union, mem_image, mem_image] at hβ hβ'
    rw [show i + 1 + (d + 1) = i + 1 + 1 + d by ring, show i + 1 + (d' + 1) = i + 1 + 1 + d' by ring]
    rcases hβ' with ⟨γ', hγ', rfl⟩ | ⟨γ', hγ', rfl⟩ <;> rcases hβ with ⟨γ, hγ, rfl⟩ | ⟨γ, hγ, rfl⟩
    · obtain ⟨a, b⟩ := ih (i + 1) d (by omega) (by omega) γ' hγ' γ hγ
      constructor <;> omega
    · obtain ⟨h1', h2'⟩ := vApicesAux_span hms d' (i + 1) (by omega) γ' hγ'
      obtain ⟨h1, h2⟩ := vApicesAux_span hms d (i + 1) (by omega) γ hγ
      have := strokeLen_pos s0 m (i + 1 + 1 + d')
      exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
    · obtain ⟨h1', h2'⟩ := vApicesAux_span hms d' (i + 1) (by omega) γ' hγ'
      obtain ⟨h1, h2⟩ := vApicesAux_span hms d (i + 1) (by omega) γ hγ
      exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    · obtain ⟨a, b⟩ := ih (i + 1) d (by omega) (by omega) γ' hγ' γ hγ
      constructor <;> omega

/-- **Turns in the span of a V have at least its level** (the span `[α, α + 2Π_k)` of a level-`k`
V contains only turns of levels `≥ k`). -/
theorem isTurnOfLevel_ge_of_span {s0 m k : ℕ} (hms : m ≤ s0) (hk1 : 1 ≤ k) (hkm : k ≤ m)
    {α : ℕ} (hα : α ∈ periodVApices s0 m k) (n : ℤ) {τ : ℤ} {l : ℕ}
    (h1 : (α : ℤ) + n * dnpPeriod s0 m ≤ τ)
    (h2 : τ < (α : ℤ) + n * dnpPeriod s0 m + 2 * strokeLen s0 m k)
    (hτ : IsTurnOfLevel s0 m τ l) : k ≤ l := by
  have hspan := periodVApices_span_subset hk1 hkm hms hα
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, τ = (t : ℤ) + n * dnpPeriod s0 m :=
    ⟨(τ - n * dnpPeriod s0 m).toNat, by omega⟩
  rw [isTurnOfLevel_add_mul_period] at hτ
  have ht1 : α ≤ t := by omega
  have ht2 : t < α + 2 * strokeLen s0 m k := by omega
  unfold IsTurnOfLevel at hτ
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (show t < dnpPeriod s0 m by omega)),
    Int.toNat_natCast] at hτ
  rw [periodVApices, mem_biUnion] at hα
  obtain ⟨q, hq, hα⟩ := hα; rw [mem_range] at hq
  obtain ⟨β, hβ, rfl⟩ := mem_image.mp hα
  obtain ⟨hβ1, hβ2⟩ := vApicesAux_span hms (k - 1) 0 (by omega) β hβ
  rw [show 0 + 1 + (k - 1) = k by omega] at hβ2
  have hR0 := scaleR_pos s0 0
  rcases hτ with hτ | ⟨rfl, hτ⟩
  · obtain ⟨l', hl', hτ⟩ := mem_biUnion.mp hτ
    obtain ⟨τ', hτ', heq⟩ := mem_image.mp hτ
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [mem_Icc] at hl'
    by_contra hlt; push Not at hlt
    rcases mem_union.mp hτ' with hτ' | hτ'
    · rw [periodVApices, mem_biUnion] at hτ'
      obtain ⟨q', hq', hτ'⟩ := hτ'; rw [mem_range] at hq'
      obtain ⟨β', hβ', hβ'e⟩ := mem_image.mp hτ'
      obtain ⟨h1', h2'⟩ := vApicesAux_span hms (l' - 1) 0 (by omega) β' hβ'
      obtain ⟨a, b⟩ := vApicesAux_nest hms (l' - 1) 0 (k - 1) (by omega) (by omega) β' hβ' β hβ
      rw [show 0 + 1 + (k - 1) = k by omega] at a b
      rw [show 0 + 1 + (l' - 1) = l' by omega] at b h2'
      have := strokeLen_pos s0 m l'
      interval_cases q <;> interval_cases q' <;> omega
    · obtain ⟨α', hα', hα'e⟩ := mem_image.mp hτ'
      rw [periodVApices, mem_biUnion] at hα'
      obtain ⟨q', hq', hα'⟩ := hα'; rw [mem_range] at hq'
      obtain ⟨β', hβ', rfl⟩ := mem_image.mp hα'
      obtain ⟨h1', h2'⟩ := vApicesAux_span hms (l' - 1) 0 (by omega) β' hβ'
      obtain ⟨a, b⟩ := vApicesAux_nest hms (l' - 1) 0 (k - 1) (by omega) (by omega) β' hβ' β hβ
      rw [show 0 + 1 + (k - 1) = k by omega] at a b
      rw [show 0 + 1 + (l' - 1) = l' by omega] at b h2'
      have := strokeLen_pos s0 m l'
      interval_cases q <;> interval_cases q' <;> omega
  · exfalso; rcases hτ with hτ | hτ <;> interval_cases q <;> omega

/-! ### The V's of `U` -/

/-- Inside a level-`i` stroke, the parent stroke (of level `i + d`) of the V with apex
`β ∈ vApicesAux s0 m i d` starts at `β - R_{i+d}`, at some cell and in some direction. -/
theorem strokePos_parent {s0 m : ℕ} (hms : m ≤ s0) : ∀ d i, i + 1 + d ≤ m →
    ∀ β ∈ vApicesAux s0 m i d, scaleR s0 (i + d) ≤ β ∧ ∃ c σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      ∀ o ≤ strokeLen s0 m (i + d),
        strokePos s0 m i (β - scaleR s0 (i + d) + o) = c + σ * strokePos s0 m (i + d) o := by
  intro d
  induction d with
  | zero =>
    intro i _ β hβ
    rw [vApicesAux, mem_singleton] at hβ; subst hβ
    refine ⟨le_refl _, 0, 1, Or.inl rfl, fun o _ => ?_⟩
    simp
  | succ d ih =>
    intro i hi β hβ
    have hsp := strokeLen_succ (s0 := s0) (m := m) (i := i) (by omega) hms
    have hsp2 := strokeLen_succ (s0 := s0) (m := m) (i := i + 1 + d) (by omega) hms
    have hRle : scaleR s0 (i + 1 + d) ≤ scaleR s0 (i + 1) := by
      unfold scaleR; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [show i + (d + 1) = i + 1 + d by ring]
    rw [vApicesAux, mem_union, mem_image, mem_image] at hβ
    rcases hβ with ⟨β', hβ', rfl⟩ | ⟨β', hβ', rfl⟩
    · obtain ⟨hR', c', σ', hσ', hC'⟩ := ih (i + 1) (by omega) β' hβ'
      obtain ⟨h1, h2⟩ := vApicesAux_span hms d (i + 1) (by omega) β' hβ'
      rw [show i + 1 + 1 + d = i + 1 + d + 1 by ring] at h2
      refine ⟨by omega, scaleR s0 i - c', -σ', by rcases hσ' with h | h <;> simp [h], fun o ho => ?_⟩
      rw [show scaleR s0 i + β' - scaleR s0 (i + 1 + d) + o =
          scaleR s0 i + (β' - scaleR s0 (i + 1 + d) + o) by omega,
        strokePos_back (by omega) hms (by omega), hC' o ho]
      ring
    · obtain ⟨hR', c', σ', hσ', hC'⟩ := ih (i + 1) (by omega) β' hβ'
      refine ⟨by omega, scaleR s0 (i + 1) + c', σ', hσ', fun o ho => ?_⟩
      rw [show scaleR s0 i + strokeLen s0 m (i + 1) + β' - scaleR s0 (i + 1 + d) + o =
          scaleR s0 i + strokeLen s0 m (i + 1) + (β' - scaleR s0 (i + 1 + d) + o) by omega,
        strokePos_fwd (by omega), hC' o ho]
      ring

/-- The parent stroke (of level `k - 1`) of a level-`k` V of a period starts at `α - R_{k-1}`. -/
theorem dnpWalk_parent {s0 m k : ℕ} (hms : m ≤ s0) (hk1 : 1 ≤ k) (hkm : k ≤ m) {α : ℕ}
    (hα : α ∈ periodVApices s0 m k) :
    scaleR s0 (k - 1) ≤ α ∧ ∃ c σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ o ≤ strokeLen s0 m (k - 1),
      dnpWalk s0 m ((α - scaleR s0 (k - 1) + o : ℕ) : ℤ) = c + σ * strokePos s0 m (k - 1) o := by
  rw [periodVApices, mem_biUnion] at hα
  obtain ⟨q, hq, hα⟩ := hα; rw [mem_range] at hq
  obtain ⟨β, hβ, rfl⟩ := mem_image.mp hα
  obtain ⟨hR, c, σ, hσ, hC⟩ := strokePos_parent hms (k - 1) 0 (by omega) β hβ
  rw [show 0 + (k - 1) = k - 1 by ring] at hR hC
  obtain ⟨h1, h2⟩ := vApicesAux_span hms (k - 1) 0 (by omega) β hβ
  rw [show 0 + 1 + (k - 1) = k by omega] at h2
  have hsp := strokeLen_succ (s0 := s0) (m := m) (i := k - 1) (by omega) hms
  rw [show k - 1 + 1 = k by omega] at hsp
  refine ⟨by nlinarith, zeroStart s0 q + zeroSign q * c, zeroSign q * σ, ?_, fun o ho => ?_⟩
  · rcases zeroSign_pm q with h | h <;> rcases hσ with h' | h' <;> simp [h, h']
  · rw [show q * strokeLen s0 m 0 + β - scaleR s0 (k - 1) + o =
        q * strokeLen s0 m 0 + (β - scaleR s0 (k - 1) + o) by omega,
      dnpWalk_stroke hms hq (by omega), hC o ho]
    ring

/-- **The V's of `U`**: around the apex `α` of a level-`k` V of a period, with base `b = U(α)` and
direction `σ`, the walk comes in along a segment of `R_{k-1}` steps of direction `σ`, then makes a back
stroke of level `k` and direction `-σ`, then a forward stroke of level `k` and direction `σ`. -/
theorem dnpWalk_V {s0 m k : ℕ} (hms : m ≤ s0) (hk1 : 1 ≤ k) (hkm : k ≤ m) {α : ℕ}
    (hα : α ∈ periodVApices s0 m k) :
    ∃ b σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      (∀ o ≤ scaleR s0 (k - 1), dnpWalk s0 m ((α : ℤ) - o) = b - σ * o) ∧
      (∀ o ≤ strokeLen s0 m k, dnpWalk s0 m ((α : ℤ) + o) = b - σ * strokePos s0 m k o) ∧
      (∀ o ≤ strokeLen s0 m k, dnpWalk s0 m ((α : ℤ) + strokeLen s0 m k + o) =
        b - σ * scaleR s0 k + σ * strokePos s0 m k o) := by
  obtain ⟨hRα, c, σ, hσ, hC⟩ := dnpWalk_parent hms hk1 hkm hα
  have hsp := strokeLen_succ (s0 := s0) (m := m) (i := k - 1) (by omega) hms
  rw [show k - 1 + 1 = k by omega] at hsp
  have hR := scaleR_succ (s0 := s0) (i := k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at hR
  refine ⟨c + σ * scaleR s0 (k - 1), σ, hσ, fun o ho => ?_, fun o ho => ?_, fun o ho => ?_⟩
  · rw [show (α : ℤ) - o = ((α - scaleR s0 (k - 1) + (scaleR s0 (k - 1) - o) : ℕ) : ℤ) by
      push_cast [Nat.cast_sub hRα, Nat.cast_sub ho]; ring, hC _ (by omega), strokePos_seg (by omega)]
    push_cast [Nat.cast_sub ho]; ring
  · have hb := strokePos_back (s0 := s0) (m := m) (i := k - 1) (o := o) (by omega) hms
      (by rw [show k - 1 + 1 = k by omega]; exact ho)
    rw [show k - 1 + 1 = k by omega] at hb
    rw [show (α : ℤ) + o = ((α - scaleR s0 (k - 1) + (scaleR s0 (k - 1) + o) : ℕ) : ℤ) by
      push_cast [Nat.cast_sub hRα]; ring, hC _ (by omega), hb]
    ring
  · have hf := strokePos_fwd (s0 := s0) (m := m) (i := k - 1) (by omega) o
    rw [show k - 1 + 1 = k by omega] at hf
    rw [show (α : ℤ) + strokeLen s0 m k + o =
        ((α - scaleR s0 (k - 1) + (scaleR s0 (k - 1) + strokeLen s0 m k + o) : ℕ) : ℤ) by
      push_cast [Nat.cast_sub hRα]; ring, hC _ (by omega), hf]
    push_cast [hR]; ring

end MergeDepth

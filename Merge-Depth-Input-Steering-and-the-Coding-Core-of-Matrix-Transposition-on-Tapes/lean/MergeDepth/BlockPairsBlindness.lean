import MergeDepth.BlockPairsWitness

/-!
# Block pairs: turn-free runs and the blindness bound (the eighth paper's Proposition 5.17)

This file proves `BlindnessBound s0 m` for `m < s₀` (`blindnessBound_holds`), the odd-shift
blindness bound used in Lemma 7.8 and Theorem BP (in the form without the level-`0` term), and
derives the unconditional forms `prob_many_nonHalfBlind_le'` (Lemma 7.8) and `theoremBP'`
(Theorem BP with Conjecture S as its only hypothesis).

* `strokeTurns s0 m i d`: the turns inside a level-`i` stroke, with their levels;
  `strokeTurns_gap`: each turn of level `l` is followed by `R_l` steps without turns, and the offset
  of a turn determines its level.
* `vApicesAux_mem_strokeTurns`, `mem_periodTurns_cases`, `periodV_mem_strokeTurns`: the turns of a
  period are the tips and the turns of the four level-`0` strokes; `period_gap`,
  `period_level_unique`: the turn-free runs and the uniqueness of levels in a period.
* `blindnessBound_holds`: a window of length `ℓ` is blind at every odd shift that puts its start in
  the first `R_l - ℓ` steps of the run after a turn of level `l`; these starts are disjoint, there
  are `2^{l+2}` turns of level `l`, and at least half of the starts minus one have the right parity.
-/

namespace MergeDepth

open Finset DirectedReciprocity

/-- The turns inside a level-`i` stroke with remaining depth `d`, as pairs (offset, level). -/
def strokeTurns (s0 m : ℕ) : ℕ → ℕ → Finset (ℕ × ℕ)
  | _, 0 => ∅
  | i, d + 1 =>
    {(scaleR s0 i, i + 1), (scaleR s0 i + strokeLen s0 m (i + 1), i + 1)} ∪
      (strokeTurns s0 m (i + 1) d).image (fun x => (scaleR s0 i + x.1, x.2)) ∪
      (strokeTurns s0 m (i + 1) d).image
        (fun x => (scaleR s0 i + strokeLen s0 m (i + 1) + x.1, x.2))

/-- Inside a stroke, every turn of level `l` is followed by `R_l` turn-free steps, and the offset of a
turn determines its level. -/
theorem strokeTurns_gap {s0 m : ℕ} (hms : m ≤ s0) : ∀ d i, i + d ≤ m → ∀ x ∈ strokeTurns s0 m i d,
    scaleR s0 i ≤ x.1 ∧ i + 1 ≤ x.2 ∧ x.2 ≤ i + d ∧ x.1 + scaleR s0 x.2 ≤ strokeLen s0 m i ∧
      ∀ y ∈ strokeTurns s0 m i d, (x.1 < y.1 → x.1 + scaleR s0 x.2 ≤ y.1) ∧
        (y.1 = x.1 → y.2 = x.2) := by
  intro d
  induction d with
  | zero => intro i _ x hx; simp [strokeTurns] at hx
  | succ d ih =>
    intro i hid x hx
    have hsp := strokeLen_succ (s0 := s0) (m := m) (i := i) (by omega) hms
    have hR1 : scaleR s0 (i + 1) ≤ strokeLen s0 m (i + 1) := by
      unfold strokeLen; nlinarith [scaleR_pos s0 (i + 1)]
    have hRi : scaleR s0 (i + 1) ≤ scaleR s0 i := by
      unfold scaleR; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have IH := ih (i + 1) (by omega)
    -- the position bounds of the four kinds of turns
    have kinds : ∀ z ∈ strokeTurns s0 m i (d + 1),
        (z = (scaleR s0 i, i + 1)) ∨ (z = (scaleR s0 i + strokeLen s0 m (i + 1), i + 1)) ∨
        (∃ z' ∈ strokeTurns s0 m (i + 1) d, z = (scaleR s0 i + z'.1, z'.2)) ∨
        (∃ z' ∈ strokeTurns s0 m (i + 1) d,
          z = (scaleR s0 i + strokeLen s0 m (i + 1) + z'.1, z'.2)) := by
      intro z hz
      simp only [strokeTurns, mem_union, mem_insert, mem_singleton, mem_image] at hz
      rcases hz with ((h | h) | ⟨z', hz', rfl⟩) | ⟨z', hz', rfl⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨z', hz', rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨z', hz', rfl⟩))
    have hpos : ∀ z ∈ strokeTurns s0 m i (d + 1),
        (z.1 = scaleR s0 i ∧ z.2 = i + 1) ∨
        (z.1 = scaleR s0 i + strokeLen s0 m (i + 1) ∧ z.2 = i + 1) ∨
        (scaleR s0 i + scaleR s0 (i + 1) ≤ z.1 ∧ z.1 + scaleR s0 z.2 ≤ scaleR s0 i +
          strokeLen s0 m (i + 1) ∧ i + 2 ≤ z.2 ∧ z.2 ≤ i + 1 + d) ∨
        (scaleR s0 i + strokeLen s0 m (i + 1) + scaleR s0 (i + 1) ≤ z.1 ∧
          z.1 + scaleR s0 z.2 ≤ strokeLen s0 m i ∧ i + 2 ≤ z.2 ∧ z.2 ≤ i + 1 + d) := by
      intro z hz
      rcases kinds z hz with h | h | ⟨z', hz', rfl⟩ | ⟨z', hz', rfl⟩
      · subst h; exact Or.inl ⟨rfl, rfl⟩
      · subst h; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · obtain ⟨h1, h2, h3, h4, -⟩ := IH z' hz'
        exact Or.inr (Or.inr (Or.inl ⟨by simp only; omega, by simp only; omega, by simp only; omega,
          by simp only; omega⟩))
      · obtain ⟨h1, h2, h3, h4, -⟩ := IH z' hz'
        exact Or.inr (Or.inr (Or.inr ⟨by simp only; omega, by simp only; omega, by simp only; omega,
          by simp only; omega⟩))
    refine ⟨?_, ?_, ?_, ?_, fun y hy => ?_⟩
    · rcases hpos x hx with h | h | h | h <;> omega
    · rcases hpos x hx with h | h | h | h <;> omega
    · rcases hpos x hx with h | h | h | h <;> omega
    · rcases hpos x hx with h | h | h | h
      · rw [h.1, h.2]; omega
      · rw [h.1, h.2]; omega
      · omega
      · omega
    -- the gap and the uniqueness of levels
    have hp1 := scaleR_pos s0 (i + 1)
    have kinds' : ∀ z ∈ strokeTurns s0 m i (d + 1),
        (z.1 = scaleR s0 i ∧ z.2 = i + 1) ∨ (z.1 = scaleR s0 i + strokeLen s0 m (i + 1) ∧ z.2 = i + 1) ∨
        (∃ z' ∈ strokeTurns s0 m (i + 1) d, z.1 = scaleR s0 i + z'.1 ∧ z.2 = z'.2) ∨
        (∃ z' ∈ strokeTurns s0 m (i + 1) d,
          z.1 = scaleR s0 i + strokeLen s0 m (i + 1) + z'.1 ∧ z.2 = z'.2) := by
      intro z hz
      rcases kinds z hz with h | h | ⟨z', hz', rfl⟩ | ⟨z', hz', rfl⟩
      · subst h; exact Or.inl ⟨rfl, rfl⟩
      · subst h; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨z', hz', rfl, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨z', hz', rfl, rfl⟩))
    rcases kinds' x hx with ⟨xa, xb⟩ | ⟨xa, xb⟩ | ⟨x', hx', xa, xb⟩ | ⟨x', hx', xa, xb⟩ <;>
      rcases kinds' y hy with ⟨ya, yb⟩ | ⟨ya, yb⟩ | ⟨y', hy', ya, yb⟩ | ⟨y', hy', ya, yb⟩
    · rw [xa, xb, ya, yb]; omega
    · rw [xa, xb, ya, yb]; omega
    · obtain ⟨k1, k2, k3, k4, -⟩ := IH y' hy'; have := scaleR_pos s0 y'.2; rw [xa, xb, ya, yb]; omega
    · obtain ⟨k1, k2, k3, k4, -⟩ := IH y' hy'; have := scaleR_pos s0 y'.2; rw [xa, xb, ya, yb]; omega
    · rw [xa, xb, ya, yb]; omega
    · rw [xa, xb, ya, yb]; omega
    · obtain ⟨k1, k2, k3, k4, -⟩ := IH y' hy'; have := scaleR_pos s0 y'.2; rw [xa, xb, ya, yb]; omega
    · obtain ⟨k1, k2, k3, k4, -⟩ := IH y' hy'; have := scaleR_pos s0 y'.2; rw [xa, xb, ya, yb]; omega
    · obtain ⟨h1, h2, h3, h4, hxy⟩ := IH x' hx'; have := scaleR_pos s0 x'.2; rw [xa, xb, ya, yb]; omega
    · obtain ⟨h1, h2, h3, h4, hxy⟩ := IH x' hx'; have := scaleR_pos s0 x'.2; rw [xa, xb, ya, yb]; omega
    · obtain ⟨h1, h2, h3, h4, hxy⟩ := IH x' hx'; have := scaleR_pos s0 x'.2; obtain ⟨k1, k2, k3, k4, -⟩ := IH y' hy'; have := scaleR_pos s0 y'.2; obtain ⟨g1, g2⟩ := hxy y' hy'; rw [xa, xb, ya, yb]; omega
    · obtain ⟨h1, h2, h3, h4, hxy⟩ := IH x' hx'; have := scaleR_pos s0 x'.2; obtain ⟨k1, k2, k3, k4, -⟩ := IH y' hy'; have := scaleR_pos s0 y'.2; rw [xa, xb, ya, yb]; omega
    · obtain ⟨h1, h2, h3, h4, hxy⟩ := IH x' hx'; have := scaleR_pos s0 x'.2; rw [xa, xb, ya, yb]; omega
    · obtain ⟨h1, h2, h3, h4, hxy⟩ := IH x' hx'; have := scaleR_pos s0 x'.2; rw [xa, xb, ya, yb]; omega
    · obtain ⟨h1, h2, h3, h4, hxy⟩ := IH x' hx'; have := scaleR_pos s0 x'.2; obtain ⟨k1, k2, k3, k4, -⟩ := IH y' hy'; have := scaleR_pos s0 y'.2; rw [xa, xb, ya, yb]; omega
    · obtain ⟨h1, h2, h3, h4, hxy⟩ := IH x' hx'; have := scaleR_pos s0 x'.2; obtain ⟨k1, k2, k3, k4, -⟩ := IH y' hy'; have := scaleR_pos s0 y'.2; obtain ⟨g1, g2⟩ := hxy y' hy'; rw [xa, xb, ya, yb]; omega

/-- The apices and valleys of the inner V's are turns of the stroke, with their levels. -/
theorem vApicesAux_mem_strokeTurns {s0 m : ℕ} : ∀ d' d i, d' < d → ∀ β ∈ vApicesAux s0 m i d',
    (β, i + 1 + d') ∈ strokeTurns s0 m i d ∧
      (β + strokeLen s0 m (i + 1 + d'), i + 1 + d') ∈ strokeTurns s0 m i d := by
  intro d'
  induction d' with
  | zero =>
    intro d i hd β hβ
    rw [vApicesAux, mem_singleton] at hβ; subst hβ
    obtain ⟨d'', rfl⟩ : ∃ d'', d = d'' + 1 := ⟨d - 1, by omega⟩
    simp [strokeTurns]
  | succ d' ih =>
    intro d i hd β hβ
    obtain ⟨d'', rfl⟩ : ∃ d'', d = d'' + 1 := ⟨d - 1, by omega⟩
    rw [vApicesAux, mem_union, mem_image, mem_image] at hβ
    have hidx : i + 1 + (d' + 1) = i + 1 + 1 + d' := by omega
    rcases hβ with ⟨β', hβ', rfl⟩ | ⟨β', hβ', rfl⟩
    · obtain ⟨h1, h2⟩ := ih d'' (i + 1) (by omega) β' hβ'
      simp only [strokeTurns, mem_union, mem_image]
      refine ⟨Or.inl (Or.inr ⟨_, h1, by rw [hidx]⟩), Or.inl (Or.inr ⟨_, h2, ?_⟩)⟩
      rw [hidx]; simp only [Prod.mk.injEq, and_true]; ring
    · obtain ⟨h1, h2⟩ := ih d'' (i + 1) (by omega) β' hβ'
      simp only [strokeTurns, mem_union, mem_image]
      refine ⟨Or.inr ⟨_, h1, by rw [hidx]⟩, Or.inr ⟨_, h2, ?_⟩⟩
      rw [hidx]; simp only [Prod.mk.injEq, and_true]; ring

/-- Every turn of a period is a tip or a turn of one of the four level-`0` strokes. -/
theorem mem_periodTurns_cases {s0 m r : ℕ} (hr : r ∈ periodTurns s0 m) :
    r = strokeLen s0 m 0 ∨ r = 3 * strokeLen s0 m 0 ∨
      ∃ q < 4, ∃ x ∈ strokeTurns s0 m 0 m, r = q * strokeLen s0 m 0 + x.1 := by
  unfold periodTurns at hr
  rw [mem_union, mem_insert, mem_singleton] at hr
  rcases hr with hr | hr | hr
  · obtain ⟨l, hl, hr⟩ := mem_biUnion.mp hr
    rw [mem_Icc] at hl
    right; right
    rcases mem_union.mp hr with hr | hr
    · obtain ⟨q, hq, hr⟩ := mem_biUnion.mp hr
      obtain ⟨β, hβ, rfl⟩ := mem_image.mp hr
      exact ⟨q, mem_range.mp hq, _, (vApicesAux_mem_strokeTurns (l - 1) m 0 (by omega) β hβ).1, rfl⟩
    · obtain ⟨α, hα, rfl⟩ := mem_image.mp hr
      obtain ⟨q, hq, hα⟩ := mem_biUnion.mp hα
      obtain ⟨β, hβ, rfl⟩ := mem_image.mp hα
      have := (vApicesAux_mem_strokeTurns (l - 1) m 0 (by omega) β hβ).2
      rw [show 0 + 1 + (l - 1) = l by omega] at this
      exact ⟨q, mem_range.mp hq, _, this, by simp only; ring⟩
  · exact Or.inl hr
  · exact Or.inr (Or.inl hr)

/-- The apices and valleys of a period are turns of the level-`0` strokes, with their levels. -/
theorem periodV_mem_strokeTurns {s0 m l α : ℕ} (hl1 : 1 ≤ l) (hlm : l ≤ m)
    (hα : α ∈ periodVApices s0 m l) :
    (∃ q < 4, ∃ x ∈ strokeTurns s0 m 0 m, α = q * strokeLen s0 m 0 + x.1 ∧ x.2 = l) ∧
    (∃ q < 4, ∃ x ∈ strokeTurns s0 m 0 m, α + strokeLen s0 m l = q * strokeLen s0 m 0 + x.1 ∧
      x.2 = l) := by
  obtain ⟨q, hq, hα⟩ := mem_biUnion.mp hα
  obtain ⟨β, hβ, rfl⟩ := mem_image.mp hα
  obtain ⟨h1, h2⟩ := vApicesAux_mem_strokeTurns (l - 1) m 0 (by omega) β hβ
  rw [show 0 + 1 + (l - 1) = l by omega] at h1 h2
  exact ⟨⟨q, mem_range.mp hq, _, h1, rfl, rfl⟩, ⟨q, mem_range.mp hq, _, h2, by simp only; ring, rfl⟩⟩

/-- **The turn-free runs**: a turn of level `l` at time `τ = q Π₀ + x` is followed by `R_l` steps
without turns, inside the period. -/
theorem period_gap {s0 m : ℕ} (hms : m ≤ s0) {q : ℕ} (hq : q < 4) {x : ℕ × ℕ}
    (hx : x ∈ strokeTurns s0 m 0 m) :
    q * strokeLen s0 m 0 + x.1 + scaleR s0 x.2 ≤ dnpPeriod s0 m ∧
      ∀ r ∈ periodTurns s0 m, q * strokeLen s0 m 0 + x.1 < r →
        q * strokeLen s0 m 0 + x.1 + scaleR s0 x.2 ≤ r := by
  obtain ⟨h1, h2, h3, h4, hgap⟩ := strokeTurns_gap hms m 0 (by omega) x hx
  have hR0 := scaleR_pos s0 0
  unfold dnpPeriod
  refine ⟨by interval_cases q <;> omega, fun r hr hlt => ?_⟩
  rcases mem_periodTurns_cases hr with rfl | rfl | ⟨q', hq', y, hy, rfl⟩
  · interval_cases q <;> omega
  · interval_cases q <;> omega
  · obtain ⟨k1, -, -, k4, -⟩ := strokeTurns_gap hms m 0 (by omega) y hy
    have g := (hgap y hy).1
    interval_cases q <;> interval_cases q' <;> omega

/-- The time of a turn determines its level. -/
theorem period_level_unique {s0 m : ℕ} (hms : m ≤ s0) {q q' : ℕ} (hq : q < 4) (hq' : q' < 4)
    {x y : ℕ × ℕ} (hx : x ∈ strokeTurns s0 m 0 m) (hy : y ∈ strokeTurns s0 m 0 m)
    (h : q * strokeLen s0 m 0 + x.1 = q' * strokeLen s0 m 0 + y.1) : y.2 = x.2 := by
  obtain ⟨h1, -, -, h4, hgap⟩ := strokeTurns_gap hms m 0 (by omega) x hx
  obtain ⟨k1, -, -, k4, -⟩ := strokeTurns_gap hms m 0 (by omega) y hy
  have hRx := scaleR_pos s0 x.2
  have hRy := scaleR_pos s0 y.2
  have hxy : x.1 = y.1 := by interval_cases q <;> interval_cases q' <;> omega
  exact (hgap y hy).2 hxy.symm

/-- At least `(n - 1)/2` of `n` consecutive naturals have a given parity. -/
theorem card_parity_ge (a n p : ℕ) (hp : p < 2) :
    n ≤ 2 * ((Ico a (a + n)).filter fun x => x % 2 = p).card + 1 := by
  set δ := (p + 2 - a % 2) % 2
  have hδ : (a + δ) % 2 = p := by omega
  have := Finset.card_le_card_of_injOn (fun j => a + 2 * j + δ) (s := range (n / 2))
    (t := (Ico a (a + n)).filter fun x => x % 2 = p) (fun j hj => by
      rw [Finset.coe_range, Set.mem_Iio] at hj
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_Ico]
      refine ⟨⟨by omega, by omega⟩, by omega⟩) (fun i _ j _ hij => by simp only at hij; omega)
  rw [card_range] at this
  omega

/-- The apices and valleys of all levels `1, …, m` in one period, with their levels. -/
def periodTurnsLevels (s0 m : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 m).biUnion fun l => ((periodVApices s0 m l) ∪
    (periodVApices s0 m l).image (· + strokeLen s0 m l)).image fun τ => (τ, l)

theorem card_apex_valley {s0 m l : ℕ} (hl1 : 1 ≤ l) (hlm : l ≤ m) (hms : m ≤ s0) :
    ((periodVApices s0 m l) ∪ (periodVApices s0 m l).image (· + strokeLen s0 m l)).card =
      2 ^ (l + 2) := by
  have hpos := strokeLen_pos s0 m l
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun a b h => by
    omega), card_periodVApices hl1 hlm hms]
  · rw [pow_succ]; ring
  · rw [Finset.disjoint_left]
    intro α hα hα'
    obtain ⟨α', hα'', rfl⟩ := mem_image.mp hα'
    by_cases he : α' + strokeLen s0 m l = α'
    · omega
    · rcases periodVApices_spans_disjoint hl1 hlm hms hα hα'' he with h | h <;> omega


theorem mem_periodTurnsLevels {s0 m : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ periodTurnsLevels s0 m) :
    1 ≤ x.2 ∧ x.2 ≤ m ∧ x.1 ∈ periodTurns s0 m ∧
      ∃ q < 4, ∃ y ∈ strokeTurns s0 m 0 m, x.1 = q * strokeLen s0 m 0 + y.1 ∧ y.2 = x.2 := by
  obtain ⟨l, hl, hx⟩ := mem_biUnion.mp hx
  obtain ⟨τ, hτ, rfl⟩ := mem_image.mp hx
  rw [mem_Icc] at hl
  refine ⟨hl.1, hl.2, ?_, ?_⟩
  · unfold periodTurns
    exact mem_union_left _ (mem_biUnion.mpr ⟨l, mem_Icc.mpr hl, hτ⟩)
  · rcases mem_union.mp hτ with hτ | hτ
    · exact (periodV_mem_strokeTurns hl.1 hl.2 hτ).1
    · obtain ⟨α, hα, rfl⟩ := mem_image.mp hτ
      exact (periodV_mem_strokeTurns hl.1 hl.2 hα).2

theorem sum_two_pow_le (m : ℕ) : ∑ l ∈ Icc 1 m, (2 : ℝ) ^ l ≤ 2 ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), show (2 : ℝ) ^ (m + 1 + 1) = 2 ^ (m + 1) + 2 ^ (m + 1)
      by ring]
    linarith

theorem scale_max_identity {s0 l L : ℕ} (hl : l ≤ s0) :
    (2 : ℝ) ^ l * ((scaleR s0 l - L : ℕ) : ℝ) = 2 ^ s0 * max 0 (1 - (L : ℝ) / scaleR s0 l) := by
  have hR : (0 : ℝ) < scaleR s0 l := by exact_mod_cast scaleR_pos s0 l
  have h2 : (2 : ℝ) ^ l * scaleR s0 l = 2 ^ s0 := by
    rw [scaleR_real hl, inv_pow]; field_simp
  rcases le_or_gt L (scaleR s0 l) with hLR | hLR
  · rw [Nat.cast_sub hLR, max_eq_right (by rw [sub_nonneg, div_le_one hR]; exact_mod_cast hLR),
      ← h2]
    field_simp
  · rw [Nat.sub_eq_zero_of_le hLR.le, max_eq_left (by
      rw [sub_nonpos, le_div_iff₀ hR, one_mul]; exact_mod_cast hLR.le)]
    simp

/-- **The blindness bound** (the eighth paper's Proposition 5.17 without its level-`0` term):
proved from the turn-free runs `period_gap` by counting the window starts that fit into them. -/
theorem blindnessBound_holds {s0 m : ℕ} (hms : m < s0) : BlindnessBound s0 m := by
  intro h p u hpu
  set P := dnpPeriod s0 m with hPdef
  have hPpos := dnpPeriod_pos s0 m
  have hPeven := dnpPeriod_even s0 m
  set L : ℕ := (u - p).toNat with hLdef
  have hLp : (L : ℤ) = u - p := Int.toNat_of_nonneg (by omega)
  set par : ℕ := ((p + 1) % 2).toNat with hpar
  have hpar2 : par < 2 := by omega
  set S : ℕ × ℕ → Finset ℕ := fun x =>
    (Ico x.1 (x.1 + (scaleR s0 x.2 - L))).filter fun a => a % 2 = par with hSdef
  set T := periodTurnsLevels s0 m
  set G := T.biUnion S with hGdef
  have hgap : ∀ x ∈ T, x.1 + scaleR s0 x.2 ≤ P ∧
      ∀ r ∈ periodTurns s0 m, x.1 < r → x.1 + scaleR s0 x.2 ≤ r := by
    intro x hx
    obtain ⟨-, -, -, q, hq, y, hy, hxy, hl⟩ := mem_periodTurnsLevels hx
    obtain ⟨g1, g2⟩ := period_gap hms.le hq hy
    rw [hl] at g1 g2
    refine ⟨by rw [hxy]; exact g1, fun r hr hlt => by rw [hxy]; exact g2 r hr (by rw [← hxy]; exact hlt)⟩
  have huniq : ∀ x ∈ T, ∀ x' ∈ T, x.1 = x'.1 → x.2 = x'.2 := by
    intro x hx x' hx' he
    obtain ⟨-, -, -, q, hq, y, hy, hxy, hl⟩ := mem_periodTurnsLevels hx
    obtain ⟨-, -, -, q', hq', y', hy', hxy', hl'⟩ := mem_periodTurnsLevels hx'
    rw [← hl, ← hl']
    exact period_level_unique hms.le hq' hq hy' hy (by rw [← hxy', ← hxy, he])
  -- the shift sending the window start to `a`
  set g : ℕ → ℕ := fun a => ((if h then (a : ℤ) - p else p - (a : ℤ)) % (P : ℤ)).toNat with hgdef
  have hPZ : (0 : ℤ) < P := by exact_mod_cast hPpos
  have hdiv : ∀ z : ℤ, z % (P : ℤ) - z = -((P : ℤ) * (z / P)) := fun z => by
    linarith [Int.emod_add_mul_ediv z (P : ℤ)]
  have hga : ∀ a : ℕ, (g a : ℤ) = (if h then (a : ℤ) - p else p - (a : ℤ)) % P := fun a =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hPZ.ne')
  -- the window of the shift `g a` starts at `a`
  have hwin : ∀ a : ℕ, ∀ t : ℤ, (t + (if h then (g a : ℤ) else -(g a : ℤ))) % P =
      (t - p + a) % P := by
    intro a t
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    have hg1 := hga a
    cases h
    · simp only [Bool.false_eq_true, ↓reduceIte] at hg1 ⊢
      refine ⟨(p - a) / P, ?_⟩
      have := hdiv (p - (a : ℤ)); rw [hg1]; linarith
    · simp only [↓reduceIte] at hg1 ⊢
      refine ⟨-(((a : ℤ) - p) / P), ?_⟩
      have := hdiv ((a : ℤ) - p); rw [hg1]; linarith
  have hmemS : ∀ x ∈ T, ∀ a ∈ S x, x.1 ≤ a ∧ a + L < x.1 + scaleR s0 x.2 ∧ a % 2 = par := by
    intro x _ a ha
    simp only [hSdef, Finset.mem_filter, mem_Ico] at ha
    omega
  -- `g` maps the good starts injectively to blind odd shifts
  have hgood : ∀ a ∈ G, g a ∈ (oddRange P).filter fun ξ : ℕ => BlindHop s0 m (ξ : ℤ) h p u := by
    intro a ha
    obtain ⟨x, hx, haS⟩ := mem_biUnion.mp ha
    obtain ⟨h1, h2, h3⟩ := hmemS x hx a haS
    obtain ⟨hxP, hxgap⟩ := hgap x hx
    have hg1 := hga a
    have hlt : (g a : ℤ) < P := by rw [hg1]; exact Int.emod_lt_of_pos _ hPZ
    have hP2 : (2 : ℤ) ∣ (P : ℤ) := by exact_mod_cast Nat.dvd_of_mod_eq_zero hPeven
    have hpar' : ((g a : ℤ)) % 2 = 1 := by
      rw [hg1, Int.emod_emod_of_dvd _ hP2]
      have : (a : ℤ) % 2 = ((p + 1) % 2) := by
        have : ((a % 2 : ℕ) : ℤ) = (par : ℤ) := by rw [h3]
        push_cast at this; rw [this, hpar, Int.toNat_of_nonneg (by omega)]
      cases h <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · simp only [oddRange, Finset.mem_filter, mem_range]
      constructor <;> omega
    · unfold BlindHop TurnFree
      intro t ht
      rw [Finset.mem_Ioc] at ht
      have hcast : (if h then ((g a : ℕ) : ℤ) else -((g a : ℕ) : ℤ)) =
          (if h then (g a : ℤ) else -(g a : ℤ)) := rfl
      rw [hwin a t, Int.emod_eq_of_lt (by omega) (by omega)]
      intro hr
      have := hxgap _ hr (by omega)
      omega
  have hinj : Set.InjOn g G := by
    intro a ha a' ha' he
    obtain ⟨x, hx, haS⟩ := mem_biUnion.mp ha
    obtain ⟨x', hx', haS'⟩ := mem_biUnion.mp ha'
    have hxP := (hgap x hx).1
    have hxP' := (hgap x' hx').1
    obtain ⟨h1, h2, -⟩ := hmemS x hx a haS
    obtain ⟨k1, k2, -⟩ := hmemS x' hx' a' haS'
    have he' : (g a : ℤ) = (g a' : ℤ) := by rw [he]
    rw [hga, hga] at he'
    have hd := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp he'
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hd
    have haP : (a : ℤ) < P := by exact_mod_cast (by omega : a < P)
    have haP' : (a' : ℤ) < P := by exact_mod_cast (by omega : a' < P)
    have hdiff : (a : ℤ) - a' = P * k ∨ (a : ℤ) - a' = -(P * k) := by
      cases h <;> simp only [Bool.false_eq_true, ↓reduceIte] at hk
      · right; linarith
      · left; linarith
    have hk0 : k = 0 := by
      rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
      · have := mul_le_mul_of_nonneg_left (show k ≤ -1 by omega) hPZ.le
        rcases hdiff with hd | hd <;> linarith
      · exact hk0
      · have := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ k by omega) hPZ.le
        rcases hdiff with hd | hd <;> linarith
    rw [hk0, mul_zero, neg_zero] at hdiff
    rcases hdiff with hd | hd <;> omega
  have hcardG : (G.card : ℝ) ≤
      (((oddRange P).filter fun ξ : ℕ => BlindHop s0 m (ξ : ℤ) h p u).card : ℝ) := by
    exact_mod_cast Finset.card_le_card_of_injOn g hgood hinj
  -- the good starts of distinct turns are disjoint
  have hdisj : (T : Set (ℕ × ℕ)).PairwiseDisjoint S := by
    intro x hx x' hx' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨h1, h2, -⟩ := hmemS x hx a ha
    obtain ⟨k1, k2, -⟩ := hmemS x' hx' a ha'
    rcases lt_trichotomy x.1 x'.1 with hlt | heq | hlt
    · have := (hgap x hx).2 x'.1 (mem_periodTurnsLevels hx').2.2.1 hlt; omega
    · exact hne (Prod.ext heq (huniq x hx x' hx' heq))
    · have := (hgap x' hx').2 x.1 (mem_periodTurnsLevels hx).2.2.1 hlt; omega
  have hsumG : (G.card : ℝ) = ∑ x ∈ T, ((S x).card : ℝ) := by
    rw [hGdef, Finset.card_biUnion hdisj]; push_cast; rfl
  have hT : ∑ l ∈ Icc 1 m, (2 : ℝ) ^ (l + 2) * ((((scaleR s0 l - L : ℕ) : ℝ) - 1) / 2) ≤
      ∑ x ∈ T, ((S x).card : ℝ) := by
    show _ ≤ ∑ x ∈ periodTurnsLevels s0 m, ((S x).card : ℝ)
    unfold periodTurnsLevels
    rw [Finset.sum_biUnion (by
      intro l _ l' _ hll'
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨τ, -, rfl⟩ := mem_image.mp hx
      obtain ⟨τ', -, he⟩ := mem_image.mp hx'
      exact hll' (Prod.ext_iff.mp he).2.symm)]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [mem_Icc] at hl
    rw [Finset.sum_image (fun τ _ τ' _ he => (Prod.ext_iff.mp he).1)]
    calc (2 : ℝ) ^ (l + 2) * ((((scaleR s0 l - L : ℕ) : ℝ) - 1) / 2)
        = ∑ _τ ∈ (periodVApices s0 m l ∪ (periodVApices s0 m l).image (· + strokeLen s0 m l)),
            ((((scaleR s0 l - L : ℕ) : ℝ) - 1) / 2) := by
          rw [Finset.sum_const, card_apex_valley hl.1 hl.2 hms.le, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := by
          refine Finset.sum_le_sum fun τ _ => ?_
          have := card_parity_ge τ (scaleR s0 l - L) par hpar2
          have hR : ((scaleR s0 l - L : ℕ) : ℝ) ≤
              2 * (((Ico τ (τ + (scaleR s0 l - L))).filter fun x => x % 2 = par).card : ℝ) + 1 := by
            exact_mod_cast this
          simp only [hSdef]
          linarith
  -- the final comparison
  have hΩ : ((oddRange P).card : ℝ) = 2 * (2 ^ s0 * ((m : ℝ) + 1)) := by
    obtain ⟨M', hM'⟩ : ∃ M', P = 2 * M' := ⟨P / 2, by omega⟩
    have hPR := dnpPeriod_real s0 m
    rw [← hPdef, hM'] at hPR
    rw [hM', card_oddRange_two_mul]
    push_cast at hPR; linarith
  have hΛ : (0 : ℝ) < 2 ^ s0 := by positivity
  have hN : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hLR : ((u - p : ℤ) : ℝ) = (L : ℝ) := by rw [← hLp]; push_cast; rfl
  have hmax : ∀ l ∈ Icc 1 m, max 0 (1 - ((u - p : ℤ) : ℝ) / scaleR s0 l) =
      (2 : ℝ) ^ l * ((scaleR s0 l - L : ℕ) : ℝ) / 2 ^ s0 := by
    intro l hl
    rw [mem_Icc] at hl
    rw [hLR, scale_max_identity (by omega)]; field_simp
  have hRm : (2 : ℝ) / (((m : ℝ) + 1) * scaleR s0 m) = 2 ^ (m + 1) / (2 ^ s0 * ((m : ℝ) + 1)) := by
    rw [scaleR_real hms.le, inv_pow]; field_simp; ring
  rw [Finset.sum_congr rfl hmax, hRm, le_div_iff₀ (by rw [hΩ]; positivity), hΩ]
  have hgeom := sum_two_pow_le m
  have hsplit : ∑ l ∈ Icc 1 m, (2 : ℝ) ^ (l + 2) * ((((scaleR s0 l - L : ℕ) : ℝ) - 1) / 2) =
      2 * (∑ l ∈ Icc 1 m, (2 : ℝ) ^ l * ((scaleR s0 l - L : ℕ) : ℝ)) -
        2 * ∑ l ∈ Icc 1 m, (2 : ℝ) ^ l := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [pow_add]; ring
  rw [← Finset.sum_div] at *
  have key : ((m : ℝ) + 1)⁻¹ * ((∑ l ∈ Icc 1 m, (2 : ℝ) ^ l * ((scaleR s0 l - L : ℕ) : ℝ)) / 2 ^ s0) -
      2 ^ (m + 1) / (2 ^ s0 * ((m : ℝ) + 1)) ≤
      (2 * (∑ l ∈ Icc 1 m, (2 : ℝ) ^ l * ((scaleR s0 l - L : ℕ) : ℝ)) -
        2 * ∑ l ∈ Icc 1 m, (2 : ℝ) ^ l) / (2 * (2 ^ s0 * ((m : ℝ) + 1))) := by
    generalize (∑ l ∈ Icc 1 m, (2 : ℝ) ^ l * ((scaleR s0 l - L : ℕ) : ℝ)) = X at *
    generalize (∑ l ∈ Icc 1 m, (2 : ℝ) ^ l) = Y at *
    have hD : (0 : ℝ) < 2 ^ s0 * ((m : ℝ) + 1) := by positivity
    have e1 : ((m : ℝ) + 1)⁻¹ * (X / 2 ^ s0) = X / (2 ^ s0 * ((m : ℝ) + 1)) := by field_simp
    have e2 : (2 * X - 2 * Y) / (2 * (2 ^ s0 * ((m : ℝ) + 1))) = (X - Y) / (2 ^ s0 * ((m : ℝ) + 1)) := by
      field_simp
    rw [e1, e2, div_sub_div_same, div_le_div_iff_of_pos_right hD]
    linarith
  have hfin : (2 * (∑ l ∈ Icc 1 m, (2 : ℝ) ^ l * ((scaleR s0 l - L : ℕ) : ℝ)) -
        2 * ∑ l ∈ Icc 1 m, (2 : ℝ) ^ l) / (2 * (2 ^ s0 * ((m : ℝ) + 1))) * (2 * (2 ^ s0 * ((m : ℝ) + 1))) ≤
      (((oddRange P).filter fun ξ : ℕ => BlindHop s0 m (ξ : ℤ) h p u).card : ℝ) := by
    rw [div_mul_cancel₀ _ (by positivity), ← hsplit]
    linarith
  calc _ ≤ (2 * (∑ l ∈ Icc 1 m, (2 : ℝ) ^ l * ((scaleR s0 l - L : ℕ) : ℝ)) -
        2 * ∑ l ∈ Icc 1 m, (2 : ℝ) ^ l) / (2 * (2 ^ s0 * ((m : ℝ) + 1))) *
          (2 * (2 ^ s0 * ((m : ℝ) + 1))) := by
          exact mul_le_mul_of_nonneg_right key (by positivity)
    _ ≤ _ := hfin

/-- **Lemma 7.8** (probability), unconditionally: for `m < s₀`, `0 < ε ≤ 1/8` and `ε m ≥ 4`, more
than `δ |ℱ_ε|` non-half-blind triples, `δ = 1/(48 (a₀ + 1))`, occur with probability at most
`6144 (a₀ + 1) ε`. -/
theorem prob_many_nonHalfBlind_le' {s0 m : ℕ} {ε : ℝ} (hms : m < s0) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1 / 8) (hεm : 4 ≤ ε * m) (a0 : ℕ) :
    (((oddRange (dnpPeriod s0 m)).filter fun ξ : ℕ =>
        1 / (48 * ((a0 : ℝ) + 1)) * (fineZone m ε).card < (nonHalfBlind s0 m ε ξ).card).card : ℝ) /
      (oddRange (dnpPeriod s0 m)).card ≤ 6144 * ((a0 : ℝ) + 1) * ε :=
  prob_many_nonHalfBlind_le (blindnessBound_holds hms) hms hε0 hε1 hεm a0

/-- **Lemma 7.8** (expectation), unconditionally. -/
theorem sum_nonHalfBlind_le' {s0 m : ℕ} {ε : ℝ} (hms : m < s0) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 8)
    (hεm : 4 ≤ ε * m) :
    ∑ ξ ∈ oddRange (dnpPeriod s0 m), ((nonHalfBlind s0 m ε ξ).card : ℝ) ≤
      64 * ε ^ 2 * m * (oddRange (dnpPeriod s0 m)).card :=
  sum_nonHalfBlind_le (blindnessBound_holds hms) hms hε0 hε1 hεm

/-- **Theorem BP**, assuming only Conjecture S for `a = 1, …, a₀`: with `θ₀ = 2^{-(a₀+11)}` and
`c = 2^{-16}/(26 (a₀ + 1)²)`, there is `C'` such that for all `m` and `s₀ > m` some odd shift `ξ`
has the property: for all `1 ≤ a₁, a₂ ≤ a₀`, all `K₁, K₂` and every `q ≥ 3`, the block-pair label
of `(B(a₁, K₁), B(a₂, K₂))` modulo `q` doubly `θ₀`-serves (on the witness hops) at most
`(1 - c)(m + 1) + C'` levels. -/
theorem theoremBP' {a0 : ℕ} (ha0 : 1 ≤ a0) (hS : ∀ a ∈ Icc 1 a0, ConjectureS a) :
    ∃ C' : ℝ, ∀ m s0 : ℕ, m < s0 → ∃ ξ ∈ oddRange (dnpPeriod s0 m),
      ∀ a1 a2 : ℕ, 1 ≤ a1 → a1 ≤ a0 → 1 ≤ a2 → a2 ≤ a0 → ∀ K1 K2 q : ℤ, 3 ≤ q →
        ((doublyServedLevels s0 m a1 a2 K1 K2 q ξ (theta0 a0)).card : ℝ) ≤
          (1 - constBP a0) * ((m : ℝ) + 1) + C' :=
  theoremBP ha0 hS fun _ _ hms => blindnessBound_holds hms

end MergeDepth

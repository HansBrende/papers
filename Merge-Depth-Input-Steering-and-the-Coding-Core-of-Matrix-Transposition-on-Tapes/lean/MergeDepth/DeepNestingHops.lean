import MergeDepth.DeepNestingWalk
import BoundedNesting.OneWalk

/-!
# Hops, levels and classes of the deep-nesting pair (the eighth paper's Lemma 5.1)

For a walk `x : ℤ → ℤ`, a **hop** `(p, u)` is a pair of consecutive visits `p < u` of one cell
(`IsHopZ`; on natural times these are the hops `BoundedNesting.IsHop` of the eighth paper's library,
`isHop_iff_isHopZ`, and `U` restricted to `ℕ` is a `BoundedNesting.IsWalk`, `dnpWalk_isWalk`). A hop
is determined by either endpoint (`IsHopZ.eq_of_snd`, `IsHopZ.eq_of_fst`).

* `dnpPrev s0 m u`: the previous visit of `U`; `(prev(u), u)` is the hop ending at `u`
  (`isHopZ_dnpPrev`, `IsHopZ.eq_dnpPrev`); every hop of `U` is long and contains a turn
  (`IsHopZ.long`, `IsHopZ.exists_turn`).
* `HopLevelIs s0 m p u k`: the **level** of a hop, the least level of a turn of its own head strictly
  inside it; unique and at most `m` (`HopLevelIs.unique`, `exists_hopLevelIs`).
* The two heads `x₁ = U`, `x₂ = U(· + ξ)` (`headWalk`, `headShift`, `true` for head `1`), their
  turns with levels (`IsHeadTurnOfLevel`, `isTurnZ_headWalk_iff`), hop levels (`HeadHopLevelIs`)
  and the **class** `(h, k)` (`InHopClass`): the hops of head `h` of level `k`.
* **Lemma 5.1(b)**: `apexHop_spec` (the apex hops `(α - d, α + d)`, `1 ≤ d ≤ R_k`, of a level-`k` V are
  hops of level `k` whose only inner turn is the apex), `bandHop_spec` (the valley hops
  `(ν - (m - l) R_l - x, ν + x)`, `R_{l+1} < x ≤ R_l`, are hops of level `k`, through the tail lemma
  `strokePos_tail`), and `levelHops_eq_listed`: the hops of level `k ≥ 1` ending in `(0, P]` are
  exactly these `2 R_k` hops per V. **The explicit families of `BlockPairsModel` are hops of the class
  `(h, k)`** in every period (`family_spec`, `family_inHopClass`), with later endpoints in `(0, P)`
  (`family_snd_mem`).
* **Lemma 5.1(a)**: `card_periodTurns`, `card_turns_period`: `2^{m+3} - 6` turns per period.
  `hop_cells`: the apex hop of half-width `d` is at the cell `b - σd` and the valley hop ending at
  `ν + x` at the cell `v + σx` (`b = U(α)`, `v = U(ν)`), as in Definition 7.6.
* **Lemma 5.1(c)**: `levelCount_eq`, every level has exactly `4Λ` hops per period (any window), from
  `levelCount_ge` (the listed hops), `levelCount_zero_ge` (the hops around the two tips, via the
  discrete intermediate value theorem `dnpWalk_ivt` and first visits `firstVisit`) and
  `sum_levelCount` (each hop has one level, one hop ends at each time).
* The `r`-fold cover: `coverHops` (the hops of head `h`, lifted with later endpoint in `[0, rP)`; they
  represent the residues of the hops on `ℤ` exactly once, `existsUnique_coverHops`), `n_h =
  coverHopCount = 2rP` (`coverHopCount_eq`), the classes `coverClass` with `4rΛ = n_h/(2N)` hops each
  (`card_coverClass`, `card_coverClass_mul`).
-/

namespace MergeDepth

open Finset DirectedReciprocity

/-! ### Periodic sums -/

theorem periodic_add_int_mul {M : Type*} {g : ℤ → M} {P : ℤ} (hg : ∀ t, g (t + P) = g t)
    (t n : ℤ) : g (t + n * P) = g t := by
  induction n using Int.induction_on generalizing t with
  | zero => simp
  | succ n ih => rw [show t + (n + 1) * P = (t + n * P) + P by ring, hg, ih]
  | pred n ih =>
    have := hg (t + (-n - 1) * P)
    rw [show t + (-n - 1) * P + P = t + -n * P by ring, ih] at this
    exact this.symm

/-- The sum of a `P`-periodic function over any window of length `P`. -/
theorem sum_Ico_periodic {M : Type*} [AddCommMonoid M] {g : ℤ → M} {P : ℤ} (hP : 0 < P)
    (hg : ∀ t, g (t + P) = g t) (a : ℤ) :
    ∑ t ∈ Ico a (a + P), g t = ∑ t ∈ Ico 0 P, g t := by
  refine Finset.sum_nbij (fun t => t % P) (fun t _ => ?_) (fun t₁ h₁ t₂ h₂ he => ?_)
    (fun s hs => ?_) (fun t _ => ?_)
  · exact mem_Ico.mpr ⟨Int.emod_nonneg _ hP.ne', Int.emod_lt_of_pos _ hP⟩
  · simp only [coe_Ico, Set.mem_Ico] at h₁ h₂
    have hd : P ∣ t₁ - t₂ := (Int.ModEq.dvd (show t₂ ≡ t₁ [ZMOD P] from he.symm))
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
    linarith
  · simp only [coe_Ico, Set.mem_Ico] at hs
    refine ⟨a + (s - a) % P, ?_, ?_⟩
    · simp only [coe_Ico, Set.mem_Ico]
      exact ⟨by linarith [Int.emod_nonneg (s - a) hP.ne'], by linarith [Int.emod_lt_of_pos (s - a) hP]⟩
    · simp only
      rw [Int.add_emod, Int.emod_emod_of_dvd _ (dvd_refl P), ← Int.add_emod,
        show a + (s - a) = s by ring, Int.emod_eq_of_lt hs.1 hs.2]
  · have := periodic_add_int_mul hg (t % P) (t / P)
    rw [show t % P + t / P * P = t by linarith [Int.emod_add_mul_ediv t P]] at this
    exact this

/-- The sum of a `P`-periodic function over `r` periods. -/
theorem sum_Ico_mul_periodic {M : Type*} [AddCommMonoid M] {g : ℤ → M} {P : ℤ} (hP : 0 < P)
    (hg : ∀ t, g (t + P) = g t) (a : ℤ) (r : ℕ) :
    ∑ t ∈ Ico a (a + r * P), g t = r • ∑ t ∈ Ico 0 P, g t := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [← Finset.Ico_union_Ico_eq_Ico (b := a + r * P) (by nlinarith) (by push_cast; nlinarith),
      Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive _ _ _), ih,
      show a + ((r + 1 : ℕ) : ℤ) * P = (a + r * P) + P by push_cast; ring,
      sum_Ico_periodic hP hg, succ_nsmul]

/-! ### Hops on `ℤ` -/

/-- `(p, u)` is a **hop** of the walk `x : ℤ → ℤ`: two consecutive visits `p < u` of one cell. -/
def IsHopZ (x : ℤ → ℤ) (p u : ℤ) : Prop := p < u ∧ x u = x p ∧ ∀ t ∈ Ioo p u, x t ≠ x p

instance (x : ℤ → ℤ) (p u : ℤ) : Decidable (IsHopZ x p u) := by unfold IsHopZ; infer_instance

/-- A hop is determined by its later endpoint. -/
theorem IsHopZ.eq_of_snd {x : ℤ → ℤ} {p p' u : ℤ} (h : IsHopZ x p u) (h' : IsHopZ x p' u) :
    p = p' := by
  obtain ⟨hl, he, hin⟩ := h
  obtain ⟨hl', he', hin'⟩ := h'
  rcases lt_trichotomy p p' with hlt | heq | hgt
  · exact absurd (he'.symm.trans he) (hin p' (mem_Ioo.mpr ⟨hlt, hl'⟩))
  · exact heq
  · exact absurd (he.symm.trans he') (hin' p (mem_Ioo.mpr ⟨hgt, hl⟩))

/-- A hop is determined by its earlier endpoint. -/
theorem IsHopZ.eq_of_fst {x : ℤ → ℤ} {p u u' : ℤ} (h : IsHopZ x p u) (h' : IsHopZ x p u') :
    u = u' := by
  obtain ⟨hl, he, hin⟩ := h
  obtain ⟨hl', he', hin'⟩ := h'
  rcases lt_trichotomy u u' with hlt | heq | hgt
  · exact absurd he (hin' u (mem_Ioo.mpr ⟨hl, hlt⟩))
  · exact heq
  · exact absurd he' (hin u' (mem_Ioo.mpr ⟨hl', hgt⟩))

theorem isHopZ_comp_add (x : ℤ → ℤ) (c p u : ℤ) :
    IsHopZ (fun t => x (t + c)) p u ↔ IsHopZ x (p + c) (u + c) := by
  unfold IsHopZ
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by linarith, h2, fun t ht => ?_⟩
    rw [mem_Ioo] at ht
    have := h3 (t - c) (mem_Ioo.mpr ⟨by linarith, by linarith⟩)
    simpa using this
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, h2, fun t ht => h3 (t + c) (by rw [mem_Ioo] at ht ⊢; constructor <;> linarith)⟩

/-- On natural times, the hops of `x` are the hops of the eighth paper's library (`IsHop`) of its
restriction to `ℕ`, up to the long-hop and horizon conditions. -/
theorem isHop_iff_isHopZ (x : ℤ → ℤ) (T p u : ℕ) :
    BoundedNesting.IsHop (fun t : ℕ => x t) T p u ↔ p + 2 ≤ u ∧ u < T ∧ IsHopZ x p u := by
  unfold BoundedNesting.IsHop IsHopZ
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, by exact_mod_cast (by omega : p < u), h3, fun t ht => ?_⟩
    rw [mem_Ioo] at ht
    obtain ⟨t', rfl⟩ : ∃ t' : ℕ, t = t' := ⟨t.toNat, by omega⟩
    exact h4 t' (mem_Ioo.mpr ⟨by exact_mod_cast ht.1, by exact_mod_cast ht.2⟩)
  · rintro ⟨h1, h2, -, h3, h4⟩
    exact ⟨h1, h2, h3, fun t ht => h4 t (by rw [mem_Ioo] at ht ⊢; exact_mod_cast ht)⟩

/-- `U` restricted to `ℕ` is a walk in the sense of the eighth paper's library. -/
theorem dnpWalk_isWalk {s0 m : ℕ} (hms : m ≤ s0) :
    BoundedNesting.IsWalk (fun t : ℕ => dnpWalk s0 m t) := by
  intro t
  have := dnpStep_pm hms t
  unfold dnpStep at this
  push_cast
  rcases this with h | h <;> rw [h] <;> norm_num

/-! ### The hops of `U` -/

theorem isHopZ_dnpWalk_add_mul_period (s0 m : ℕ) (p u n : ℤ) :
    IsHopZ (dnpWalk s0 m) (p + n * dnpPeriod s0 m) (u + n * dnpPeriod s0 m) ↔
      IsHopZ (dnpWalk s0 m) p u := by
  have := isHopZ_comp_add (dnpWalk s0 m) (n * dnpPeriod s0 m) p u
  rw [← this]
  simp only [dnpWalk_add_mul_period]

/-- Every hop of `U` is long. -/
theorem IsHopZ.long {s0 m : ℕ} (hms : m ≤ s0) {p u : ℤ} (h : IsHopZ (dnpWalk s0 m) p u) :
    p + 2 ≤ u := by
  obtain ⟨h1, h2, -⟩ := h
  by_contra hc
  have hu : u = p + 1 := by omega
  have := dnpStep_pm hms p
  unfold dnpStep at this
  rw [← hu, h2] at this
  rcases this with h | h <;> norm_num at h

theorem dnpWalk_exists_prev (s0 m : ℕ) (u : ℤ) :
    ∃ d : ℕ, 0 < d ∧ dnpWalk s0 m (u - d) = dnpWalk s0 m u :=
  ⟨dnpPeriod s0 m, dnpPeriod_pos s0 m, by
    have := dnpWalk_add_mul_period s0 m (u - dnpPeriod s0 m) 1
    rw [show u - dnpPeriod s0 m + 1 * dnpPeriod s0 m = u by ring] at this
    exact this.symm⟩

/-- The previous visit `prev(u)` of `U` to the cell `U(u)`. -/
def dnpPrev (s0 m : ℕ) (u : ℤ) : ℤ := u - Nat.find (dnpWalk_exists_prev s0 m u)

/-- `(prev(u), u)` is the hop of `U` ending at `u`. -/
theorem isHopZ_dnpPrev (s0 m : ℕ) (u : ℤ) : IsHopZ (dnpWalk s0 m) (dnpPrev s0 m u) u := by
  have hspec := Nat.find_spec (dnpWalk_exists_prev s0 m u)
  unfold dnpPrev
  refine ⟨by have := hspec.1; omega, hspec.2.symm, fun t ht => ?_⟩
  rw [mem_Ioo] at ht
  obtain ⟨d, hd⟩ : ∃ d : ℕ, t = u - d := ⟨(u - t).toNat, by omega⟩
  have hdlt : d < Nat.find (dnpWalk_exists_prev s0 m u) := by omega
  have := Nat.find_min (dnpWalk_exists_prev s0 m u) hdlt
  rw [hd, hspec.2]
  intro he; exact this ⟨by omega, he⟩

/-- Every hop of `U` is `(prev(u), u)`. -/
theorem IsHopZ.eq_dnpPrev {s0 m : ℕ} {p u : ℤ} (h : IsHopZ (dnpWalk s0 m) p u) :
    p = dnpPrev s0 m u :=
  h.eq_of_snd (isHopZ_dnpPrev s0 m u)

theorem dnpPrev_ge (s0 m : ℕ) (u : ℤ) : u - dnpPeriod s0 m ≤ dnpPrev s0 m u := by
  unfold dnpPrev
  have := Nat.find_min' (dnpWalk_exists_prev s0 m u)
    ⟨dnpPeriod_pos s0 m, (dnpWalk_exists_prev s0 m u).choose_spec.2 |> fun _ => by
      have := dnpWalk_add_mul_period s0 m (u - dnpPeriod s0 m) 1
      rw [show u - dnpPeriod s0 m + 1 * dnpPeriod s0 m = u by ring] at this
      exact this.symm⟩
  omega

theorem dnpPrev_add_mul_period (s0 m : ℕ) (u n : ℤ) :
    dnpPrev s0 m (u + n * dnpPeriod s0 m) = dnpPrev s0 m u + n * dnpPeriod s0 m := by
  have h := (isHopZ_dnpWalk_add_mul_period s0 m (dnpPrev s0 m u) u n).2 (isHopZ_dnpPrev s0 m u)
  exact (h.eq_dnpPrev).symm

/-- Every hop of `U` contains a turn strictly inside (its owner). -/
theorem IsHopZ.exists_turn {s0 m : ℕ} (hms : m ≤ s0) {p u : ℤ} (h : IsHopZ (dnpWalk s0 m) p u) :
    ∃ τ, p < τ ∧ τ < u ∧ IsTurnZ (dnpWalk s0 m) τ := by
  by_contra hno
  push Not at hno
  obtain ⟨n, hn⟩ : ∃ n : ℕ, u = p + n := ⟨(u - p).toNat, by have := h.1; omega⟩
  have hstep : ∀ j : ℕ, j < n → dnpStep s0 m (p + j) = dnpStep s0 m p := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hnt := hno (p + (j + 1 : ℕ)) (by push_cast; omega) (by rw [hn]; push_cast; omega)
      rw [isTurnZ_dnpWalk_iff_step, not_not] at hnt
      rw [hnt, show p + ((j + 1 : ℕ) : ℤ) - 1 = p + (j : ℕ) by push_cast; ring, ih (by omega)]
  have hpos : ∀ j : ℕ, j ≤ n → dnpWalk s0 m (p + j) = dnpWalk s0 m p + j * dnpStep s0 m p := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have h1 := hstep j (by omega)
      have h2 : dnpStep s0 m (p + (j : ℕ)) =
          dnpWalk s0 m (p + (j : ℕ) + 1) - dnpWalk s0 m (p + (j : ℕ)) := rfl
      rw [show p + ((j + 1 : ℕ) : ℤ) = p + (j : ℕ) + 1 by push_cast; ring]
      push_cast
      linarith [ih (by omega)]
  have hu := hpos n le_rfl
  rw [← hn, h.2.1] at hu
  have hn0 : (0 : ℤ) < n := by have := h.1; omega
  rcases dnpStep_pm hms p with hs | hs <;> rw [hs] at hu <;> linarith

/-! ### Levels of hops -/

/-- The hop `(p, u)` of `U` has **level** `k`: the least level of a turn of `U` strictly inside it
(the eighth paper's Section 2.5). -/
def HopLevelIs (s0 m : ℕ) (p u : ℤ) (k : ℕ) : Prop :=
  (∃ τ, p < τ ∧ τ < u ∧ IsTurnOfLevel s0 m τ k) ∧
    ∀ τ l, p < τ → τ < u → IsTurnOfLevel s0 m τ l → k ≤ l

theorem HopLevelIs.unique {s0 m : ℕ} {p u : ℤ} {k k' : ℕ} (h : HopLevelIs s0 m p u k)
    (h' : HopLevelIs s0 m p u k') : k = k' := by
  obtain ⟨τ, h1, h2, h3⟩ := h.1
  obtain ⟨τ', h1', h2', h3'⟩ := h'.1
  exact le_antisymm (h.2 τ' k' h1' h2' h3') (h'.2 τ k h1 h2 h3)

theorem HopLevelIs.le_m {s0 m : ℕ} {p u : ℤ} {k : ℕ} (h : HopLevelIs s0 m p u k) : k ≤ m := by
  obtain ⟨τ, -, -, h3⟩ := h.1; exact h3.le_m

theorem exists_hopLevelIs {s0 m : ℕ} (hms : m ≤ s0) {p u : ℤ} (h : IsHopZ (dnpWalk s0 m) p u) :
    ∃ k, HopLevelIs s0 m p u k := by
  classical
  obtain ⟨τ, h1, h2, h3⟩ := h.exists_turn hms
  obtain ⟨l, hl⟩ := (isTurnZ_iff_exists_level hms τ).1 h3
  have hex : ∃ k, ∃ τ, p < τ ∧ τ < u ∧ IsTurnOfLevel s0 m τ k := ⟨l, τ, h1, h2, hl⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun τ' l' h1' h2' h3' => ?_⟩
  exact Nat.find_min' hex ⟨τ', h1', h2', h3'⟩

theorem hopLevelIs_add_mul_period (s0 m : ℕ) (p u n : ℤ) (k : ℕ) :
    HopLevelIs s0 m (p + n * dnpPeriod s0 m) (u + n * dnpPeriod s0 m) k ↔ HopLevelIs s0 m p u k := by
  unfold HopLevelIs
  constructor
  · rintro ⟨⟨τ, h1, h2, h3⟩, h4⟩
    refine ⟨⟨τ - n * dnpPeriod s0 m, by linarith, by linarith, ?_⟩, fun τ' l h1' h2' h3' => ?_⟩
    · rw [← isTurnOfLevel_add_mul_period _ n]; simpa using h3
    · exact h4 (τ' + n * dnpPeriod s0 m) l (by linarith) (by linarith)
        ((isTurnOfLevel_add_mul_period τ' n l).2 h3')
  · rintro ⟨⟨τ, h1, h2, h3⟩, h4⟩
    refine ⟨⟨τ + n * dnpPeriod s0 m, by linarith, by linarith,
      (isTurnOfLevel_add_mul_period τ n k).2 h3⟩, fun τ' l h1' h2' h3' => ?_⟩
    have := (isTurnOfLevel_add_mul_period (s0 := s0) (m := m) (τ' - n * dnpPeriod s0 m) n l).1
      (by simpa using h3')
    exact h4 _ l (by linarith) (by linarith) this

/-! ### The two heads -/

/-- The shift of head `h` (`true` for head `1`, `false` for head `2`): `x_h(t) = U(t + c_h)`, so
`x₁ = U` and `x₂ = U(· + ξ)`. -/
def headShift (ξ : ℤ) (h : Bool) : ℤ := if h then 0 else ξ

/-- The walk of head `h` of the pair `x₁ = U`, `x₂ = U(· + ξ)`. -/
def headWalk (s0 m : ℕ) (ξ : ℤ) (h : Bool) (t : ℤ) : ℤ := dnpWalk s0 m (t + headShift ξ h)

/-- `τ` is a turn of head `h` of level `l`. -/
def IsHeadTurnOfLevel (s0 m : ℕ) (ξ : ℤ) (h : Bool) (τ : ℤ) (l : ℕ) : Prop :=
  IsTurnOfLevel s0 m (τ + headShift ξ h) l

theorem isTurnZ_headWalk_iff {s0 m : ℕ} (hms : m ≤ s0) (ξ : ℤ) (h : Bool) (τ : ℤ) :
    IsTurnZ (headWalk s0 m ξ h) τ ↔ ∃ l, IsHeadTurnOfLevel s0 m ξ h τ l := by
  unfold IsHeadTurnOfLevel
  rw [← isTurnZ_iff_exists_level hms]
  unfold IsTurnZ headWalk
  rw [show τ + 1 + headShift ξ h = τ + headShift ξ h + 1 by ring,
    show τ - 1 + headShift ξ h = τ + headShift ξ h - 1 by ring]

/-- The hop `(p, u)` of head `h` has **level** `k`: the least level of a turn of its own head strictly
inside it. -/
def HeadHopLevelIs (s0 m : ℕ) (ξ : ℤ) (h : Bool) (p u : ℤ) (k : ℕ) : Prop :=
  (∃ τ, p < τ ∧ τ < u ∧ IsHeadTurnOfLevel s0 m ξ h τ k) ∧
    ∀ τ l, p < τ → τ < u → IsHeadTurnOfLevel s0 m ξ h τ l → k ≤ l

theorem headHopLevelIs_iff (s0 m : ℕ) (ξ : ℤ) (h : Bool) (p u : ℤ) (k : ℕ) :
    HeadHopLevelIs s0 m ξ h p u k ↔ HopLevelIs s0 m (p + headShift ξ h) (u + headShift ξ h) k := by
  unfold HeadHopLevelIs HopLevelIs IsHeadTurnOfLevel
  set c := headShift ξ h
  constructor
  · rintro ⟨⟨τ, h1, h2, h3⟩, h4⟩
    refine ⟨⟨τ + c, by linarith, by linarith, h3⟩, fun τ' l h1' h2' h3' => ?_⟩
    exact h4 (τ' - c) l (by linarith) (by linarith) (by simpa using h3')
  · rintro ⟨⟨τ, h1, h2, h3⟩, h4⟩
    refine ⟨⟨τ - c, by linarith, by linarith, by simpa using h3⟩, fun τ' l h1' h2' h3' => ?_⟩
    exact h4 (τ' + c) l (by linarith) (by linarith) h3'

theorem isHopZ_headWalk_iff (s0 m : ℕ) (ξ : ℤ) (h : Bool) (p u : ℤ) :
    IsHopZ (headWalk s0 m ξ h) p u ↔ IsHopZ (dnpWalk s0 m) (p + headShift ξ h) (u + headShift ξ h) :=
  isHopZ_comp_add (dnpWalk s0 m) (headShift ξ h) p u

/-- The **class** `(h, k)`: the hops of head `h` of level `k`. -/
def InHopClass (s0 m : ℕ) (ξ : ℤ) (h : Bool) (k : ℕ) (p u : ℤ) : Prop :=
  IsHopZ (headWalk s0 m ξ h) p u ∧ HeadHopLevelIs s0 m ξ h p u k

theorem inHopClass_iff (s0 m : ℕ) (ξ : ℤ) (h : Bool) (k : ℕ) (p u : ℤ) :
    InHopClass s0 m ξ h k p u ↔ IsHopZ (dnpWalk s0 m) (p + headShift ξ h) (u + headShift ξ h) ∧
      HopLevelIs s0 m (p + headShift ξ h) (u + headShift ξ h) k := by
  unfold InHopClass; rw [isHopZ_headWalk_iff, headHopLevelIs_iff]

/-! ### The hops of a V (the eighth paper's Lemma 5.1(b)) -/

/-- **The tail of a stroke**: in a level-`j` stroke, for `j ≤ l ≤ m` and `R_{l+1} < x ≤ R_l`
(`R_{m+1} = 0`), the walk is at `R_j - x` at offset `Π_j - (m - l) R_l - x`, and strictly beyond
`R_j - x` afterwards. -/
theorem strokePos_tail {s0 m : ℕ} (hms : m ≤ s0) : ∀ e j l, l = j + e → l ≤ m →
    ∀ x, scaleBelow s0 m l < x → x ≤ scaleR s0 l →
      (m - l) * scaleR s0 l + x ≤ strokeLen s0 m j ∧
      strokePos s0 m j (strokeLen s0 m j - ((m - l) * scaleR s0 l + x)) = (scaleR s0 j : ℤ) - x ∧
      ∀ o, strokeLen s0 m j - ((m - l) * scaleR s0 l + x) < o → o ≤ strokeLen s0 m j →
        (scaleR s0 j : ℤ) - x < strokePos s0 m j o := by
  intro e
  induction e with
  | zero =>
    intro j l hl hlm x hx1 hx2
    obtain rfl : l = j := by omega
    have hPi : strokeLen s0 m l = (m - l) * scaleR s0 l + scaleR s0 l := by unfold strokeLen; ring
    refine ⟨by omega, ?_, fun o ho1 ho2 => ?_⟩
    · rw [show strokeLen s0 m l - ((m - l) * scaleR s0 l + x) = scaleR s0 l - x by omega,
        strokePos_seg (by omega)]
      push_cast [Nat.cast_sub hx2]; ring
    · rcases le_or_gt o (scaleR s0 l) with h | h
      · rw [strokePos_seg h]
        have : scaleR s0 l - x < o := by omega
        have : ((scaleR s0 l - x : ℕ) : ℤ) < o := by exact_mod_cast this
        push_cast [Nat.cast_sub hx2] at this; linarith
      · have hjm : l < m := by
          by_contra hc
          have : strokeLen s0 m l = scaleR s0 l := by
            unfold strokeLen; rw [show m - l + 1 = 1 by omega, one_mul]
          omega
        have := strokePos_mem_V hms hjm h.le ho2
        unfold scaleBelow at hx1; rw [ite_eq_left hjm] at hx1
        have hR := scaleR_succ (s0 := s0) (i := l) (by omega)
        have hx1' : (scaleR s0 (l + 1) : ℤ) < x := by exact_mod_cast hx1
        push_cast [hR] at this ⊢
        linarith [this.1]
  | succ e ih =>
    intro j l hl hlm x hx1 hx2
    have hjm : j < m := by omega
    obtain ⟨hb, hpos, hgt⟩ := ih (j + 1) l (by omega) hlm x hx1 hx2
    have hsp := strokeLen_succ (s0 := s0) (m := m) (i := j) hjm hms
    have hR := scaleR_succ (s0 := s0) (i := j) (by omega)
    refine ⟨by omega, ?_, fun o ho1 ho2 => ?_⟩
    · rw [show strokeLen s0 m j - ((m - l) * scaleR s0 l + x) = scaleR s0 j + strokeLen s0 m (j + 1) +
          (strokeLen s0 m (j + 1) - ((m - l) * scaleR s0 l + x)) by omega,
        strokePos_fwd hjm, hpos]
      push_cast [hR]; ring
    · obtain ⟨o', rfl⟩ : ∃ o', o = scaleR s0 j + strokeLen s0 m (j + 1) + o' :=
        ⟨o - scaleR s0 j - strokeLen s0 m (j + 1), by omega⟩
      rw [strokePos_fwd hjm]
      have := hgt o' (by omega) (by omega)
      push_cast [hR]; linarith

theorem sigma_mul_inj {σ a b : ℤ} (hσ : σ = 1 ∨ σ = -1) (h : σ * a = σ * b) : a = b := by
  rcases hσ with rfl | rfl <;> linarith

/-- **Apex hops** (the eighth paper's Lemma 5.1(b)): for a level-`k` V with apex `α` and
`1 ≤ d ≤ R_k`, `(α - d, α + d)` (in every period) is a hop of `U` of level `k`; the only turn of `U`
strictly inside it is `α`. -/
theorem apexHop_spec {s0 m k : ℕ} (hms : m ≤ s0) (hk1 : 1 ≤ k) (hkm : k ≤ m) {α : ℕ}
    (hα : α ∈ periodVApices s0 m k) {d : ℕ} (hd1 : 1 ≤ d) (hd2 : d ≤ scaleR s0 k) (n : ℤ) :
    IsHopZ (dnpWalk s0 m) ((α : ℤ) - d + n * dnpPeriod s0 m) ((α : ℤ) + d + n * dnpPeriod s0 m) ∧
      HopLevelIs s0 m ((α : ℤ) - d + n * dnpPeriod s0 m) ((α : ℤ) + d + n * dnpPeriod s0 m) k := by
  rw [isHopZ_dnpWalk_add_mul_period, hopLevelIs_add_mul_period]
  obtain ⟨b, σ, hσ, hseg, hback, -⟩ := dnpWalk_V hms hk1 hkm hα
  have hRk : scaleR s0 (k - 1) = 2 * scaleR s0 k := by
    have := scaleR_succ (s0 := s0) (i := k - 1) (by omega); rwa [show k - 1 + 1 = k by omega] at this
  have hpk : scaleR s0 k ≤ strokeLen s0 m k := by unfold strokeLen; nlinarith [scaleR_pos s0 k]
  have hpos : ∀ j : ℤ, -(d : ℤ) ≤ j → j ≤ d → dnpWalk s0 m ((α : ℤ) + j) = b - σ * |j| := by
    intro j hj1 hj2
    rcases le_or_gt 0 j with hj | hj
    · obtain ⟨o, rfl⟩ : ∃ o : ℕ, j = o := ⟨j.toNat, by omega⟩
      rw [hback o (by omega), strokePos_seg (by omega), abs_of_nonneg hj]
    · obtain ⟨o, ho⟩ : ∃ o : ℕ, j = -(o : ℤ) := ⟨(-j).toNat, by omega⟩
      rw [ho, show (α : ℤ) + -(o : ℤ) = α - o by ring, hseg o (by omega), abs_neg,
        abs_of_nonneg (by positivity)]
  have hend : dnpWalk s0 m ((α : ℤ) - d) = b - σ * d := by
    rw [show (α : ℤ) - d = α + (-(d : ℤ)) by ring, hpos _ le_rfl (by omega), abs_neg,
      abs_of_nonneg (by positivity)]
  refine ⟨⟨by omega, ?_, fun t ht => ?_⟩, ⟨α, by omega, by omega, ?_⟩, fun τ l h1 h2 hτ => ?_⟩
  · rw [hpos d (by omega) le_rfl, hend, abs_of_nonneg (by positivity)]
  · rw [mem_Ioo] at ht
    rw [show t = α + (t - α) by ring, hpos (t - α) (by omega) (by omega), hend]
    intro he
    have h2 : |t - α| = d := sigma_mul_inj hσ (by linarith)
    rcases abs_eq (by positivity : (0 : ℤ) ≤ d) |>.1 h2 with h | h <;> omega
  · simpa using isTurnOfLevel_apex hms hk1 hkm hα 0
  · have hα0 : IsTurnOfLevel s0 m (α : ℤ) k := by simpa using isTurnOfLevel_apex hms hk1 hkm hα 0
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, τ = α + j := ⟨τ - α, by ring⟩
    have hj0 : j = 0 := by
      by_contra hne
      apply hτ.isTurnZ hms
      rw [show (α : ℤ) + j + 1 = α + (j + 1) by ring, show (α : ℤ) + j - 1 = α + (j - 1) by ring,
        hpos (j + 1) (by omega) (by omega), hpos j (by omega) (by omega),
        hpos (j - 1) (by omega) (by omega)]
      have key : |j + 1| + |j - 1| = 2 * |j| := by
        rcases lt_or_gt_of_ne hne with hj | hj
        · rw [abs_of_nonpos (by omega : j + 1 ≤ 0), abs_of_neg (by omega : j - 1 < 0),
            abs_of_neg hj]; ring
        · rw [abs_of_pos (by omega : 0 < j + 1), abs_of_nonneg (by omega : 0 ≤ j - 1),
            abs_of_pos hj]; ring
      linear_combination (-σ) * key
    subst hj0
    simp only [add_zero] at hτ
    exact le_of_eq ((hτ.unique hms hα0).symm)

/-- **Valley hops** (the eighth paper's Lemma 5.1(b)): for a level-`k` V with apex `α` and valley
`ν = α + Π_k`, `k ≤ l ≤ m` and `R_{l+1} < x ≤ R_l` (`R_{m+1} = 0`), the valley hop
`(ν - (m - l) R_l - x, ν + x)` at the cell `v + σx` (in every period) is a hop of `U` of level `k`. -/
theorem bandHop_spec {s0 m k l : ℕ} (hms : m ≤ s0) (hk1 : 1 ≤ k) (hkl : k ≤ l) (hlm : l ≤ m)
    {α : ℕ} (hα : α ∈ periodVApices s0 m k) {x : ℕ} (hx1 : scaleBelow s0 m l < x)
    (hx2 : x ≤ scaleR s0 l) (n : ℤ) :
    IsHopZ (dnpWalk s0 m)
        (((α + strokeLen s0 m k : ℕ) : ℤ) - ((m - l) * scaleR s0 l : ℕ) - x + n * dnpPeriod s0 m)
        (((α + strokeLen s0 m k + x : ℕ) : ℤ) + n * dnpPeriod s0 m) ∧
      HopLevelIs s0 m
        (((α + strokeLen s0 m k : ℕ) : ℤ) - ((m - l) * scaleR s0 l : ℕ) - x + n * dnpPeriod s0 m)
        (((α + strokeLen s0 m k + x : ℕ) : ℤ) + n * dnpPeriod s0 m) k := by
  rw [isHopZ_dnpWalk_add_mul_period, hopLevelIs_add_mul_period]
  obtain ⟨b, σ, hσ, -, hback, hfwd⟩ := dnpWalk_V hms hk1 (by omega) hα
  obtain ⟨hy, htail, hgt⟩ := strokePos_tail hms (l - k) k l (by omega) hlm x hx1 hx2
  have hRl : scaleR s0 l ≤ scaleR s0 k := by
    unfold scaleR; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpk : scaleR s0 k ≤ strokeLen s0 m k := by unfold strokeLen; nlinarith [scaleR_pos s0 k]
  have hspan := periodVApices_span_subset hk1 (by omega) hms hα
  set y := (m - l) * scaleR s0 l + x with hydef
  have hp : ((α + strokeLen s0 m k : ℕ) : ℤ) - ((m - l) * scaleR s0 l : ℕ) - x =
      (α : ℤ) + ((strokeLen s0 m k - y : ℕ) : ℤ) := by
    rw [Nat.cast_sub hy, hydef]; push_cast; ring
  have hu : ((α + strokeLen s0 m k + x : ℕ) : ℤ) = (α : ℤ) + strokeLen s0 m k + (x : ℕ) := by
    push_cast; ring
  have hUp : dnpWalk s0 m ((α : ℤ) + ((strokeLen s0 m k - y : ℕ) : ℤ)) = b - σ * (scaleR s0 k - x) := by
    rw [hback _ (by omega), htail]
  have hUu : dnpWalk s0 m ((α : ℤ) + strokeLen s0 m k + (x : ℕ)) = b - σ * scaleR s0 k + σ * x := by
    rw [hfwd x (by omega), strokePos_seg (by omega)]
  have hx0 : 0 < x := by unfold scaleBelow at hx1; split_ifs at hx1 <;> omega
  have hν : IsTurnOfLevel s0 m ((α : ℤ) + (strokeLen s0 m k : ℤ)) k := by
    simpa using isTurnOfLevel_valley hms hk1 (by omega) hα 0
  rw [hp, hu]
  refine ⟨⟨by omega, by rw [hUp, hUu]; ring, fun t ht => ?_⟩,
    ⟨(α : ℤ) + (strokeLen s0 m k : ℤ), by omega, by omega, hν⟩, fun τ l' h1 h2 hτ => ?_⟩
  · rw [mem_Ioo] at ht
    rw [hUp]
    rcases le_or_gt t ((α : ℤ) + (strokeLen s0 m k : ℤ)) with h | h
    · obtain ⟨o, rfl⟩ : ∃ o : ℕ, t = (α : ℤ) + o := ⟨(t - α).toNat, by omega⟩
      rw [hback o (by omega)]
      have := hgt o (by omega) (by omega)
      intro he
      have := sigma_mul_inj hσ (show σ * strokePos s0 m k o = σ * ((scaleR s0 k : ℤ) - x) by linarith)
      linarith
    · obtain ⟨o, rfl⟩ : ∃ o : ℕ, t = (α : ℤ) + (strokeLen s0 m k : ℤ) + o :=
        ⟨(t - α - strokeLen s0 m k).toNat, by omega⟩
      rw [hfwd o (by omega), strokePos_seg (by omega)]
      intro he
      have := sigma_mul_inj hσ (show σ * ((o : ℤ) - 0) = σ * ((x : ℤ) - 0) by linarith)
      omega
  · exact isTurnOfLevel_ge_of_span hms hk1 (by omega) hα 0 (by simp; omega) (by simp; omega) hτ

/-- Every `x ∈ [1, R_k]` lies in a band: `R_{l+1} < x ≤ R_l` for some `k ≤ l ≤ m`. -/
theorem exists_band {s0 m k x : ℕ} (hkm : k ≤ m) (hx1 : 1 ≤ x) (hx2 : x ≤ scaleR s0 k) :
    ∃ l, k ≤ l ∧ l ≤ m ∧ scaleBelow s0 m l < x ∧ x ≤ scaleR s0 l := by
  classical
  set l := Nat.findGreatest (fun l' => k ≤ l' ∧ x ≤ scaleR s0 l') m with hl
  have hspec : k ≤ l ∧ x ≤ scaleR s0 l :=
    Nat.findGreatest_spec (P := fun l' => k ≤ l' ∧ x ≤ scaleR s0 l') hkm ⟨le_rfl, hx2⟩
  have hle : l ≤ m := Nat.findGreatest_le m
  refine ⟨l, hspec.1, hle, ?_, hspec.2⟩
  unfold scaleBelow
  split_ifs with hlm
  · by_contra hc; push Not at hc
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self l) (by omega) ⟨by omega, hc⟩
  · omega

/-- The explicit families of `BlockPairsModel` are hops of `U` of level `k` (in every period). -/
theorem family_spec {s0 m k f : ℕ} (hms : m ≤ s0) (hk1 : 1 ≤ k) (hkm : k + 2 ≤ m) (hf : f < 4)
    {η : ℤ × ℤ} (hη : η ∈ family s0 m k f) (n : ℤ) :
    IsHopZ (dnpWalk s0 m) (η.1 + n * dnpPeriod s0 m) (η.2 + n * dnpPeriod s0 m) ∧
      HopLevelIs s0 m (η.1 + n * dnpPeriod s0 m) (η.2 + n * dnpPeriod s0 m) k := by
  unfold family at hη
  split_ifs at hη with hf0
  · obtain ⟨⟨α, d⟩, hx, rfl⟩ := mem_image.mp hη
    rw [mem_product, mem_Icc] at hx
    exact apexHop_spec hms hk1 (by omega) hx.1 hx.2.1 (by omega) n
  · obtain ⟨⟨α, x⟩, hx, rfl⟩ := mem_image.mp hη
    rw [mem_product, mem_Ioo] at hx
    exact bandHop_spec hms hk1 (by omega : k ≤ k + (f - 1)) (by omega) hx.1 hx.2.1 hx.2.2.le n

/-- The later endpoints of the explicit families lie in `(0, P)`. -/
theorem family_snd_mem {s0 m k f : ℕ} (hms : m ≤ s0) (hk1 : 1 ≤ k) (hkm : k + 2 ≤ m)
    {η : ℤ × ℤ} (hη : η ∈ family s0 m k f) : 0 < η.2 ∧ η.2 < dnpPeriod s0 m := by
  unfold family at hη
  split_ifs at hη with hf0
  · obtain ⟨⟨α, d⟩, hx, rfl⟩ := mem_image.mp hη
    rw [mem_product, mem_Icc] at hx
    have := periodVApices_span_subset hk1 (by omega) hms hx.1
    have : scaleR s0 k ≤ strokeLen s0 m k := by unfold strokeLen; nlinarith [scaleR_pos s0 k]
    simp only; omega
  · obtain ⟨⟨α, x⟩, hx, rfl⟩ := mem_image.mp hη
    rw [mem_product, mem_Ioo] at hx
    have := periodVApices_span_subset hk1 (by omega) hms hx.1
    have hRl : scaleR s0 (k + (f - 1)) ≤ scaleR s0 k := by
      unfold scaleR; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have : scaleR s0 k ≤ strokeLen s0 m k := by unfold strokeLen; nlinarith [scaleR_pos s0 k]
    simp only; constructor <;> push_cast <;> omega

/-- **The families are sets of hops of the class `(h, k)`** (for head `2` in real time, shifted by
`-ξ`), in every period. -/
theorem family_inHopClass {s0 m k f : ℕ} (hms : m ≤ s0) (hk1 : 1 ≤ k) (hkm : k + 2 ≤ m) (hf : f < 4)
    {η : ℤ × ℤ} (hη : η ∈ family s0 m k f) (ξ : ℤ) (h : Bool) (n : ℤ) :
    InHopClass s0 m ξ h k (η.1 - headShift ξ h + n * dnpPeriod s0 m)
      (η.2 - headShift ξ h + n * dnpPeriod s0 m) := by
  rw [inHopClass_iff, show η.1 - headShift ξ h + n * dnpPeriod s0 m + headShift ξ h =
    η.1 + n * dnpPeriod s0 m by ring, show η.2 - headShift ξ h + n * dnpPeriod s0 m + headShift ξ h =
    η.2 + n * dnpPeriod s0 m by ring]
  exact family_spec hms hk1 hkm hf hη n

/-! ### Counting the hops of a level (the eighth paper's Lemma 5.1(c)) -/

open Classical in
/-- The number of hops of `U` of level `k` with later endpoint in the window `[t₀, t₀ + P)`. -/
noncomputable def levelCount (s0 m k : ℕ) (t₀ : ℤ) : ℕ :=
  ((Ico t₀ (t₀ + dnpPeriod s0 m)).filter fun u => HopLevelIs s0 m (dnpPrev s0 m u) u k).card

theorem hopLevelIs_prev_add_period (s0 m k : ℕ) (u : ℤ) :
    HopLevelIs s0 m (dnpPrev s0 m (u + dnpPeriod s0 m)) (u + dnpPeriod s0 m) k ↔
      HopLevelIs s0 m (dnpPrev s0 m u) u k := by
  have h1 := dnpPrev_add_mul_period s0 m u 1
  rw [one_mul] at h1
  rw [h1]
  have := hopLevelIs_add_mul_period s0 m (dnpPrev s0 m u) u 1 k
  rwa [one_mul] at this

/-- The count does not depend on the window. -/
theorem levelCount_window (s0 m k : ℕ) (t₀ : ℤ) : levelCount s0 m k t₀ = levelCount s0 m k 0 := by
  classical
  unfold levelCount
  rw [Finset.card_filter, Finset.card_filter]
  have hP : (0 : ℤ) < dnpPeriod s0 m := by exact_mod_cast dnpPeriod_pos s0 m
  rw [sum_Ico_periodic hP (fun u => by simp only [hopLevelIs_prev_add_period]) t₀,
    sum_Ico_periodic hP (fun u => by simp only [hopLevelIs_prev_add_period]) 0]

/-- Every hop has exactly one level, so the counts of the levels `0, …, m` add up to `P`. -/
theorem sum_levelCount {s0 m : ℕ} (hms : m ≤ s0) (t₀ : ℤ) :
    ∑ k ∈ range (m + 1), levelCount s0 m k t₀ = dnpPeriod s0 m := by
  classical
  unfold levelCount
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  have hone : ∀ u ∈ Ico t₀ (t₀ + dnpPeriod s0 m),
      (∑ k ∈ range (m + 1), if HopLevelIs s0 m (dnpPrev s0 m u) u k then 1 else 0) = 1 := by
    intro u _
    obtain ⟨k, hk⟩ := exists_hopLevelIs hms (isHopZ_dnpPrev s0 m u)
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro k' _ hne
      rw [ite_eq_right (fun h => hne (h.unique hk))]
    · intro hk'; exact absurd (mem_range.mpr (Nat.lt_succ_of_le hk.le_m)) hk'
  rw [Finset.sum_congr rfl hone, Finset.sum_const, Int.card_Ico, smul_eq_mul, mul_one]
  simp

theorem scaleR_mul_pow {s0 k : ℕ} (hk : k ≤ s0) : 2 ^ k * scaleR s0 k = 2 ^ s0 := by
  unfold scaleR; rw [← pow_add]; congr 1; omega

open Classical in
/-- At least `4Λ` hops of each level `k ≥ 1` per period: the `2 R_k` apex and valley hops of each of
the `2^{k+1}` level-`k` V's, with later endpoints in `(0, P]`. -/
theorem listed_subset {s0 m k : ℕ} (hms : m ≤ s0) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    ((periodVApices s0 m k).biUnion fun α =>
      (Icc 1 (scaleR s0 k)).image (fun d : ℕ => ((α + d : ℕ) : ℤ)) ∪
        (Icc 1 (scaleR s0 k)).image (fun x : ℕ => ((α + strokeLen s0 m k + x : ℕ) : ℤ))) ⊆
      (Ico (1 : ℤ) (1 + (dnpPeriod s0 m : ℤ))).filter fun u => HopLevelIs s0 m (dnpPrev s0 m u) u k := by
  have hpk : scaleR s0 k ≤ strokeLen s0 m k := by unfold strokeLen; nlinarith [scaleR_pos s0 k]
  intro u hu
  obtain ⟨α, hα, hu⟩ := mem_biUnion.mp hu
  have hspan := periodVApices_span_subset hk1 hkm hms hα
  rw [mem_filter, mem_Ico]
  rcases mem_union.mp hu with hu | hu
  · obtain ⟨d, hd, rfl⟩ := mem_image.mp hu
    rw [mem_Icc] at hd
    obtain ⟨hhop, hlev⟩ := apexHop_spec hms hk1 hkm hα hd.1 hd.2 0
    simp only [zero_mul, add_zero] at hhop hlev
    rw [show ((α + d : ℕ) : ℤ) = (α : ℤ) + d by push_cast; ring, ← hhop.eq_dnpPrev]
    exact ⟨⟨by omega, by omega⟩, hlev⟩
  · obtain ⟨x, hx, rfl⟩ := mem_image.mp hu
    rw [mem_Icc] at hx
    obtain ⟨l, hkl, hlm, hl1, hl2⟩ := exists_band hkm hx.1 hx.2
    obtain ⟨hhop, hlev⟩ := bandHop_spec hms hk1 hkl hlm hα hl1 hl2 0
    simp only [zero_mul, add_zero] at hhop hlev
    rw [← hhop.eq_dnpPrev]
    exact ⟨⟨by omega, by push_cast; omega⟩, hlev⟩

theorem card_listed {s0 m k : ℕ} (hms : m ≤ s0) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    ((periodVApices s0 m k).biUnion fun α =>
      (Icc 1 (scaleR s0 k)).image (fun d : ℕ => ((α + d : ℕ) : ℤ)) ∪
        (Icc 1 (scaleR s0 k)).image (fun x : ℕ => ((α + strokeLen s0 m k + x : ℕ) : ℤ))).card =
      4 * 2 ^ s0 := by
  classical
  have hpk : scaleR s0 k ≤ strokeLen s0 m k := by unfold strokeLen; nlinarith [scaleR_pos s0 k]
  rw [Finset.card_biUnion]
  · have hinner : ∀ α ∈ periodVApices s0 m k,
        ((Icc 1 (scaleR s0 k)).image (fun d : ℕ => ((α + d : ℕ) : ℤ)) ∪
          (Icc 1 (scaleR s0 k)).image (fun x : ℕ => ((α + strokeLen s0 m k + x : ℕ) : ℤ))).card =
          2 * scaleR s0 k := by
      intro α _
      rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun a b h => by
          simp only [Nat.cast_inj] at h; omega),
        Finset.card_image_of_injective _ (fun a b h => by simp only [Nat.cast_inj] at h; omega),
        Nat.card_Icc]
      · omega
      · rw [Finset.disjoint_left]
        intro u h1 h2
        obtain ⟨d, hd, rfl⟩ := mem_image.mp h1
        obtain ⟨x, hx, he⟩ := mem_image.mp h2
        rw [mem_Icc] at hd hx
        simp only [Nat.cast_inj] at he
        omega
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, card_periodVApices hk1 hkm hms, smul_eq_mul,
      ← scaleR_mul_pow (s0 := s0) (k := k) (by omega)]
    ring
  · intro α hα α' hα' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro u h1 h2
    have hd := periodVApices_spans_disjoint hk1 hkm hms hα hα' hne
    rcases mem_union.mp h1 with h1 | h1 <;> rcases mem_union.mp h2 with h2 | h2 <;>
      obtain ⟨a, ha, rfl⟩ := mem_image.mp h1 <;> obtain ⟨b, hb, he⟩ := mem_image.mp h2 <;>
      rw [mem_Icc] at ha hb <;> simp only [Nat.cast_inj] at he <;> omega

theorem levelCount_ge {s0 m k : ℕ} (hms : m ≤ s0) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    4 * 2 ^ s0 ≤ levelCount s0 m k 1 := by
  classical
  unfold levelCount
  rw [← card_listed hms hk1 hkm]
  convert Finset.card_le_card (listed_subset hms hk1 hkm) using 2

/-- A discrete intermediate value theorem for `U`. -/
theorem dnpWalk_ivt {s0 m : ℕ} (hms : m ≤ s0) (c : ℤ) : ∀ (n : ℕ) (a : ℤ),
    ((dnpWalk s0 m a ≤ c ∧ c ≤ dnpWalk s0 m (a + n)) ∨
      (dnpWalk s0 m (a + n) ≤ c ∧ c ≤ dnpWalk s0 m a)) →
    ∃ t, a ≤ t ∧ t ≤ a + n ∧ dnpWalk s0 m t = c := by
  intro n
  induction n with
  | zero => intro a h; exact ⟨a, le_rfl, by simp, by simp at h; omega⟩
  | succ n ih =>
    intro a h
    by_cases hc : dnpWalk s0 m a = c
    · exact ⟨a, le_rfl, by omega, hc⟩
    have hs := dnpStep_pm hms a
    unfold dnpStep at hs
    obtain ⟨t, h1, h2, h3⟩ := ih (a + 1) (by
      rw [show a + 1 + (n : ℤ) = a + ((n + 1 : ℕ) : ℤ) by push_cast; ring]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hs with hs | hs
      · left; constructor <;> omega
      · left; constructor <;> omega
      · right; constructor <;> omega
      · right; constructor <;> omega)
    exact ⟨t, by omega, by push_cast; omega, h3⟩

open Classical in
/-- The first visit of `U` to the cell `c` after the time `τ` (if any). -/
noncomputable def firstVisit (s0 m : ℕ) (τ c : ℤ) : ℤ :=
  if h : ∃ d : ℕ, 0 < d ∧ dnpWalk s0 m (τ + d) = c then τ + Nat.find h else τ

theorem firstVisit_spec {s0 m : ℕ} {τ c : ℤ} {d : ℕ} (hd : 0 < d) (hdc : dnpWalk s0 m (τ + d) = c) :
    τ < firstVisit s0 m τ c ∧ firstVisit s0 m τ c ≤ τ + d ∧
      dnpWalk s0 m (firstVisit s0 m τ c) = c ∧
      ∀ t, τ < t → t < firstVisit s0 m τ c → dnpWalk s0 m t ≠ c := by
  classical
  have hex : ∃ d : ℕ, 0 < d ∧ dnpWalk s0 m (τ + d) = c := ⟨d, hd, hdc⟩
  have hfv : firstVisit s0 m τ c = τ + Nat.find hex := by unfold firstVisit; rw [dite_eq_left hex]
  have hspec := Nat.find_spec hex
  rw [hfv]
  refine ⟨by omega, by have := Nat.find_min' hex ⟨hd, hdc⟩; omega, hspec.2, fun t h1 h2 => ?_⟩
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, t = τ + e := ⟨(t - τ).toNat, by omega⟩
  have := Nat.find_min hex (show e < Nat.find hex by omega)
  intro he; exact this ⟨by omega, he⟩

/-- The hop ending at the first visit to a cell after a tip contains the tip: it has level `0`. -/
theorem hopLevelIs_firstVisit {s0 m : ℕ} (j : ℕ) (hj : j = 1 ∨ j = 3) {c : ℤ}
    {d : ℕ} (hd : 0 < d) (hdc : dnpWalk s0 m ((j * strokeLen s0 m 0 : ℕ) + d) = c)
    (hne : dnpWalk s0 m (j * strokeLen s0 m 0 : ℕ) ≠ c) :
    HopLevelIs s0 m (dnpPrev s0 m (firstVisit s0 m (j * strokeLen s0 m 0 : ℕ) c))
      (firstVisit s0 m (j * strokeLen s0 m 0 : ℕ) c) 0 := by
  set τ : ℤ := ((j * strokeLen s0 m 0 : ℕ) : ℤ)
  obtain ⟨h1, -, h3, h4⟩ := firstVisit_spec hd hdc
  set u := firstVisit s0 m τ c
  have hhop := isHopZ_dnpPrev s0 m u
  have hpτ : dnpPrev s0 m u < τ := by
    by_contra hc; push Not at hc
    rcases eq_or_lt_of_le hc with he | hlt
    · apply hne; rw [he, ← hhop.2.1, h3]
    · exact h4 _ hlt hhop.1 (by rw [← hhop.2.1, h3])
  have htip := isTurnOfLevel_tip (s0 := s0) (m := m) j hj 0
  rw [zero_mul, add_zero] at htip
  exact ⟨⟨τ, hpτ, h1, htip⟩, fun _ _ _ _ _ => Nat.zero_le _⟩

theorem dnpWalk_tip_one {s0 m : ℕ} (hms : m ≤ s0) :
    dnpWalk s0 m ((1 * strokeLen s0 m 0 : ℕ) : ℤ) = scaleR s0 0 := by
  have := dnpWalk_stroke hms (q := 1) (o := 0) (by norm_num) (Nat.zero_le _)
  rw [add_zero] at this
  rw [this, strokePos_zero]; simp [zeroStart]

theorem dnpWalk_tip_three {s0 m : ℕ} (hms : m ≤ s0) :
    dnpWalk s0 m ((3 * strokeLen s0 m 0 : ℕ) : ℤ) = -(scaleR s0 0 : ℤ) := by
  have := dnpWalk_stroke hms (q := 3) (o := 0) (by norm_num) (Nat.zero_le _)
  rw [add_zero] at this
  rw [this, strokePos_zero]; simp [zeroStart]

/-- At least `4Λ` hops of level `0` per period: at each of the two tips of a period, one hop for each
of the other `2Λ` cells of `[-Λ, Λ]`. -/
theorem levelCount_zero_ge {s0 m : ℕ} (hms : m ≤ s0) :
    4 * 2 ^ s0 ≤ levelCount s0 m 0 (strokeLen s0 m 0 + 1) := by
  classical
  have hpi := strokeLen_pos s0 m 0
  have hΛ : (scaleR s0 0 : ℤ) = ((2 ^ s0 : ℕ) : ℤ) := by unfold scaleR; simp
  set τ1 : ℤ := ((1 * strokeLen s0 m 0 : ℕ) : ℤ) with hτ1d
  set τ3 : ℤ := ((3 * strokeLen s0 m 0 : ℕ) : ℤ) with hτ3d
  have hτ1 : τ1 = (strokeLen s0 m 0 : ℤ) := by rw [hτ1d]; push_cast; ring
  have hτ3 : τ3 = 3 * (strokeLen s0 m 0 : ℤ) := by rw [hτ3d]; push_cast; ring
  have hU1 : dnpWalk s0 m τ1 = scaleR s0 0 := dnpWalk_tip_one hms
  have hU3 : dnpWalk s0 m τ3 = -(scaleR s0 0 : ℤ) := dnpWalk_tip_three hms
  have hU5 : dnpWalk s0 m (τ3 + ((2 * strokeLen s0 m 0 : ℕ) : ℤ)) = scaleR s0 0 := by
    rw [show τ3 + ((2 * strokeLen s0 m 0 : ℕ) : ℤ) = τ1 + 1 * dnpPeriod s0 m by
      rw [hτ1, hτ3]; unfold dnpPeriod; push_cast; ring, dnpWalk_add_mul_period, hU1]
  have hvis1 : ∀ c ∈ Ico (-(scaleR s0 0 : ℤ)) (scaleR s0 0), ∃ d : ℕ, 0 < d ∧
      d ≤ 2 * strokeLen s0 m 0 ∧ dnpWalk s0 m (τ1 + d) = c := by
    intro c hc
    rw [mem_Ico] at hc
    obtain ⟨t, ht1, ht2, ht3⟩ := dnpWalk_ivt hms c (2 * strokeLen s0 m 0) τ1 (Or.inr ⟨by
      rw [show τ1 + ((2 * strokeLen s0 m 0 : ℕ) : ℤ) = τ3 by rw [hτ1, hτ3]; push_cast; ring, hU3]
      omega, by omega⟩)
    have : t ≠ τ1 := by rintro rfl; omega
    refine ⟨(t - τ1).toNat, by omega, ?_, by rw [show τ1 + ((t - τ1).toNat : ℤ) = t by omega, ht3]⟩
    push_cast at ht2; omega
  have hvis3 : ∀ c ∈ Ioc (-(scaleR s0 0 : ℤ)) (scaleR s0 0), ∃ d : ℕ, 0 < d ∧
      d ≤ 2 * strokeLen s0 m 0 ∧ dnpWalk s0 m (τ3 + d) = c := by
    intro c hc
    rw [mem_Ioc] at hc
    obtain ⟨t, ht1, ht2, ht3⟩ := dnpWalk_ivt hms c (2 * strokeLen s0 m 0) τ3 (Or.inl ⟨by omega, by
      rw [hU5]; omega⟩)
    have : t ≠ τ3 := by rintro rfl; omega
    refine ⟨(t - τ3).toNat, by omega, ?_, by rw [show τ3 + ((t - τ3).toNat : ℤ) = t by omega, ht3]⟩
    push_cast at ht2; omega
  have hfv1 : ∀ c ∈ Ico (-(scaleR s0 0 : ℤ)) (scaleR s0 0), τ1 < firstVisit s0 m τ1 c ∧
      firstVisit s0 m τ1 c ≤ τ3 ∧ dnpWalk s0 m (firstVisit s0 m τ1 c) = c ∧
      HopLevelIs s0 m (dnpPrev s0 m (firstVisit s0 m τ1 c)) (firstVisit s0 m τ1 c) 0 := by
    intro c hc
    obtain ⟨d, hd0, hd2, hdc⟩ := hvis1 c hc
    obtain ⟨a1, a2, a3, -⟩ := firstVisit_spec hd0 hdc
    rw [mem_Ico] at hc
    have hd2' : (d : ℤ) ≤ 2 * (strokeLen s0 m 0 : ℤ) := by exact_mod_cast hd2
    exact ⟨a1, by omega, a3, hopLevelIs_firstVisit 1 (Or.inl rfl) hd0 hdc (by rw [hU1]; omega)⟩
  have hfv3 : ∀ c ∈ Ioc (-(scaleR s0 0 : ℤ)) (scaleR s0 0), τ3 < firstVisit s0 m τ3 c ∧
      firstVisit s0 m τ3 c ≤ τ3 + 2 * (strokeLen s0 m 0 : ℤ) ∧
      dnpWalk s0 m (firstVisit s0 m τ3 c) = c ∧
      HopLevelIs s0 m (dnpPrev s0 m (firstVisit s0 m τ3 c)) (firstVisit s0 m τ3 c) 0 := by
    intro c hc
    obtain ⟨d, hd0, hd2, hdc⟩ := hvis3 c hc
    obtain ⟨a1, a2, a3, -⟩ := firstVisit_spec hd0 hdc
    rw [mem_Ioc] at hc
    have hd2' : (d : ℤ) ≤ 2 * (strokeLen s0 m 0 : ℤ) := by exact_mod_cast hd2
    exact ⟨a1, by omega, a3, hopLevelIs_firstVisit 3 (Or.inr rfl) hd0 hdc (by rw [hU3]; omega)⟩
  set S1 := (Ico (-(scaleR s0 0 : ℤ)) (scaleR s0 0)).image fun c => firstVisit s0 m τ1 c
  set S3 := (Ioc (-(scaleR s0 0 : ℤ)) (scaleR s0 0)).image fun c => firstVisit s0 m τ3 c
  have hcard1 : S1.card = 2 * 2 ^ s0 := by
    rw [Finset.card_image_of_injOn (fun c1 h1 c2 h2 he => by
      have e1 := (hfv1 c1 h1).2.2.1; have e2 := (hfv1 c2 h2).2.2.1
      rw [← e1, ← e2]; exact congrArg (dnpWalk s0 m) he), Int.card_Ico, hΛ]
    omega
  have hcard3 : S3.card = 2 * 2 ^ s0 := by
    rw [Finset.card_image_of_injOn (fun c1 h1 c2 h2 he => by
      have e1 := (hfv3 c1 h1).2.2.1; have e2 := (hfv3 c2 h2).2.2.1
      rw [← e1, ← e2]; exact congrArg (dnpWalk s0 m) he), Int.card_Ioc, hΛ]
    omega
  have hdisj : Disjoint S1 S3 := by
    rw [Finset.disjoint_left]
    intro u h1 h3
    obtain ⟨c1, hc1, rfl⟩ := mem_image.mp h1
    obtain ⟨c3, hc3, he⟩ := mem_image.mp h3
    have := (hfv1 c1 hc1).2.1; have := (hfv3 c3 hc3).1
    omega
  have hsub : S1 ∪ S3 ⊆ (Ico ((strokeLen s0 m 0 : ℤ) + 1)
      ((strokeLen s0 m 0 : ℤ) + 1 + dnpPeriod s0 m)).filter
        fun u => HopLevelIs s0 m (dnpPrev s0 m u) u 0 := by
    have hPd : (dnpPeriod s0 m : ℤ) = 4 * (strokeLen s0 m 0 : ℤ) := by unfold dnpPeriod; push_cast; ring
    intro u hu
    rw [mem_filter, mem_Ico]
    rcases mem_union.mp hu with hu | hu
    · obtain ⟨c, hc, rfl⟩ := mem_image.mp hu
      obtain ⟨a1, a2, -, a4⟩ := hfv1 c hc
      exact ⟨⟨by omega, by omega⟩, a4⟩
    · obtain ⟨c, hc, rfl⟩ := mem_image.mp hu
      obtain ⟨a1, a2, -, a4⟩ := hfv3 c hc
      exact ⟨⟨by omega, by omega⟩, a4⟩
  unfold levelCount
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hcard1, hcard3] at this
  convert this using 1
  ring

/-- **Every level has exactly `4Λ` hops per period** (the eighth paper's Lemma 5.1(c)), for every
window of later endpoints. -/
theorem levelCount_eq {s0 m k : ℕ} (hms : m ≤ s0) (hk : k ≤ m) (t₀ : ℤ) :
    levelCount s0 m k t₀ = 4 * 2 ^ s0 := by
  have hsum := sum_levelCount hms 0
  have hge : ∀ k ∈ range (m + 1), 4 * 2 ^ s0 ≤ levelCount s0 m k 0 := by
    intro k hk
    rw [mem_range] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [← levelCount_window s0 m 0 ((strokeLen s0 m 0 : ℤ) + 1)]
      exact levelCount_zero_ge hms
    · rw [← levelCount_window s0 m k 1]; exact levelCount_ge hms hk1 (by omega)
  have hP : dnpPeriod s0 m = (m + 1) * (4 * 2 ^ s0) := by
    unfold dnpPeriod strokeLen scaleR; simp only [Nat.sub_zero]; ring
  rw [levelCount_window]
  by_contra hne
  have hgt : 4 * 2 ^ s0 < levelCount s0 m k 0 :=
    lt_of_le_of_ne (hge k (mem_range.mpr (by omega))) (Ne.symm hne)
  have := Finset.sum_lt_sum hge ⟨k, mem_range.mpr (by omega), hgt⟩
  rw [hsum, Finset.sum_const, card_range, smul_eq_mul] at this
  omega

open Classical in
/-- **The hops of level `k ≥ 1` are exactly the listed ones** (the eighth paper's Lemma 5.1(b)): the
hops of `U` of level `k` with later endpoint in `(0, P]` are the apex hops `(α - d, α + d)` and the
valley hops ending at `ν + x` (`1 ≤ d, x ≤ R_k`) of the level-`k` V's of the period. -/
theorem levelHops_eq_listed {s0 m k : ℕ} (hms : m ≤ s0) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    (Ico (1 : ℤ) (1 + (dnpPeriod s0 m : ℤ))).filter (fun u => HopLevelIs s0 m (dnpPrev s0 m u) u k) =
      (periodVApices s0 m k).biUnion fun α =>
        (Icc 1 (scaleR s0 k)).image (fun d : ℕ => ((α + d : ℕ) : ℤ)) ∪
          (Icc 1 (scaleR s0 k)).image (fun x : ℕ => ((α + strokeLen s0 m k + x : ℕ) : ℤ)) := by
  symm
  apply Finset.eq_of_subset_of_card_le (listed_subset hms hk1 hkm)
  rw [card_listed hms hk1 hkm, ← levelCount_eq hms hkm 1]
  unfold levelCount
  exact le_of_eq (by congr 1)

/-! ### The hops of the heads and of the `r`-fold cover -/

/-- The previous visit of head `h` to its cell at time `u`. -/
def headPrev (s0 m : ℕ) (ξ : ℤ) (h : Bool) (u : ℤ) : ℤ :=
  dnpPrev s0 m (u + headShift ξ h) - headShift ξ h

theorem isHopZ_headPrev (s0 m : ℕ) (ξ : ℤ) (h : Bool) (u : ℤ) :
    IsHopZ (headWalk s0 m ξ h) (headPrev s0 m ξ h u) u := by
  rw [isHopZ_headWalk_iff]; unfold headPrev; rw [sub_add_cancel]; exact isHopZ_dnpPrev s0 m _

theorem IsHopZ.eq_headPrev {s0 m : ℕ} {ξ : ℤ} {h : Bool} {p u : ℤ}
    (hh : IsHopZ (headWalk s0 m ξ h) p u) : p = headPrev s0 m ξ h u :=
  hh.eq_of_snd (isHopZ_headPrev s0 m ξ h u)

theorem headPrev_add_mul_period (s0 m : ℕ) (ξ : ℤ) (h : Bool) (u n : ℤ) :
    headPrev s0 m ξ h (u + n * dnpPeriod s0 m) = headPrev s0 m ξ h u + n * dnpPeriod s0 m := by
  unfold headPrev
  rw [show u + n * dnpPeriod s0 m + headShift ξ h = (u + headShift ξ h) + n * dnpPeriod s0 m by ring,
    dnpPrev_add_mul_period]; ring

theorem headPrev_ge (s0 m : ℕ) (ξ : ℤ) (h : Bool) (u : ℤ) :
    u - dnpPeriod s0 m ≤ headPrev s0 m ξ h u := by
  unfold headPrev; have := dnpPrev_ge s0 m (u + headShift ξ h); linarith

theorem isHopZ_headWalk_add_mul_period (s0 m : ℕ) (ξ : ℤ) (h : Bool) (p u n : ℤ) :
    IsHopZ (headWalk s0 m ξ h) (p + n * dnpPeriod s0 m) (u + n * dnpPeriod s0 m) ↔
      IsHopZ (headWalk s0 m ξ h) p u := by
  rw [isHopZ_headWalk_iff, isHopZ_headWalk_iff, show p + n * dnpPeriod s0 m + headShift ξ h =
    (p + headShift ξ h) + n * dnpPeriod s0 m by ring, show u + n * dnpPeriod s0 m + headShift ξ h =
    (u + headShift ξ h) + n * dnpPeriod s0 m by ring, isHopZ_dnpWalk_add_mul_period]

theorem headHopLevelIs_add_mul_period (s0 m : ℕ) (ξ : ℤ) (h : Bool) (p u n : ℤ) (k : ℕ) :
    HeadHopLevelIs s0 m ξ h (p + n * dnpPeriod s0 m) (u + n * dnpPeriod s0 m) k ↔
      HeadHopLevelIs s0 m ξ h p u k := by
  rw [headHopLevelIs_iff, headHopLevelIs_iff, show p + n * dnpPeriod s0 m + headShift ξ h =
    (p + headShift ξ h) + n * dnpPeriod s0 m by ring, show u + n * dnpPeriod s0 m + headShift ξ h =
    (u + headShift ξ h) + n * dnpPeriod s0 m by ring, hopLevelIs_add_mul_period]

/-- The hops of head `h` on the `r`-fold cover of the pair (time axis `ℤ_{rP}`), each given by its
lift `(p, u)` with later endpoint `u ∈ [0, rP)`. -/
def coverHops (s0 m : ℕ) (ξ : ℤ) (r : ℕ) (h : Bool) : Finset (ℤ × ℤ) :=
  ((Ico (-(dnpPeriod s0 m : ℤ)) ((r : ℤ) * dnpPeriod s0 m)) ×ˢ
    (Ico 0 ((r : ℤ) * dnpPeriod s0 m))).filter fun η => IsHopZ (headWalk s0 m ξ h) η.1 η.2

theorem mem_coverHops {s0 m : ℕ} {ξ : ℤ} {r : ℕ} {h : Bool} {η : ℤ × ℤ} :
    η ∈ coverHops s0 m ξ r h ↔
      η.2 ∈ Ico 0 ((r : ℤ) * dnpPeriod s0 m) ∧ η.1 = headPrev s0 m ξ h η.2 := by
  unfold coverHops
  rw [mem_filter, mem_product]
  constructor
  · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h2, h3.eq_headPrev⟩
  · rintro ⟨h2, h3⟩
    have hge := headPrev_ge s0 m ξ h η.2
    have hhop := isHopZ_headPrev s0 m ξ h η.2
    rw [mem_Ico] at h2
    refine ⟨⟨mem_Ico.mpr ⟨by rw [h3]; linarith, by rw [h3]; linarith [hhop.1]⟩, mem_Ico.mpr h2⟩, ?_⟩
    rw [h3]; exact hhop

theorem coverHops_eq_image (s0 m : ℕ) (ξ : ℤ) (r : ℕ) (h : Bool) :
    coverHops s0 m ξ r h = (Ico 0 ((r : ℤ) * dnpPeriod s0 m)).image fun u => (headPrev s0 m ξ h u, u) := by
  ext η
  rw [mem_coverHops, mem_image]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨η.2, h1, Prod.ext h2.symm rfl⟩
  · rintro ⟨u, hu, rfl⟩; exact ⟨hu, rfl⟩

/-- Every time is the later endpoint of exactly one hop of each head: the cover has `rP` hops of each
head. -/
theorem card_coverHops (s0 m : ℕ) (ξ : ℤ) (r : ℕ) (h : Bool) :
    (coverHops s0 m ξ r h).card = r * dnpPeriod s0 m := by
  rw [coverHops_eq_image, Finset.card_image_of_injective _ (fun a b hab => by
    simp only [Prod.mk.injEq] at hab; exact hab.2), Int.card_Ico, sub_zero,
    show ((r : ℤ) * dnpPeriod s0 m) = ((r * dnpPeriod s0 m : ℕ) : ℤ) by push_cast; ring,
    Int.toNat_natCast]

/-- The number `n_h` of hops of the `r`-fold cover (both heads). -/
def coverHopCount (s0 m : ℕ) (ξ : ℤ) (r : ℕ) : ℕ :=
  (coverHops s0 m ξ r true).card + (coverHops s0 m ξ r false).card

/-- `n_h = 2T` with `T = rP`. -/
theorem coverHopCount_eq (s0 m : ℕ) (ξ : ℤ) (r : ℕ) :
    coverHopCount s0 m ξ r = 2 * (r * dnpPeriod s0 m) := by
  unfold coverHopCount; rw [card_coverHops, card_coverHops]; ring

/-- The hops of the cover are the residues of the hops on `ℤ`: every hop of head `h` is congruent
modulo `rP` to exactly one element of `coverHops`. -/
theorem existsUnique_coverHops {s0 m : ℕ} {ξ : ℤ} {r : ℕ} (hr : 0 < r) {h : Bool} {p u : ℤ}
    (hη : IsHopZ (headWalk s0 m ξ h) p u) :
    ∃! n : ℤ, (p + n * (r * dnpPeriod s0 m), u + n * (r * dnpPeriod s0 m)) ∈ coverHops s0 m ξ r h := by
  have hT : (0 : ℤ) < r * dnpPeriod s0 m := by
    have := dnpPeriod_pos s0 m; positivity
  have hshift : ∀ n : ℤ, IsHopZ (headWalk s0 m ξ h) (p + n * (r * dnpPeriod s0 m))
      (u + n * (r * dnpPeriod s0 m)) := by
    intro n
    rw [show n * (r * (dnpPeriod s0 m : ℤ)) = (n * r) * dnpPeriod s0 m by ring,
      isHopZ_headWalk_add_mul_period]; exact hη
  refine ⟨-(u / (r * dnpPeriod s0 m)), ?_, fun n hn => ?_⟩
  · dsimp only
    rw [mem_coverHops]
    refine ⟨mem_Ico.mpr ⟨?_, ?_⟩, (hshift _).eq_headPrev⟩
    · have := Int.emod_add_mul_ediv u (r * dnpPeriod s0 m)
      have := Int.emod_nonneg u hT.ne'
      simp only; nlinarith
    · have := Int.emod_add_mul_ediv u (r * dnpPeriod s0 m)
      have := Int.emod_lt_of_pos u hT
      simp only; nlinarith
  · dsimp only at hn
    rw [mem_coverHops, mem_Ico] at hn
    obtain ⟨⟨h1, h2⟩, -⟩ := hn
    simp only at h1 h2
    have e1 := Int.emod_add_mul_ediv u (r * dnpPeriod s0 m)
    have e2 := Int.emod_nonneg u hT.ne'
    have e3 := Int.emod_lt_of_pos u hT
    have key : (n + u / (r * dnpPeriod s0 m)) * (r * dnpPeriod s0 m) = u + n * (r * dnpPeriod s0 m) - u % (r * dnpPeriod s0 m) := by
      linarith
    have hlt : -(r * (dnpPeriod s0 m : ℤ)) < (n + u / (r * dnpPeriod s0 m)) * (r * dnpPeriod s0 m) := by
      linarith
    have hgt : (n + u / (r * dnpPeriod s0 m)) * (r * dnpPeriod s0 m) < r * dnpPeriod s0 m := by linarith
    have h0 : n + u / (r * dnpPeriod s0 m) = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have : (n + u / (r * dnpPeriod s0 m)) * (r * dnpPeriod s0 m) ≤ -(r * dnpPeriod s0 m) := by
          nlinarith
        linarith
      · have : r * (dnpPeriod s0 m : ℤ) ≤ (n + u / (r * dnpPeriod s0 m)) * (r * dnpPeriod s0 m) := by
          nlinarith
        linarith
    linarith

open Classical in
/-- The **class** `(h, k)` on the `r`-fold cover: the hops of head `h` of level `k`. -/
noncomputable def coverClass (s0 m : ℕ) (ξ : ℤ) (r : ℕ) (h : Bool) (k : ℕ) : Finset (ℤ × ℤ) :=
  (coverHops s0 m ξ r h).filter fun η => HeadHopLevelIs s0 m ξ h η.1 η.2 k

open Classical in
theorem mem_coverClass {s0 m : ℕ} {ξ : ℤ} {r : ℕ} {h : Bool} {k : ℕ} {η : ℤ × ℤ} :
    η ∈ coverClass s0 m ξ r h k ↔
      η.2 ∈ Ico 0 ((r : ℤ) * dnpPeriod s0 m) ∧ InHopClass s0 m ξ h k η.1 η.2 := by
  unfold coverClass InHopClass
  rw [mem_filter, mem_coverHops]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by rw [h2]; exact isHopZ_headPrev s0 m ξ h _, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2.eq_headPrev⟩, h3⟩

open Classical in
theorem sum_coverClass {M : Type*} [AddCommMonoid M] (s0 m : ℕ) (ξ : ℤ) (r : ℕ) (h : Bool) (k : ℕ)
    (F : ℤ × ℤ → M) :
    ∑ η ∈ coverClass s0 m ξ r h k, F η =
      ∑ u ∈ Ico 0 ((r : ℤ) * dnpPeriod s0 m),
        if HeadHopLevelIs s0 m ξ h (headPrev s0 m ξ h u) u k then F (headPrev s0 m ξ h u, u) else 0 := by
  unfold coverClass
  rw [Finset.sum_filter, coverHops_eq_image, Finset.sum_image (fun a _ b _ hab => by
    simp only [Prod.mk.injEq] at hab; exact hab.2)]

open Classical in
/-- **Every class has exactly `4rΛ` hops on the `r`-fold cover** (the eighth paper's
Lemma 5.1(c)). -/
theorem card_coverClass {s0 m : ℕ} (hms : m ≤ s0) (ξ : ℤ) (r : ℕ) (h : Bool) {k : ℕ} (hk : k ≤ m) :
    (coverClass s0 m ξ r h k).card = r * (4 * 2 ^ s0) := by
  have hP : (0 : ℤ) < dnpPeriod s0 m := by exact_mod_cast dnpPeriod_pos s0 m
  rw [Finset.card_eq_sum_ones, sum_coverClass]
  set c := headShift ξ h
  set g : ℤ → ℕ := fun v => if HopLevelIs s0 m (dnpPrev s0 m v) v k then 1 else 0 with hg
  have hrw : ∀ u : ℤ, (if HeadHopLevelIs s0 m ξ h (headPrev s0 m ξ h u) u k then 1 else 0) = g (u + c) := by
    intro u
    simp only [hg, headHopLevelIs_iff]
    unfold headPrev
    rw [sub_add_cancel]
  simp_rw [hrw]
  rw [Finset.sum_Ico_add' g 0 ((r : ℤ) * dnpPeriod s0 m) c, zero_add,
    show (r : ℤ) * dnpPeriod s0 m + c = c + r * dnpPeriod s0 m by ring,
    sum_Ico_mul_periodic hP (fun v => by simp only [hg, hopLevelIs_prev_add_period]) c r,
    smul_eq_mul]
  congr 1
  rw [← levelCount_eq hms hk 0]
  unfold levelCount
  rw [Finset.card_filter, zero_add]

/-- On the `r`-fold cover every class has `n_h/(2N)` hops, `N = m + 1`. -/
theorem card_coverClass_mul {s0 m : ℕ} (hms : m ≤ s0) (ξ : ℤ) (r : ℕ) (h : Bool) {k : ℕ}
    (hk : k ≤ m) :
    2 * (m + 1) * (coverClass s0 m ξ r h k).card = coverHopCount s0 m ξ r := by
  rw [card_coverClass hms ξ r h hk, coverHopCount_eq]
  unfold dnpPeriod strokeLen scaleR; simp only [Nat.sub_zero]; ring

/-- The valley hop of the band containing `x` ends at `ν + x` at the cell `v + σ x`, where `v = U(ν)`
is the valley cell and `σ` the direction of the V's parent stroke; the apex hop of half-width `d`
is at the cell `b - σ d`, `b = U(α)` the base. -/
theorem hop_cells {s0 m k : ℕ} (hms : m ≤ s0) (hk1 : 1 ≤ k) (hkm : k ≤ m) {α : ℕ}
    (hα : α ∈ periodVApices s0 m k) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      (∀ d ≤ scaleR s0 k, dnpWalk s0 m ((α : ℤ) + d) = dnpWalk s0 m α - σ * d ∧
        dnpWalk s0 m ((α : ℤ) - d) = dnpWalk s0 m α - σ * d) ∧
      (∀ x ≤ scaleR s0 k, dnpWalk s0 m ((α : ℤ) + strokeLen s0 m k + x) =
        dnpWalk s0 m ((α : ℤ) + strokeLen s0 m k) + σ * x) := by
  obtain ⟨b, σ, hσ, hseg, hback, hfwd⟩ := dnpWalk_V hms hk1 hkm hα
  have hRk : scaleR s0 (k - 1) = 2 * scaleR s0 k := by
    have := scaleR_succ (s0 := s0) (i := k - 1) (by omega); rwa [show k - 1 + 1 = k by omega] at this
  have hpk : scaleR s0 k ≤ strokeLen s0 m k := by unfold strokeLen; nlinarith [scaleR_pos s0 k]
  have hb : dnpWalk s0 m α = b := by
    have := hback 0 (Nat.zero_le _); simpa [strokePos_zero] using this
  refine ⟨σ, hσ, fun d hd => ⟨?_, ?_⟩, fun x hx => ?_⟩
  · rw [hback d (by omega), strokePos_seg hd, hb]
  · rw [hseg d (by omega), hb]
  · have h0 := hfwd 0 (Nat.zero_le _)
    simp only [Nat.cast_zero, add_zero, strokePos_zero, mul_zero] at h0
    rw [hfwd x (by omega), strokePos_seg (by omega), h0]

/-! ### The number of turns (the eighth paper's Lemma 5.1(a)) -/

theorem sum_two_pow_add_two (m : ℕ) : ∑ i ∈ Icc 1 m, 2 ^ (i + 2) + 8 = 2 ^ (m + 3) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), show 2 ^ (m + 1 + 3) = 2 ^ (m + 3) + 2 ^ (m + 3) by ring]
    rw [show m + 1 + 2 = m + 3 by ring]; omega

/-- **Each head has `2^{m+3} - 6` turns per period** (the eighth paper's Lemma 5.1(a)): the
`2^{l+2}` apex and valley times of each level `l ∈ [1, m]` and the two tips. -/
theorem card_periodTurns {s0 m : ℕ} (hms : m ≤ s0) : (periodTurns s0 m).card = 2 ^ (m + 3) - 6 := by
  classical
  have hpi := strokeLen_pos s0 m 0
  set X := (Icc 1 m).biUnion fun i => periodVApices s0 m i ∪
    (periodVApices s0 m i).image (· + strokeLen s0 m i)
  have hlev : ∀ i ∈ Icc 1 m, ∀ r ∈ periodVApices s0 m i ∪ (periodVApices s0 m i).image
      (· + strokeLen s0 m i), IsTurnOfLevel s0 m (r : ℤ) i := by
    intro i hi r hr
    rw [mem_Icc] at hi
    rcases mem_union.mp hr with hr | hr
    · simpa using isTurnOfLevel_apex hms hi.1 hi.2 hr 0
    · obtain ⟨α, hα, rfl⟩ := mem_image.mp hr
      simpa using isTurnOfLevel_valley hms hi.1 hi.2 hα 0
  have hX : X.card = ∑ i ∈ Icc 1 m, 2 ^ (i + 2) := by
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [mem_Icc] at hi
      exact card_apex_valley hi.1 hi.2 hms
    · intro i hi j hj hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro r h1 h2
      exact hne ((hlev i hi r h1).unique hms (hlev j hj r h2))
  have htip : Disjoint X {strokeLen s0 m 0, 3 * strokeLen s0 m 0} := by
    rw [Finset.disjoint_left]
    intro r hrX hrT
    obtain ⟨i, hi, hr⟩ := mem_biUnion.mp hrX
    have h1 := hlev i hi r hr
    have h2 : IsTurnOfLevel s0 m (r : ℤ) 0 := by
      rw [mem_insert, mem_singleton] at hrT
      rcases hrT with rfl | rfl
      · simpa using isTurnOfLevel_tip (s0 := s0) (m := m) 1 (Or.inl rfl) 0
      · simpa using isTurnOfLevel_tip (s0 := s0) (m := m) 3 (Or.inr rfl) 0
    have := h1.unique hms h2
    rw [mem_Icc] at hi; omega
  have hT : ({strokeLen s0 m 0, 3 * strokeLen s0 m 0} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by rw [mem_singleton]; omega), Finset.card_singleton]
  unfold periodTurns
  rw [Finset.card_union_of_disjoint htip, hX, hT]
  have := sum_two_pow_add_two m
  omega

open Classical in
/-- The turns of `U` in one period `[0, P)` are `2^{m+3} - 6` (the eighth paper's Lemma 5.1(a)). -/
theorem card_turns_period {s0 m : ℕ} (hms : m ≤ s0) :
    ((Ico (0 : ℤ) (dnpPeriod s0 m)).filter fun t => IsTurnZ (dnpWalk s0 m) t).card =
      2 ^ (m + 3) - 6 := by
  classical
  rw [← card_periodTurns hms]
  have hpi := strokeLen_pos s0 m 0
  have hP : (0 : ℤ) < dnpPeriod s0 m := by exact_mod_cast dnpPeriod_pos s0 m
  refine Finset.card_nbij (fun t => t.toNat) (fun t ht => ?_) (fun t₁ h₁ t₂ h₂ he => ?_)
    (fun r hr => ?_)
  · simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq] at ht
    obtain ⟨⟨h1, h2⟩, h3⟩ := ht
    rw [isTurnZ_dnpWalk_iff hms, Int.emod_eq_of_lt h1 h2] at h3
    exact h3
  · simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq] at h₁ h₂
    simp only at he
    omega
  · have hrP : r < dnpPeriod s0 m := by
      rcases mem_periodTurns_cases hr with h | h | ⟨q, hq, x, hx, h⟩
      · unfold dnpPeriod; omega
      · unfold dnpPeriod; omega
      · obtain ⟨-, -, -, h4, -⟩ := strokeTurns_gap hms m 0 (by omega) x hx
        have := scaleR_pos s0 x.2
        unfold dnpPeriod; interval_cases q <;> omega
    refine ⟨(r : ℤ), ?_, by simp⟩
    simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq]
    refine ⟨⟨by positivity, by exact_mod_cast hrP⟩, ?_⟩
    rw [isTurnZ_dnpWalk_iff hms, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hrP),
      Int.toNat_natCast]
    exact hr

end MergeDepth

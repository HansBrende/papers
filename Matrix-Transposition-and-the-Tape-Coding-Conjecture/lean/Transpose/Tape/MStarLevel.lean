import Transpose.Tape.MStarAnalysis

/-!
# Theorem M*: long chords counted by levels (abstract integer sequences)

* `count_le_crossPairs` (finitary form): at a good level `p`, once `n` is large and the rescaled
  sequence is uniformly close to `P`, the long crossing chords of block `⌊p n⌋` inject into the
  consecutive pairs of `Λ(p)` counted by `κ(p)`.
* `levelChords_limsup_le` (the limsup bound): the long label-crossing chords, per `n`, have
  `limsup ≤ ∫⁻ κ`. The proof counts by levels, with a per-block bound, domination on a tail, and
  reverse Fatou.
-/

namespace Transpose.Tape.Impl

open Transpose MeasureTheory Filter Topology

open scoped ENNReal

/-! ### The excised set -/

/-- The endpoints of the intervals of `S`. -/
noncomputable def endpts (I : Finset (ℝ × ℝ)) : Finset ℝ := I.image Prod.fst ∪ I.image Prod.snd

/-- An interval containing no endpoint of `S` and some point off `S` lies off `S`. -/
theorem no_S_of_no_endpts {I : Finset (ℝ × ℝ)} {u v w : ℝ} (hw : w ∈ Set.Icc u v)
    (hwS : w ∉ ⋃ x ∈ I, Set.Icc x.1 x.2) (hE : ∀ e ∈ endpts I, e ∉ Set.Icc u v) :
    ∀ y ∈ Set.Icc u v, y ∉ ⋃ x ∈ I, Set.Icc x.1 x.2 := by
  intro y hy hyS
  apply hwS
  rw [Set.mem_iUnion₂] at hyS ⊢
  obtain ⟨x, hx, hyx⟩ := hyS
  refine ⟨x, hx, ?_⟩
  have h1 : x.1 ∉ Set.Icc u v :=
    hE _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))
  have h2 : x.2 ∉ Set.Icc u v :=
    hE _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx))
  simp only [Set.mem_Icc, not_and_or, not_le] at h1 h2
  rw [Set.mem_Icc] at hy hyx hw ⊢
  constructor
  · rcases h1 with h | h
    · linarith
    · linarith
  · rcases h2 with h | h
    · linarith
    · linarith

/-! ### Long chords -/

theorem mem_longCross {R : ℕ → Finset ℤ} {S : Set ℝ} {β : ℝ → ℕ} {n : ℕ} {η : ℝ} {N z : ℕ}
    {σ : ℤ} :
    (z, σ) ∈ longCross R S β n η N ↔ z < N ∧ σ ∈ R z ∧ ∃ x, IsChord R σ x z ∧
      η * n ≤ (z : ℝ) - x ∧ (x : ℝ) / n ∉ S ∧ (z : ℝ) / n ∉ S ∧
        β ((x : ℝ) / n) ≠ β ((z : ℝ) / n) := by
  classical
  simp only [longCross, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨z', h1, σ', ⟨h3, h4⟩, rfl, rfl⟩; exact ⟨h1, h3, h4⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨z, h1, σ, ⟨h2, h3⟩, rfl, rfl⟩

/-! ### Long crossing chords at a good level, finitary form -/

/-- A point of `[0, c₀]` within `ρ` of `s ∈ (0, c₀)` with a property that holds frequently near `s`
(used for the points above and below a level). -/
theorem exists_near_of_frequently {q : ℝ → Prop} {s ρ c₀ : ℝ} (hρ : 0 < ρ)
    (hs : s ∈ Set.Ioo 0 c₀) (hq : ∃ᶠ x in 𝓝 s, q x) :
    ∃ u, |u - s| < ρ ∧ u ∈ Set.Icc 0 c₀ ∧ q u := by
  have h1 : ∀ᶠ x in 𝓝 s, x ∈ Set.Ioo (s - ρ) (s + ρ) := Ioo_mem_nhds (by linarith) (by linarith)
  have h2 : ∀ᶠ x in 𝓝 s, x ∈ Set.Ioo 0 c₀ := Ioo_mem_nhds hs.1 hs.2
  obtain ⟨u, hu1, hu2, hu3⟩ := (hq.and_eventually (h1.and h2)).exists
  exact ⟨u, by rw [abs_lt]; constructor <;> linarith [hu2.1, hu2.2], ⟨hu3.1.le, hu3.2.le⟩, hu1⟩

section Lemma4

variable {c₀ η : ℝ} {D : ℕ} {P : ℝ → ℝ} {S : Set ℝ} {β : ℝ → ℕ}

/-- **Long crossing chords at a good level (finitary form).** At a good level `p` (finite level
set, no point of `Λ(p)` a local extremum, no point of `Λ(p)` among the finitely many breakpoints),
there are `ε > 0` and `n₀` such that for every `n ≥ n₀` and all data `W, R, N` satisfying
`N ≤ c₀ n`, (V1′), (V2′) and uniform closeness `< ε` to `P` on `[0, c₀]`, the long crossing chords
of block `⌊p n⌋` number at most the consecutive pairs counted by `κ(p)`. -/
theorem count_le_crossPairs (hη : 0 < η) (hP : LipschitzOnWith 1 P (Set.Icc 0 c₀))
    {I : Finset (ℝ × ℝ)} (hSI : S = ⋃ x ∈ I, Set.Icc x.1 x.2) {Z : Finset ℝ}
    (hβZ : ∀ u v, 0 ≤ u → u ≤ v → v ≤ c₀ → (∀ x ∈ Set.Icc u v, x ∉ S ∧ x ∉ (Z : Set ℝ)) →
      β u = β v)
    {p : ℝ} (hfin : (levelSet P c₀ p).Finite)
    (hext : ∀ s ∈ levelSet P c₀ p, ¬IsLocalMin P s ∧ ¬IsLocalMax P s)
    (hZ₀ : ∀ s ∈ levelSet P c₀ p, s ∉ (Z ∪ endpts I ∪ {0, c₀} : Finset ℝ)) :
    ∃ ε > 0, ∃ n₀ : ℕ, ∀ (n : ℕ) (W : ℕ → ℤ) (R : ℕ → Finset ℤ) (N : ℕ), n₀ ≤ n →
      (N : ℝ) ≤ c₀ * n → (∀ y σ, σ ∈ R y → |W y - σ| ≤ D) →
      (∀ y₁ y₂ σ, y₁ ≤ y₂ → (W y₁ < σ ∧ σ < W y₂ ∨ W y₂ < σ ∧ σ < W y₁) →
        ∃ y, y₁ ≤ y ∧ y ≤ y₂ ∧ σ ∈ R y) →
      (∀ u ∈ Set.Icc 0 c₀, dist (P u) ((W ⌊u * n⌋₊ : ℝ) / n) < ε) →
      ((longCross R S β n η N).filter (fun e => e.2 = ⌊p * n⌋)).card ≤
        (crossPairs P S β c₀ p).ncard := by
  classical
  set Λ := levelSet P c₀ p with hΛ
  set ΛF := hfin.toFinset with hΛF
  have hmemF : ∀ s, s ∈ ΛF ↔ s ∈ Λ := fun s => Set.Finite.mem_toFinset hfin
  set Z₀ : Finset ℝ := Z ∪ endpts I ∪ {0, c₀} with hZ₀def
  -- points of the level set are interior
  have hint : ∀ s ∈ Λ, 0 < s ∧ s < c₀ := by
    intro s hs
    have h1 : s ≠ 0 := fun h => hZ₀ s hs (by
      rw [hZ₀def, h]; exact Finset.mem_union_right _ (Finset.mem_insert_self _ _))
    have h2 : s ≠ c₀ := fun h => hZ₀ s hs (by
      rw [hZ₀def, h]
      exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    exact ⟨lt_of_le_of_ne hs.1.1 (Ne.symm h1), lt_of_le_of_ne hs.1.2 h2⟩
  -- Step 1: the window radius `ρ`
  obtain ⟨δ₁, hδ₁, hδ₁s⟩ := exists_pos_le_finset ((ΛF ×ˢ ΛF).filter (fun q => q.1 ≠ q.2))
    (fun q => |q.1 - q.2|) (fun q hq => by
      rw [Finset.mem_filter] at hq; exact abs_pos.2 (sub_ne_zero.2 hq.2))
  obtain ⟨δ₂, hδ₂, hδ₂s⟩ := exists_pos_le_finset (ΛF ×ˢ Z₀) (fun q => |q.1 - q.2|)
    (fun q hq => by
      rw [Finset.mem_product] at hq
      have h1 := (hmemF _).1 hq.1
      have : q.1 ≠ q.2 := fun h => hZ₀ q.1 h1 (h ▸ hq.2)
      exact abs_pos.2 (sub_ne_zero.2 this))
  set ρ := min (min (δ₁ / 4) (δ₂ / 2)) η with hρ
  have hρpos : 0 < ρ := lt_min (lt_min (by linarith) (by linarith)) hη
  have hρη : ρ ≤ η := min_le_right _ _
  have hsep : ∀ s ∈ ΛF, ∀ s' ∈ ΛF, s ≠ s' → 4 * ρ ≤ |s - s'| := by
    intro s hs s' hs' hne
    have := hδ₁s (s, s') (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hs, hs'⟩, hne⟩)
    have : ρ ≤ δ₁ / 4 := le_trans (min_le_left _ _) (min_le_left _ _)
    simp only at *; linarith
  have hfar : ∀ s ∈ ΛF, ∀ z ∈ Z₀, ρ < |s - z| := by
    intro s hs z hz
    have := hδ₂s (s, z) (Finset.mem_product.2 ⟨hs, hz⟩)
    have : ρ ≤ δ₂ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    simp only at *; linarith
  -- Step 2: points above and below the level near each point of `Λ`
  have hup : ∀ s ∈ ΛF, ∃ u, |u - s| < ρ / 2 ∧ u ∈ Set.Icc 0 c₀ ∧ p < P u := by
    intro s hs
    have hsΛ := (hmemF s).1 hs
    have h := (hext s hsΛ).2
    rw [IsLocalMax, IsMaxFilter, Filter.not_eventually] at h
    exact hsΛ.2 ▸ exists_near_of_frequently (by linarith) (hint s hsΛ)
      (h.mono fun x hx => lt_of_not_ge hx)
  have hdn : ∀ s ∈ ΛF, ∃ u, |u - s| < ρ / 2 ∧ u ∈ Set.Icc 0 c₀ ∧ P u < p := by
    intro s hs
    have hsΛ := (hmemF s).1 hs
    have h := (hext s hsΛ).1
    rw [IsLocalMin, IsMinFilter, Filter.not_eventually] at h
    exact hsΛ.2 ▸ exists_near_of_frequently (by linarith) (hint s hsΛ)
      (h.mono fun x hx => lt_of_not_ge hx)
  choose! up hup1 hup2 hup3 using hup
  choose! dn hdn1 hdn2 hdn3 using hdn
  -- Step 3: the margin `c₁`
  obtain ⟨a₁, ha₁, ha₁s⟩ := exists_pos_le_finset ΛF (fun s => P (up s) - p)
    (fun s hs => by have := hup3 s hs; linarith)
  obtain ⟨a₂, ha₂, ha₂s⟩ := exists_pos_le_finset ΛF (fun s => p - P (dn s))
    (fun s hs => by have := hdn3 s hs; linarith)
  -- Step 4: the margin `c₂` off the inner windows
  set K := Set.Icc 0 c₀ \ ⋃ s ∈ ΛF, Set.Ioo (s - ρ / 2) (s + ρ / 2) with hK
  have hKc : IsCompact K :=
    isCompact_Icc.diff (isOpen_biUnion (fun s _ => isOpen_Ioo))
  obtain ⟨c₂, hc₂, hc₂K⟩ : ∃ c₂ > 0, ∀ u ∈ K, c₂ ≤ |P u - p| := by
    rcases K.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun u hu => by rw [he] at hu; exact absurd hu (Set.notMem_empty u)⟩
    · have hcont : ContinuousOn (fun u => |P u - p|) K :=
        ((hP.continuousOn.mono Set.sdiff_subset).sub continuousOn_const).abs
      obtain ⟨u₀, hu₀K, hmin⟩ := hKc.exists_isMinOn hne hcont
      refine ⟨|P u₀ - p|, ?_, fun u hu => hmin hu⟩
      apply abs_pos.2
      intro heq
      have hu₀Λ : u₀ ∈ Λ := ⟨hu₀K.1, by linarith⟩
      apply hu₀K.2
      rw [Set.mem_iUnion₂]
      exact ⟨u₀, (hmemF u₀).2 hu₀Λ, by constructor <;> linarith⟩
  -- Step 5: the constants
  set c₁ := min a₁ a₂ with hc₁
  have hc₁pos : 0 < c₁ := lt_min ha₁ ha₂
  set ε := min c₁ c₂ / 2 with hε
  have hεpos : 0 < ε := by positivity
  have hεc₁ : 2 * ε ≤ c₁ := by rw [hε]; linarith [min_le_left c₁ c₂]
  have hεc₂ : 2 * ε ≤ c₂ := by rw [hε]; linarith [min_le_right c₁ c₂]
  refine ⟨ε, hεpos, ⌈((D : ℝ) + 2) / ε + 2 / ρ⌉₊ + 1, ?_⟩
  intro n W R N hn hN hV1 hV2 hconv
  -- large `n`
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (Nat.le_add_left 1 _) hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hnbig : ((D : ℝ) + 2) / ε + 2 / ρ < n := by
    have := Nat.le_ceil (((D : ℝ) + 2) / ε + 2 / ρ)
    have : ((⌈((D : ℝ) + 2) / ε + 2 / ρ⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this; linarith
  have hDn : ((D : ℝ) + 2) / n < ε := by
    rw [div_lt_iff₀ hnpos]
    have h1 : ((D : ℝ) + 2) / ε < n := by
      have : 0 ≤ 2 / ρ := by positivity
      linarith
    rw [div_lt_iff₀ hεpos] at h1; linarith
  have h1n : 1 / n < ρ / 2 := by
    rw [div_lt_iff₀ hnpos]
    have h1 : 2 / ρ < n := by
      have : 0 ≤ ((D : ℝ) + 2) / ε := by positivity
      linarith
    rw [div_lt_iff₀ hρpos] at h1; linarith
  set σ := ⌊p * n⌋ with hσ
  have hσ1 : (σ : ℝ) ≤ p * n := Int.floor_le _
  have hσ2 : p * n < σ + 1 := Int.lt_floor_add_one _
  -- (i): visits lie in inner windows
  have hvisit : ∀ y, σ ∈ R y → y < N → ∃ s ∈ ΛF, |(y : ℝ) / n - s| < ρ / 2 := by
    intro y hy hyN
    have hyN' : (y : ℝ) < c₀ * n := lt_of_lt_of_le (by exact_mod_cast hyN) hN
    have hu : (y : ℝ) / n ∈ Set.Icc 0 c₀ := by
      constructor
      · positivity
      · rw [div_le_iff₀ hnpos]; linarith
    have hfl : ⌊(y : ℝ) / n * n⌋₊ = y := by
      rw [div_mul_cancel₀ _ hnpos.ne']; exact Nat.floor_natCast y
    have hd := hconv _ hu
    rw [hfl, Real.dist_eq] at hd
    have hW := hV1 y σ hy
    have hW' : |(W y : ℝ) - σ| ≤ D := by exact_mod_cast hW
    have hclose : |P ((y : ℝ) / n) - p| < c₂ := by
      have e1 : |(W y : ℝ) / n - σ / n| ≤ D / n := by
        rw [← sub_div, abs_div, abs_of_pos hnpos]
        exact div_le_div_of_nonneg_right hW' hnpos.le
      have e2 : |(σ : ℝ) / n - p| ≤ 1 / n := by
        have h1 : (σ : ℝ) / n ≤ p := by rw [div_le_iff₀ hnpos]; linarith
        have h2 : p < (σ : ℝ) / n + 1 / n := by
          rw [← add_div, lt_div_iff₀ hnpos]; linarith
        rw [abs_le]; constructor <;> linarith
      have e3 : (D : ℝ) / n + 1 / n ≤ ((D : ℝ) + 2) / n := by
        rw [← add_div]; apply div_le_div_of_nonneg_right _ hnpos.le; linarith
      calc |P ((y : ℝ) / n) - p|
          ≤ |P ((y : ℝ) / n) - (W y : ℝ) / n| + |(W y : ℝ) / n - σ / n| + |(σ : ℝ) / n - p| := by
            have := abs_sub_le (P ((y : ℝ) / n)) ((W y : ℝ) / n) p
            have := abs_sub_le ((W y : ℝ) / n) ((σ : ℝ) / n) p
            linarith
        _ < ε + ε := by linarith
        _ ≤ c₂ := by linarith
    by_contra hno
    push Not at hno
    have huK : (y : ℝ) / n ∈ K := by
      refine ⟨hu, ?_⟩
      rw [Set.mem_iUnion₂]
      rintro ⟨s, hs, hmem⟩
      have h1 := hno s hs
      rw [Set.mem_Ioo] at hmem
      have h2 : |(y : ℝ) / n - s| < ρ / 2 := by
        rw [abs_lt]; constructor <;> linarith [hmem.1, hmem.2]
      linarith
    have := hc₂K _ huK
    linarith
  -- (ii): each window contains a visit
  have hwin : ∀ s ∈ ΛF, ∃ y, σ ∈ R y ∧ |(y : ℝ) / n - s| < ρ := by
    intro s hs
    set a := ⌊up s * n⌋₊ with ha
    set b := ⌊dn s * n⌋₊ with hb
    have hu0 : 0 ≤ up s := (hup2 s hs).1
    have hd0 : 0 ≤ dn s := (hdn2 s hs).1
    have ha1 : (a : ℝ) ≤ up s * n := Nat.floor_le (by positivity)
    have ha2 : up s * n < a + 1 := Nat.lt_floor_add_one _
    have hb1 : (b : ℝ) ≤ dn s * n := Nat.floor_le (by positivity)
    have hb2 : dn s * n < b + 1 := Nat.lt_floor_add_one _
    have hWa : σ < W a := by
      have hd := hconv _ (hup2 s hs)
      rw [Real.dist_eq, abs_lt] at hd
      have h1 : P (up s) - p ≥ c₁ := le_trans (min_le_left _ _) (ha₁s s hs)
      have h2 : ((W a : ℝ) / n) > p + ε := by linarith [hd.1, hd.2]
      have h3 : (W a : ℝ) > p * n + ε * n := by
        rw [gt_iff_lt, lt_div_iff₀ hnpos] at h2; linarith
      have h4 : ε * n > (D : ℝ) + 2 := by
        rw [div_lt_iff₀ hnpos] at hDn; linarith
      have : (σ : ℝ) < W a := by linarith
      exact_mod_cast this
    have hWb : W b < σ := by
      have hd := hconv _ (hdn2 s hs)
      rw [Real.dist_eq, abs_lt] at hd
      have h1 : p - P (dn s) ≥ c₁ := le_trans (min_le_right _ _) (ha₂s s hs)
      have h2 : ((W b : ℝ) / n) < p - ε := by linarith [hd.1, hd.2]
      have h3 : (W b : ℝ) < p * n - ε * n := by
        rw [div_lt_iff₀ hnpos] at h2; linarith
      have h4 : ε * n > (D : ℝ) + 2 := by
        rw [div_lt_iff₀ hnpos] at hDn; linarith
      have : (W b : ℝ) < σ := by linarith
      exact_mod_cast this
    obtain ⟨y, hy1, hy2, hyR⟩ : ∃ y, min a b ≤ y ∧ y ≤ max a b ∧ σ ∈ R y := by
      rcases le_total a b with hab | hab
      · rw [min_eq_left hab, max_eq_right hab]
        exact hV2 a b σ hab (Or.inr ⟨hWb, hWa⟩)
      · rw [min_eq_right hab, max_eq_left hab]
        exact hV2 b a σ hab (Or.inl ⟨hWb, hWa⟩)
    refine ⟨y, hyR, ?_⟩
    have hy1' : ((min a b : ℕ) : ℝ) ≤ y := by exact_mod_cast hy1
    have hy2' : (y : ℝ) ≤ ((max a b : ℕ) : ℝ) := by exact_mod_cast hy2
    have hua := hup1 s hs
    have hdb := hdn1 s hs
    rw [abs_lt] at hua hdb
    rw [abs_lt]
    have kmin : ∀ (c : ℕ) (u : ℝ), u * n < c + 1 → s - ρ / 2 < u →
        s - ρ / 2 - 1 / n < (c : ℝ) / n := by
      intro c u h1 h2
      have : u < ((c : ℝ) + 1) / n := by rw [lt_div_iff₀ hnpos]; linarith
      rw [add_div] at this
      linarith
    have kmax : ∀ (c : ℕ) (u : ℝ), (c : ℝ) ≤ u * n → u < s + ρ / 2 →
        (c : ℝ) / n ≤ s + ρ / 2 := by
      intro c u h1 h2
      have := mul_le_mul_of_nonneg_right h2.le hnpos.le
      rw [div_le_iff₀ hnpos]; linarith
    have hmin : s - ρ / 2 - 1 / n < ((min a b : ℕ) : ℝ) / n := by
      rcases le_total a b with hab | hab
      · rw [min_eq_left hab]; exact kmin a (up s) ha2 (by linarith [hua.1])
      · rw [min_eq_right hab]; exact kmin b (dn s) hb2 (by linarith [hdb.1])
    have hmax : ((max a b : ℕ) : ℝ) / n ≤ s + ρ / 2 := by
      rcases le_total a b with hab | hab
      · rw [max_eq_right hab]; exact kmax b (dn s) hb1 (by linarith [hdb.2])
      · rw [max_eq_left hab]; exact kmax a (up s) ha1 (by linarith [hua.2])
    have hyl : ((min a b : ℕ) : ℝ) / n ≤ (y : ℝ) / n := div_le_div_of_nonneg_right hy1' hnpos.le
    have hyu : (y : ℝ) / n ≤ ((max a b : ℕ) : ℝ) / n := div_le_div_of_nonneg_right hy2' hnpos.le
    constructor <;> linarith
  -- (iii): the injection into consecutive pairs
  -- window inheritance: label and `S`
  have hinherit : ∀ y : ℕ, ∀ s ∈ ΛF, |(y : ℝ) / n - s| < ρ / 2 → (y : ℝ) / n ∉ S →
      s ∉ S ∧ β ((y : ℝ) / n) = β s := by
    intro y s hs hys hyS
    have hsΛ := (hmemF s).1 hs
    set lo := min ((y : ℝ) / n) s
    set hi := max ((y : ℝ) / n) s
    have hlohi : lo ≤ hi := min_le_max
    have hwin' : ∀ x ∈ Set.Icc lo hi, |x - s| < ρ := by
      intro x hx
      rw [abs_lt] at hys ⊢
      have h1 : lo ≤ x := hx.1
      have h2 : x ≤ hi := hx.2
      have h3 : s - ρ / 2 < lo := lt_min (by linarith) (by linarith)
      have h4 : hi < s + ρ / 2 := max_lt (by linarith) (by linarith)
      constructor <;> linarith
    have hnoZ₀ : ∀ x ∈ Set.Icc lo hi, x ∉ Z₀ := by
      intro x hx hxZ
      have := hfar s hs x hxZ
      have := hwin' x hx
      rw [abs_sub_comm] at this
      linarith
    have hE : ∀ e ∈ endpts I, e ∉ Set.Icc lo hi := fun e he hx =>
      hnoZ₀ e hx (by rw [hZ₀def]; exact Finset.mem_union_left _ (Finset.mem_union_right _ he))
    have hyIcc : (y : ℝ) / n ∈ Set.Icc lo hi := ⟨min_le_left _ _, le_max_left _ _⟩
    have hnoS := no_S_of_no_endpts (I := I) hyIcc (by rw [← hSI]; exact hyS) hE
    have hlo0 : 0 ≤ lo := by
      have h0 := hfar s hs 0
        (by rw [hZ₀def]; exact Finset.mem_union_right _ (Finset.mem_insert_self _ _))
      have hs0 := hsΛ.1.1
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - 0)] at h0
      have := hwin' lo ⟨le_rfl, hlohi⟩
      rw [abs_lt] at this; linarith
    have hhic : hi ≤ c₀ := by
      have h0 := hfar s hs c₀ (by
        rw [hZ₀def]
        exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      have hs0 := hsΛ.1.2
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ c₀ - s)] at h0
      have := hwin' hi ⟨hlohi, le_rfl⟩
      rw [abs_lt] at this; linarith
    have hall : ∀ x ∈ Set.Icc lo hi, x ∉ S ∧ x ∉ (Z : Set ℝ) := by
      intro x hx
      refine ⟨by rw [hSI]; exact hnoS x hx, fun hxZ => hnoZ₀ x hx ?_⟩
      rw [hZ₀def]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_coe.1 hxZ))
    have hβeq := hβZ lo hi hlo0 hlohi hhic hall
    have hsIcc : s ∈ Set.Icc lo hi := ⟨min_le_right _ _, le_max_right _ _⟩
    refine ⟨fun hsS => (hall s hsIcc).1 hsS, ?_⟩
    rcases le_total ((y : ℝ) / n) s with h | h
    · have e1 : lo = (y : ℝ) / n := min_eq_left h
      have e2 : hi = s := max_eq_right h
      rw [e1, e2] at hβeq; exact hβeq
    · have e1 : lo = s := min_eq_right h
      have e2 : hi = (y : ℝ) / n := max_eq_left h
      rw [e1, e2] at hβeq; exact hβeq.symm
  -- the counted chords and the choice of windows
  set Fσ := (longCross R S β n η N).filter (fun e => e.2 = σ) with hFσ
  have hFmem : ∀ e ∈ Fσ, e.2 = σ ∧ e.1 < N ∧ σ ∈ R e.1 ∧ ∃ x, IsChord R σ x e.1 ∧
      η * n ≤ (e.1 : ℝ) - x ∧ (x : ℝ) / n ∉ S ∧ (e.1 : ℝ) / n ∉ S ∧
        β ((x : ℝ) / n) ≠ β ((e.1 : ℝ) / n) := by
    intro e he
    rw [hFσ, Finset.mem_filter] at he
    obtain ⟨he1, he2⟩ := he
    obtain ⟨z, τ⟩ := e
    simp only at he2
    subst he2
    rw [mem_longCross] at he1
    exact ⟨rfl, he1⟩
  choose! src hsrc using fun e (he : e ∈ Fσ) => (hFmem e he).2.2.2
  choose! ctr hctr using fun (y : ℕ) (h : σ ∈ R y ∧ y < N) => hvisit y h.1 h.2
  -- the map
  let f : ℕ × ℤ → ℝ × ℝ := fun e => (ctr (src e), ctr e.1)
  have hdata : ∀ e ∈ Fσ, src e < e.1 ∧ σ ∈ R (src e) ∧ σ ∈ R e.1 ∧ e.1 < N ∧
      ctr (src e) ∈ ΛF ∧ |((src e : ℕ) : ℝ) / n - ctr (src e)| < ρ / 2 ∧
      ctr e.1 ∈ ΛF ∧ |((e.1 : ℕ) : ℝ) / n - ctr e.1| < ρ / 2 := by
    intro e he
    obtain ⟨_, hzN, hzR, _⟩ := hFmem e he
    obtain ⟨hch, _, _, _, _⟩ := hsrc e he
    have hxz : src e < e.1 := by have := hch.1; omega
    have hxN : src e < N := lt_trans hxz hzN
    obtain ⟨h1, h2⟩ := hctr (src e) ⟨hch.2.1, hxN⟩
    obtain ⟨h3, h4⟩ := hctr e.1 ⟨hzR, hzN⟩
    exact ⟨hxz, hch.2.1, hzR, hzN, h1, h2, h3, h4⟩
  -- ordered windows
  have hord : ∀ e ∈ Fσ, ctr (src e) < ctr e.1 := by
    intro e he
    obtain ⟨hxz, -, -, -, hs₁, hx₁, hs₂, hz₂⟩ := hdata e he
    obtain ⟨-, hgap, -, -, -⟩ := hsrc e he
    rcases lt_trichotomy (ctr (src e)) (ctr e.1) with h | h | h
    · exact h
    · exfalso
      rw [h] at hx₁
      have : |((e.1 : ℕ) : ℝ) / n - ((src e : ℕ) : ℝ) / n| < ρ := by
        calc |((e.1 : ℕ) : ℝ) / n - ((src e : ℕ) : ℝ) / n|
            = |(((e.1 : ℕ) : ℝ) / n - ctr e.1) - (((src e : ℕ) : ℝ) / n - ctr e.1)| := by
              ring_nf
          _ ≤ |((e.1 : ℕ) : ℝ) / n - ctr e.1| + |((src e : ℕ) : ℝ) / n - ctr e.1| := abs_sub _ _
          _ < ρ := by linarith
      rw [← sub_div, abs_div, abs_of_pos hnpos, div_lt_iff₀ hnpos] at this
      have h' := le_abs_self (((e.1 : ℕ) : ℝ) - ((src e : ℕ) : ℝ))
      nlinarith
    · exfalso
      have := hsep _ hs₁ _ hs₂ (ne_of_gt h)
      rw [abs_of_pos (by linarith)] at this
      rw [abs_lt] at hx₁ hz₂
      have : ((e.1 : ℕ) : ℝ) / n < ((src e : ℕ) : ℝ) / n := by linarith
      rw [div_lt_div_iff_of_pos_right hnpos] at this
      have : (e.1 : ℝ) < (src e : ℝ) := by exact_mod_cast this
      have : e.1 < src e := by exact_mod_cast this
      omega
  have hmaps : ∀ e ∈ (Fσ : Set (ℕ × ℤ)), f e ∈ crossPairs P S β c₀ p := by
    intro e he
    have he' : e ∈ Fσ := he
    obtain ⟨hxz, hxR, hzR, hzN, hs₁, hx₁, hs₂, hz₂⟩ := hdata e he'
    obtain ⟨hch, hgap, hxS, hzS, hβne⟩ := hsrc e he'
    have hlt := hord e he'
    obtain ⟨hs₁S, hβ₁⟩ := hinherit (src e) _ hs₁ hx₁ hxS
    obtain ⟨hs₂S, hβ₂⟩ := hinherit e.1 _ hs₂ hz₂ hzS
    refine ⟨⟨(hmemF _).1 hs₁, (hmemF _).1 hs₂, hlt, ?_⟩, hs₁S, hs₂S, ?_⟩
    · -- no point of `Λ` strictly between
      rintro s'' hs''Λ ⟨h1, h2⟩
      have hs'' := (hmemF s'').2 hs''Λ
      obtain ⟨y, hyR, hy⟩ := hwin s'' hs''
      have e1 := hsep _ hs₁ _ hs'' (ne_of_lt h1)
      have e2 := hsep _ hs'' _ hs₂ (ne_of_lt h2)
      rw [abs_of_neg (by linarith)] at e1 e2
      rw [abs_lt] at hx₁ hz₂ hy
      have hxy : ((src e : ℕ) : ℝ) / n < (y : ℝ) / n := by linarith
      have hyz : (y : ℝ) / n < ((e.1 : ℕ) : ℝ) / n := by linarith
      rw [div_lt_div_iff_of_pos_right hnpos] at hxy hyz
      have hxy' : src e < y := by exact_mod_cast hxy
      have hyz' : y < e.1 := by exact_mod_cast hyz
      exact hch.2.2.2 y hxy' hyz' hyR
    · simp only [f]
      rw [← hβ₁, ← hβ₂]; exact hβne
  have hinj : Set.InjOn f (Fσ : Set (ℕ × ℤ)) := by
    intro e he e' he' hfe
    have hE : e ∈ Fσ := he
    have hE' : e' ∈ Fσ := he'
    simp only [f, Prod.mk.injEq] at hfe
    obtain ⟨hf1, hf2⟩ := hfe
    have h2 : e.2 = e'.2 := by rw [(hFmem e hE).1, (hFmem e' hE').1]
    suffices h1 : e.1 = e'.1 from Prod.ext h1 h2
    by_contra hne
    -- WLOG the first target is earlier
    have key : ∀ a ∈ Fσ, ∀ b ∈ Fσ, ctr (src a) = ctr (src b) → ctr a.1 = ctr b.1 →
        a.1 < b.1 → False := by
      intro a ha b hb hs1 hs2 hab
      obtain ⟨-, -, haR, -, -, -, hsa, hza⟩ := hdata a ha
      obtain ⟨hxb, -, -, -, hsxb, hxb', -, -⟩ := hdata b hb
      obtain ⟨hchb, -, -, -, -⟩ := hsrc b hb
      -- `a.1` is a visit before `b.1`, so it is at most the source of `b`
      have hle : a.1 ≤ src b := by
        by_contra hc; push Not at hc
        exact hchb.2.2.2 a.1 hc hab haR
      have hlt := hord b hb
      have hsp := hsep _ hsxb _ (by rw [← hs2]; exact hsa) (ne_of_lt hlt)
      rw [abs_of_neg (by linarith)] at hsp
      rw [abs_lt] at hza hxb'
      rw [hs2] at hza
      have : ((src b : ℕ) : ℝ) / n < ((a.1 : ℕ) : ℝ) / n := by linarith
      rw [div_lt_div_iff_of_pos_right hnpos] at this
      have : src b < a.1 := by exact_mod_cast this
      omega
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key e hE e' hE' hf1 hf2 h
    · exact key e' hE' e hE hf1.symm hf2.symm h
  have hfinpairs : (crossPairs P S β c₀ p).Finite := by
    apply (hfin.prod hfin).subset
    rintro ⟨s, s'⟩ ⟨⟨hs, hs', -⟩, -⟩
    exact ⟨hs, hs'⟩
  calc Fσ.card = (Fσ : Set (ℕ × ℤ)).ncard := (Set.ncard_coe_finset Fσ).symm
    _ ≤ (crossPairs P S β c₀ p).ncard := Set.ncard_le_ncard_of_injOn f hmaps hinj hfinpairs

end Lemma4

/-! ### Counting by levels -/

/-- The level function `g_n`: the number of long crossing chords of block `⌊p n⌋`, written as a
sum of indicators of the intervals `[σ/n, (σ+1)/n)`. -/
noncomputable def gfun (F : Finset (ℕ × ℤ)) (n : ℕ) (p : ℝ) : ℝ≥0∞ :=
  ∑ e ∈ F, (Set.Ico ((e.2 : ℝ) / n) (((e.2 : ℝ) + 1) / n)).indicator (fun _ => (1 : ℝ≥0∞)) p

theorem measurable_gfun (F : Finset (ℕ × ℤ)) (n : ℕ) : Measurable (gfun F n) :=
  Finset.measurable_sum _ (fun _ _ => measurable_const.indicator measurableSet_Ico)

theorem mem_Ico_div_iff {σ : ℤ} {n : ℕ} (hn : 0 < n) {p : ℝ} :
    p ∈ Set.Ico ((σ : ℝ) / n) (((σ : ℝ) + 1) / n) ↔ ⌊p * n⌋ = σ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Set.mem_Ico, Int.floor_eq_iff, div_le_iff₀ hn', lt_div_iff₀ hn']

theorem gfun_eq (F : Finset (ℕ × ℤ)) {n : ℕ} (hn : 0 < n) (p : ℝ) :
    gfun F n p = ((F.filter (fun e => e.2 = ⌊p * n⌋)).card : ℝ≥0∞) := by
  classical
  unfold gfun
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro e _
  rw [Set.indicator_apply]
  by_cases h : p ∈ Set.Ico ((e.2 : ℝ) / n) (((e.2 : ℝ) + 1) / n)
  · rw [ite_eq_left h, ite_eq_left ((mem_Ico_div_iff hn).1 h).symm]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((mem_Ico_div_iff hn).2 h'.symm))]

theorem lintegral_gfun (F : Finset (ℕ × ℤ)) {n : ℕ} (hn : 0 < n) :
    ∫⁻ p, gfun F n p = (F.card : ℝ≥0∞) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold gfun
  rw [lintegral_finsetSum _ (fun _ _ => measurable_const.indicator measurableSet_Ico)]
  have h1 : ∀ e ∈ F, ∫⁻ p, (Set.Ico ((e.2 : ℝ) / n) (((e.2 : ℝ) + 1) / n)).indicator
      (fun _ => (1 : ℝ≥0∞)) p = (n : ℝ≥0∞)⁻¹ := by
    intro e _
    rw [lintegral_indicator_const measurableSet_Ico, one_mul, Real.volume_Ico,
      show ((e.2 : ℝ) + 1) / n - (e.2 : ℝ) / n = (n : ℝ)⁻¹ by field_simp; ring,
      ENNReal.ofReal_inv_of_pos hn', ENNReal.ofReal_natCast]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- **Per-block bound.** The long chords of one block have pairwise disjoint gaps of length
`≥ η n` inside `[0, N)`, so there are at most `c₀ / η` of them. -/
theorem blockCount_le {R : ℕ → Finset ℤ} {S : Set ℝ} {β : ℝ → ℕ} {n N : ℕ} {η c₀ : ℝ}
    (hη : 0 < η) (hn : 0 < n) (hN : (N : ℝ) ≤ c₀ * n) (σ : ℤ) :
    (((longCross R S β n η N).filter (fun e => e.2 = σ)).card : ℝ) ≤ c₀ / η := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set T := (longCross R S β n η N).filter (fun e => e.2 = σ) with hTdef
  have hT : ∀ e ∈ T, e.2 = σ ∧ e.1 < N ∧ σ ∈ R e.1 ∧ ∃ x, IsChord R σ x e.1 ∧
      η * n ≤ (e.1 : ℝ) - x := by
    intro e he
    rw [hTdef, Finset.mem_filter] at he
    obtain ⟨he1, he2⟩ := he
    obtain ⟨z, τ⟩ := e
    simp only at he2
    subst he2
    rw [mem_longCross] at he1
    obtain ⟨h1, h2, x, hx, hg, -⟩ := he1
    exact ⟨rfl, h1, h2, x, hx, hg⟩
  choose! src hsrc using fun e (he : e ∈ T) => (hT e he).2.2.2
  have hdisj : (T : Set (ℕ × ℤ)).PairwiseDisjoint (fun e => Finset.Ioc (src e) e.1) := by
    intro e he e' he' hne
    have hE : e ∈ T := he
    have hE' : e' ∈ T := he'
    have h1 : e.1 ≠ e'.1 := by
      intro h; apply hne; exact Prod.ext h (by rw [(hT e hE).1, (hT e' hE').1])
    -- the earlier target is at most the later chord's source
    have key : ∀ a ∈ T, ∀ b ∈ T, a.1 < b.1 →
        Disjoint (Finset.Ioc (src a) a.1) (Finset.Ioc (src b) b.1) := by
      intro a ha b hb hab
      have hle : a.1 ≤ src b := by
        by_contra hc; push Not at hc
        exact (hsrc b hb).1.2.2.2 a.1 hc hab (hT a ha).2.2.1
      rw [Finset.disjoint_left]
      intro y hy hy'
      rw [Finset.mem_Ioc] at hy hy'
      omega
    rcases Nat.lt_or_gt_of_ne h1 with h | h
    · exact key e hE e' hE' h
    · exact (key e' hE' e hE h).symm
  have hsub : T.biUnion (fun e => Finset.Ioc (src e) e.1) ⊆ Finset.range N := by
    intro y hy
    rw [Finset.mem_biUnion] at hy
    obtain ⟨e, he, hy⟩ := hy
    rw [Finset.mem_Ioc] at hy
    rw [Finset.mem_range]
    have := (hT e he).2.1
    omega
  have hcard := Finset.card_biUnion hdisj
  have hle1 : ((T.biUnion (fun e => Finset.Ioc (src e) e.1)).card : ℝ) ≤ N := by
    exact_mod_cast Finset.card_le_card hsub |>.trans (by rw [Finset.card_range])
  have hle2 : (T.card : ℝ) * (η * n) ≤ ∑ e ∈ T, ((Finset.Ioc (src e) e.1).card : ℝ) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro e he
    rw [Nat.card_Ioc]
    have hlt : src e < e.1 := by have := (hsrc e he).1.1; omega
    rw [Nat.cast_sub hlt.le]
    exact (hsrc e he).2
  rw [hcard] at hle1
  push_cast at hle1
  rw [le_div_iff₀ hη]
  have : (T.card : ℝ) * (η * n) ≤ c₀ * n := by linarith
  have : (T.card : ℝ) * η * n ≤ c₀ * n := by linarith
  exact le_of_mul_le_mul_right this hn'

/-! ### The limsup bound -/

theorem levelChords_limsup_le {c₀ η : ℝ} (hη : 0 < η) {D : ℕ} {P : ℝ → ℝ}
    (hP : LipschitzOnWith 1 P (Set.Icc 0 c₀)) {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {W : ℕ → ℕ → ℤ} {R : ℕ → ℕ → Finset ℤ} {N : ℕ → ℕ}
    (hN : ∀ᶠ i in atTop, (N i : ℝ) ≤ c₀ * ns i)
    (hV1 : ∀ᶠ i in atTop, ∀ y σ, σ ∈ R i y → |W i y - σ| ≤ D)
    (hV2 : ∀ᶠ i in atTop, ∀ y₁ y₂ σ, y₁ ≤ y₂ →
      (W i y₁ < σ ∧ σ < W i y₂ ∨ W i y₂ < σ ∧ σ < W i y₁) → ∃ y, y₁ ≤ y ∧ y ≤ y₂ ∧ σ ∈ R i y)
    (hconv : TendstoUniformlyOn (fun i (u : ℝ) => (W i ⌊u * ns i⌋₊ : ℝ) / ns i) P atTop
      (Set.Icc 0 c₀))
    {S : Set ℝ} (hS : FinUnionIcc S) {β : ℝ → ℕ} (hβ : PiecewiseConstOn β S c₀) :
    limsup (fun i => ((longCross (R i) S β (ns i) η (N i)).card : ℝ≥0∞) / ns i) atTop ≤
      ∫⁻ p, levelCross P S β c₀ p := by
  classical
  obtain ⟨I, hSI⟩ := hS
  obtain ⟨Z, hβZ⟩ := hβ
  set F := fun i => longCross (R i) S β (ns i) η (N i) with hF
  have hn1 : ∀ᶠ i in atTop, 1 ≤ ns i := hns.eventually_ge_atTop 1
  -- `c₀ ≥ 0`
  have hc₀ : 0 ≤ c₀ := by
    by_contra hc
    push Not at hc
    obtain ⟨i, hi1, hi2⟩ := (hN.and hn1).exists
    have : (1 : ℝ) ≤ ns i := by exact_mod_cast hi2
    have : (0 : ℝ) ≤ N i := Nat.cast_nonneg _
    nlinarith
  have hclose1 : ∀ᶠ i in atTop, ∀ u ∈ Set.Icc 0 c₀,
      dist (P u) ((W i ⌊u * ns i⌋₊ : ℝ) / ns i) < 1 :=
    Metric.tendstoUniformlyOn_iff.1 hconv 1 one_pos
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 (hN.and (hV1.and (hn1.and hclose1)))
  set A : ℝ := |P 0| + c₀ + D + 2 with hA
  set G : ℝ → ℝ≥0∞ := (Set.Icc (-A) A).indicator (fun _ => ENNReal.ofReal (c₀ / η + 1))
    with hG
  -- domination on the tail
  have hbound : ∀ j p, gfun (F (j + i₀)) (ns (j + i₀)) p ≤ G p := by
    intro j p
    obtain ⟨hNi, hV1i, hni, hcli⟩ := hi₀ (j + i₀) (Nat.le_add_left _ _)
    set n := ns (j + i₀)
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hni
    rw [gfun_eq _ hni]
    set σ := ⌊p * n⌋
    rcases Nat.eq_zero_or_pos ((F (j + i₀)).filter (fun e => e.2 = σ)).card with hz | hz
    · rw [hz]; simp
    obtain ⟨⟨z, τ⟩, he⟩ := Finset.card_pos.1 hz
    obtain ⟨he1, rfl⟩ := Finset.mem_filter.1 he
    obtain ⟨hzN, hzR, -⟩ := mem_longCross.1 he1
    -- the block `σ` is within `D` of `W z`, and `|W z| ≤ (|P 0| + c₀ + 1) n`
    have hu : (z : ℝ) / n ∈ Set.Icc 0 c₀ := ⟨by positivity,
      (div_le_iff₀ (by linarith)).2 (le_trans (by exact_mod_cast hzN.le) hNi)⟩
    have hd := hcli _ hu
    rw [div_mul_cancel₀ _ (by linarith : (n : ℝ) ≠ 0), Nat.floor_natCast, Real.dist_eq,
      abs_lt] at hd
    have hP0 := hP.dist_le_mul _ hu 0 ⟨le_rfl, hc₀⟩
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, sub_zero, abs_of_nonneg hu.1,
      abs_le] at hP0
    have hw : |(W (j + i₀) z : ℝ) / n| ≤ |P 0| + c₀ + 1 := by
      rw [abs_le]; constructor <;> linarith [neg_abs_le (P 0), le_abs_self (P 0), hu.2]
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < n), div_le_iff₀ (by linarith), abs_le] at hw
    have hW : |(W (j + i₀) z : ℝ) - σ| ≤ D := by exact_mod_cast hV1i z _ hzR
    rw [abs_le] at hW
    have hσ1 : (σ : ℝ) ≤ p * n := Int.floor_le _
    have hσ2 : p * n < σ + 1 := Int.lt_floor_add_one _
    have hDn : (D : ℝ) + 1 ≤ (D + 1) * n := by nlinarith
    have hpA : p ∈ Set.Icc (-A) A := by
      constructor
      · exact le_of_mul_le_mul_right (by rw [hA]; linarith) (by linarith : (0 : ℝ) < n)
      · exact le_of_mul_le_mul_right (by rw [hA]; linarith) (by linarith : (0 : ℝ) < n)
    have hcnt := blockCount_le (R := R (j + i₀)) (S := S) (β := β) hη hni hNi σ
    rw [hG, Set.indicator_of_mem hpA, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- the integrals
  have hint : ∀ j, ∫⁻ p, gfun (F (j + i₀)) (ns (j + i₀)) p =
      ((F (j + i₀)).card : ℝ≥0∞) / ns (j + i₀) := fun j =>
    lintegral_gfun _ (hi₀ (j + i₀) (Nat.le_add_left _ _)).2.2.1
  -- good levels form a conull set
  set Z₀ : Finset ℝ := Z ∪ endpts I ∪ {0, c₀} with hZ₀
  have hgood : ∀ᵐ p, (levelSet P c₀ p).Finite ∧
      p ∉ {p | ∃ s, P s = p ∧ (IsLocalMin P s ∨ IsLocalMax P s)} ∧ p ∉ P '' (Z₀ : Set ℝ) := by
    have h1 := ae_finite_levelSet hP
    have h2 := (countable_localExtr_values P).ae_notMem volume
    have h3 := ((Z₀.finite_toSet.image P).countable).ae_notMem volume
    filter_upwards [h1, h2, h3] with p hp1 hp2 hp3
    exact ⟨hp1, hp2, hp3⟩
  have hae : ∀ᵐ p, limsup (fun j => gfun (F (j + i₀)) (ns (j + i₀)) p) atTop ≤
      levelCross P S β c₀ p := by
    filter_upwards [hgood] with p ⟨hfin, hext, hZp⟩
    have hext' : ∀ s ∈ levelSet P c₀ p, ¬IsLocalMin P s ∧ ¬IsLocalMax P s := by
      intro s hs
      constructor
      · intro hmin; exact hext ⟨s, hs.2, Or.inl hmin⟩
      · intro hmax; exact hext ⟨s, hs.2, Or.inr hmax⟩
    have hZ₀' : ∀ s ∈ levelSet P c₀ p, s ∉ (Z ∪ endpts I ∪ {0, c₀} : Finset ℝ) := by
      intro s hs hsZ
      exact hZp ⟨s, hsZ, hs.2⟩
    obtain ⟨ε, hε, n₀, hlem⟩ := count_le_crossPairs (D := D) hη hP hSI hβZ hfin hext' hZ₀'
    have hcloseε : ∀ᶠ i in atTop, ∀ u ∈ Set.Icc 0 c₀,
        dist (P u) ((W i ⌊u * ns i⌋₊ : ℝ) / ns i) < ε :=
      Metric.tendstoUniformlyOn_iff.1 hconv ε hε
    have hev : ∀ᶠ i in atTop, gfun (F i) (ns i) p ≤ levelCross P S β c₀ p := by
      filter_upwards [hN, hV1, hV2, hcloseε, hns.eventually_ge_atTop (max n₀ 1)] with
        i hNi hV1i hV2i hcli hni
      rw [gfun_eq _ (lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hni)), levelCross,
        ite_eq_left hfin]
      exact_mod_cast hlem (ns i) (W i) (R i) (N i) (le_trans (le_max_left _ _) hni) hNi hV1i
        hV2i hcli
    have hev' := (tendsto_add_atTop_nat i₀).eventually hev
    exact limsup_le_of_le (by isBoundedDefault) hev'
  have hGfin : ∫⁻ p, G p ≠ ∞ := by
    rw [hG, lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  calc limsup (fun i => ((F i).card : ℝ≥0∞) / ns i) atTop
      = limsup (fun j => ((F (j + i₀)).card : ℝ≥0∞) / ns (j + i₀)) atTop :=
        (limsup_nat_add (fun i => ((F i).card : ℝ≥0∞) / ns i) i₀).symm
    _ = limsup (fun j => ∫⁻ p, gfun (F (j + i₀)) (ns (j + i₀)) p) atTop := by
        simp_rw [hint]
    _ ≤ ∫⁻ p, limsup (fun j => gfun (F (j + i₀)) (ns (j + i₀)) p) atTop :=
        limsup_lintegral_le G (fun j => measurable_gfun _ _)
          (fun j => ae_of_all _ (hbound j)) hGfin
    _ ≤ ∫⁻ p, levelCross P S β c₀ p := lintegral_mono_ae hae

end Transpose.Tape.Impl

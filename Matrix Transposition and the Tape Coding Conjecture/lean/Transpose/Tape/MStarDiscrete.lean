import Transpose.Tape.MStarTM
import Transpose.Tape.Corollaries

/-!
# Theorem M*, the discrete part: the chord split, slot counting and the slot labelling

* `crossChords_split`: chords crossing labels are short (each charged to a label change), touch
  `S`, or are long label-crossing chords off `S`.
* Slot counting: slots whose interval `[y/n, (y+1)/n]` meets a finite set of breakpoints are few
  (`bad_count`); the other slots of a set `A` number at most `n · vol(A)` (`good_count`).
* The M* slot labelling `mstarLabel` (labels `2β(y/n)` off `S`, and `2⌊(y/n)/θ⌋ + 1` on `S`): its
  label changes and class sizes.

The per-size inequality from Discrete Isoperimetry is `mstar_discrete_walk` (`MStarWalk.lean`), for
any family of walks satisfying the cut inequality.
-/

namespace Transpose.Tape.Impl

open Transpose MeasureTheory Filter Topology

open scoped ENNReal

/-! ### The chord split -/

open Classical in
theorem crossChords_split {R : ℕ → Finset ℤ}
    (hsrc : ∀ {σ σ' : ℤ} {x z z' : ℕ}, IsChord R σ x z → IsChord R σ' x z' → σ = σ' ∧ z = z')
    (htgt : ∀ {σ σ' : ℤ} {x x' z : ℕ}, IsChord R σ x z → IsChord R σ' x' z → σ = σ' ∧ x = x')
    (lab : ℕ → ℕ) (N n : ℕ) (η : ℝ) (S : Set ℝ) (β : ℝ → ℕ)
    (hlab : ∀ y y' : ℕ, (y : ℝ) / n ∉ S → (y' : ℝ) / n ∉ S → lab y ≠ lab y' →
      β ((y : ℝ) / n) ≠ β ((y' : ℝ) / n)) :
    (crossChords R lab N).card ≤ labelChanges lab N * (⌈η * n⌉₊ + 1) +
      2 * ((Finset.range N).filter (fun y : ℕ => (y : ℝ) / n ∈ S)).card +
      (longCross R S β n η N).card := by
  classical
  set C := crossChords R lab N with hC
  have hCmem : ∀ e ∈ C, e.1 < N ∧ e.2 ∈ R e.1 ∧ ∃ x, lab x ≠ lab e.1 ∧ IsChord R e.2 x e.1 := by
    intro e he
    obtain ⟨z, σ⟩ := e
    exact mem_crossChords.1 he
  choose! src hsrc1 hsrc2 using fun e (he : e ∈ C) => (hCmem e he).2.2
  -- the source determines the chord
  have hinj_src : Set.InjOn src (C : Set (ℕ × ℤ)) := by
    intro e he e' he' h
    have h1 := hsrc2 e he
    have h2 := hsrc2 e' he'
    rw [h] at h1
    obtain ⟨hσ, hz⟩ := hsrc h1 h2
    exact Prod.ext hz hσ
  -- the target determines the chord
  have hinj_tgt : Set.InjOn Prod.fst (C : Set (ℕ × ℤ)) := by
    intro e he e' he' h
    have h1 := hsrc2 e he
    have h2 := hsrc2 e' he'
    rw [h] at h1
    obtain ⟨hσ, -⟩ := htgt h1 h2
    exact Prod.ext h hσ
  have hsrc_lt : ∀ e ∈ C, src e < e.1 := fun e he => by
    have := (hsrc2 e he).1; omega
  set Cs := C.filter (fun e => (e.1 : ℝ) - src e < η * n) with hCs
  set CS := C.filter (fun e => (src e : ℝ) / n ∈ S ∨ (e.1 : ℝ) / n ∈ S) with hCS
  set YS := (Finset.range N).filter (fun y : ℕ => (y : ℝ) / n ∈ S) with hYS
  -- every crossing chord is short, touches `S`, or is long off `S`
  have hcover : C ⊆ Cs ∪ CS ∪ longCross R S β n η N := by
    intro e he
    by_cases h1 : (e.1 : ℝ) - src e < η * n
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, h1⟩))
    by_cases h2 : (src e : ℝ) / n ∈ S ∨ (e.1 : ℝ) / n ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨he, h2⟩))
    apply Finset.mem_union_right
    push Not at h1 h2
    obtain ⟨hzN, hzR, -⟩ := hCmem e he
    obtain ⟨z, σ⟩ := e
    rw [mem_longCross]
    exact ⟨hzN, hzR, src (z, σ), hsrc2 _ he, h1, h2.1, h2.2,
      hlab _ _ h2.1 h2.2 (hsrc1 _ he)⟩
  -- short chords: their sources lie just before label changes
  set CH := (Finset.range N).filter (fun y => 1 ≤ y ∧ lab y ≠ lab (y - 1)) with hCH
  have hCHcard : CH.card = labelChanges lab N := rfl
  have hshort : Cs.card ≤ labelChanges lab N * (⌈η * n⌉₊ + 1) := by
    have hsub : Cs.image src ⊆ CH.biUnion (fun y => Finset.Ico (y - ⌈η * n⌉₊) y) := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
      rw [hCs, Finset.mem_filter] at he
      obtain ⟨heC, hgap⟩ := he
      obtain ⟨y, hy1, hy2, hy3⟩ := label_change_between lab (hsrc_lt e heC) (hsrc1 e heC)
      have hyN : y < N := lt_of_le_of_lt hy2 (hCmem e heC).1
      rw [Finset.mem_biUnion]
      refine ⟨y, Finset.mem_filter.2 ⟨Finset.mem_range.2 hyN, by omega, hy3⟩, ?_⟩
      rw [Finset.mem_Ico]
      refine ⟨?_, hy1⟩
      have h1 : ((y - src e : ℕ) : ℝ) < ⌈η * n⌉₊ := by
        rw [Nat.cast_sub hy1.le]
        have : (y : ℝ) ≤ e.1 := by exact_mod_cast hy2
        exact lt_of_lt_of_le (by linarith) (Nat.le_ceil _)
      have h2 : y - src e < ⌈η * n⌉₊ := by exact_mod_cast h1
      omega
    calc Cs.card = (Cs.image src).card :=
          (Finset.card_image_of_injOn (hinj_src.mono (Finset.coe_subset.2
            (Finset.filter_subset _ _)))).symm
      _ ≤ (CH.biUnion (fun y => Finset.Ico (y - ⌈η * n⌉₊) y)).card := Finset.card_le_card hsub
      _ ≤ ∑ y ∈ CH, (Finset.Ico (y - ⌈η * n⌉₊) y).card := Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ CH, (⌈η * n⌉₊ + 1) := Finset.sum_le_sum (fun y _ => by
          rw [Nat.card_Ico]; omega)
      _ = labelChanges lab N * (⌈η * n⌉₊ + 1) := by
          rw [Finset.sum_const, smul_eq_mul, hCHcard]
  -- chords touching `S`
  have hS : CS.card ≤ 2 * YS.card := by
    have hsub : CS ⊆ C.filter (fun e => (src e : ℝ) / n ∈ S) ∪
        C.filter (fun e => (e.1 : ℝ) / n ∈ S) := by
      intro e he
      rw [hCS, Finset.mem_filter] at he
      rcases he.2 with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he.1, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨he.1, h⟩)
    have h1 : (C.filter (fun e => (src e : ℝ) / n ∈ S)).card ≤ YS.card := by
      apply Finset.card_le_card_of_injOn src
      · intro e he
        rw [Finset.mem_coe, Finset.mem_filter] at he
        rw [Finset.mem_coe, hYS, Finset.mem_filter, Finset.mem_range]
        exact ⟨lt_trans (hsrc_lt e he.1) (hCmem e he.1).1, he.2⟩
      · exact hinj_src.mono (Finset.coe_subset.2 (Finset.filter_subset _ _))
    have h2 : (C.filter (fun e => (e.1 : ℝ) / n ∈ S)).card ≤ YS.card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro e he
        rw [Finset.mem_coe, Finset.mem_filter] at he
        rw [Finset.mem_coe, hYS, Finset.mem_filter, Finset.mem_range]
        exact ⟨(hCmem e he.1).1, he.2⟩
      · exact hinj_tgt.mono (Finset.coe_subset.2 (Finset.filter_subset _ _))
    calc CS.card ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ YS.card + YS.card := Nat.add_le_add h1 h2
      _ = 2 * YS.card := by ring
  calc C.card ≤ (Cs ∪ CS ∪ longCross R S β n η N).card := Finset.card_le_card hcover
    _ ≤ (Cs ∪ CS).card + (longCross R S β n η N).card := Finset.card_union_le _ _
    _ ≤ Cs.card + CS.card + (longCross R S β n η N).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ _ := by omega

/-! ### Slot counting -/

/-- A point `z` lies in the closed interval `[y/n, (y+1)/n]` of at most two slots `y`. -/
theorem slot_near_point {n : ℕ} (hn : 0 < n) {z : ℝ} {y : ℕ} (h1 : (y : ℝ) / n ≤ z)
    (h2 : z ≤ ((y : ℝ) + 1) / n) : y ∈ ({⌊z * n⌋₊ - 1, ⌊z * n⌋₊} : Finset ℕ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn'] at h1
  rw [le_div_iff₀ hn'] at h2
  have hz : 0 ≤ z * n := le_trans (Nat.cast_nonneg _) h1
  have e1 : y ≤ ⌊z * n⌋₊ := Nat.le_floor h1
  have e2 : ⌊z * n⌋₊ ≤ y + 1 := by
    have : (⌊z * n⌋₊ : ℝ) ≤ y + 1 := le_trans (Nat.floor_le hz) h2
    exact_mod_cast this
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- **Bad slots.** The slots whose closed interval `[y/n, (y+1)/n]` contains a point of a finite
set `Z` number at most `2 |Z|`. -/
theorem bad_count {n : ℕ} (hn : 0 < n) (Z : Finset ℝ) (N : ℕ) :
    ((Finset.range N).filter (fun y : ℕ => ∃ z ∈ Z, (y : ℝ) / n ≤ z ∧ z ≤ ((y : ℝ) + 1) / n)).card
      ≤ 2 * Z.card := by
  classical
  calc _ ≤ (Z.biUnion (fun z => ({⌊z * n⌋₊ - 1, ⌊z * n⌋₊} : Finset ℕ))).card := by
        apply Finset.card_le_card
        intro y hy
        rw [Finset.mem_filter] at hy
        obtain ⟨-, z, hz, h1, h2⟩ := hy
        exact Finset.mem_biUnion.2 ⟨z, hz, slot_near_point hn h1 h2⟩
    _ ≤ ∑ z ∈ Z, ({⌊z * n⌋₊ - 1, ⌊z * n⌋₊} : Finset ℕ).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ Z, 2 := Finset.sum_le_sum (fun _ _ => Finset.card_le_two)
    _ = 2 * Z.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Good slots.** Slots whose interval `[y/n, (y+1)/n)` lies in `A` number at most `n · vol(A)`. -/
theorem good_count {n : ℕ} (hn : 0 < n) (Y : Finset ℕ) (A : Set ℝ)
    (hY : ∀ y ∈ Y, Set.Ico ((y : ℝ) / n) (((y : ℝ) + 1) / n) ⊆ A) :
    (Y.card : ℝ≥0∞) ≤ n * volume A := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hdisj : (Y : Set ℕ).PairwiseDisjoint
      (fun y : ℕ => Set.Ico ((y : ℝ) / n) (((y : ℝ) + 1) / n)) := by
    intro y _ y' _ hne
    rw [Function.onFun, Set.disjoint_iff]
    rintro x ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    apply hne
    rw [div_le_iff₀ hn'] at h1 h3
    rw [lt_div_iff₀ hn'] at h2 h4
    have hx : 0 ≤ x * n := le_trans (Nat.cast_nonneg _) h1
    have e1 := (Nat.floor_eq_iff hx).2 ⟨h1, h2⟩
    have e2 := (Nat.floor_eq_iff hx).2 ⟨h3, h4⟩
    rw [← e1, ← e2]
  have hvol : volume (⋃ y ∈ Y, Set.Ico ((y : ℝ) / n) (((y : ℝ) + 1) / n)) =
      Y.card * (n : ℝ≥0∞)⁻¹ := by
    rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_Ico)]
    have : ∀ y ∈ Y, volume (Set.Ico ((y : ℝ) / n) (((y : ℝ) + 1) / n)) = (n : ℝ≥0∞)⁻¹ := by
      intro y _
      rw [Real.volume_Ico, show ((y : ℝ) + 1) / n - (y : ℝ) / n = (n : ℝ)⁻¹ by field_simp; ring,
        ENNReal.ofReal_inv_of_pos hn', ENNReal.ofReal_natCast]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  have hle : (Y.card : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ ≤ volume A := by
    rw [← hvol]
    exact measure_mono (Set.iUnion₂_subset hY)
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  calc (Y.card : ℝ≥0∞) = n * ((Y.card : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) := by
        rw [mul_comm (Y.card : ℝ≥0∞), ← mul_assoc, ENNReal.mul_inv_cancel hn0
          (ENNReal.natCast_ne_top n), one_mul]
    _ ≤ n * volume A := by gcongr

/-! ### The M* slot labelling -/

open Classical in
/-- The M* slot labelling at size `n`: slot `y` gets `2 β(y/n)` if `y/n ∉ S`, and the fresh odd
label `2 ⌊(y/n)/θ⌋ + 1` if `y/n ∈ S` (the pieces of `S` of length `≤ θ`). -/
noncomputable def mstarLabel (S : Set ℝ) (β : ℝ → ℕ) (θ : ℝ) (n y : ℕ) : ℕ :=
  if (y : ℝ) / n ∈ S then 2 * ⌊(y : ℝ) / n / θ⌋₊ + 1 else 2 * β ((y : ℝ) / n)

theorem mstarLabel_off {S : Set ℝ} {β : ℝ → ℕ} {θ : ℝ} {n y : ℕ} (h : (y : ℝ) / n ∉ S) :
    mstarLabel S β θ n y = 2 * β ((y : ℝ) / n) := by
  classical
  unfold mstarLabel; rw [ite_eq_right h]

theorem mstarLabel_on {S : Set ℝ} {β : ℝ → ℕ} {θ : ℝ} {n y : ℕ} (h : (y : ℝ) / n ∈ S) :
    mstarLabel S β θ n y = 2 * ⌊(y : ℝ) / n / θ⌋₊ + 1 := by
  classical
  unfold mstarLabel; rw [ite_eq_left h]

theorem mstarLabel_hlab (S : Set ℝ) (β : ℝ → ℕ) (θ : ℝ) (n : ℕ) :
    ∀ y y' : ℕ, (y : ℝ) / n ∉ S → (y' : ℝ) / n ∉ S →
      mstarLabel S β θ n y ≠ mstarLabel S β θ n y' → β ((y : ℝ) / n) ≠ β ((y' : ℝ) / n) := by
  intro y y' h1 h2 hne heq
  rw [mstarLabel_off h1, mstarLabel_off h2, heq] at hne
  exact hne rfl

section Labelling

variable {c₀ θ : ℝ} {n N : ℕ} {S : Set ℝ} {I : Finset (ℝ × ℝ)} {β : ℝ → ℕ} {Z : Finset ℝ}

/-- The breakpoints of the M* labelling. -/
noncomputable def mstarBreaks (Z : Finset ℝ) (I : Finset (ℝ × ℝ)) (c₀ θ : ℝ) : Finset ℝ :=
  Z ∪ endpts I ∪ (Finset.range (⌈c₀ / θ⌉₊ + 1)).image (fun j : ℕ => (j : ℝ) * θ)

/-- **Label changes** of the M* labelling are at most twice the number of breakpoints. -/
theorem mstar_labelChanges_le (hθ : 0 < θ) (hn : 0 < n) (hN : (N : ℝ) ≤ c₀ * n)
    (hSI : S = ⋃ x ∈ I, Set.Icc x.1 x.2)
    (hβZ : ∀ u v, 0 ≤ u → u ≤ v → v ≤ c₀ → (∀ x ∈ Set.Icc u v, x ∉ S ∧ x ∉ (Z : Set ℝ)) →
      β u = β v) :
    labelChanges (mstarLabel S β θ n) N ≤ 2 * (mstarBreaks Z I c₀ θ).card := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set lab := mstarLabel S β θ n
  set Z₂ := mstarBreaks Z I c₀ θ with hZ₂
  set CH := (Finset.range N).filter (fun y => 1 ≤ y ∧ lab y ≠ lab (y - 1)) with hCH
  set B := (Finset.range N).filter
    (fun y : ℕ => ∃ z ∈ Z₂, (y : ℝ) / n ≤ z ∧ z ≤ ((y : ℝ) + 1) / n) with hB
  have hmaps : ∀ y ∈ CH, y - 1 ∈ B := by
    intro y hy
    rw [hCH, Finset.mem_filter, Finset.mem_range] at hy
    obtain ⟨hyN, hy1, hne⟩ := hy
    rw [hB, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have hcast : ((y - 1 : ℕ) : ℝ) + 1 = y := by rw [Nat.cast_sub hy1]; push_cast; ring
    rw [hcast]
    by_contra hno
    push Not at hno
    -- the interval `[(y-1)/n, y/n]` contains no breakpoint
    have hnoZ : ∀ x ∈ Set.Icc (((y - 1 : ℕ) : ℝ) / n) ((y : ℝ) / n), x ∉ Z₂ := by
      intro x hx hxZ
      exact absurd hx.2 (not_le.2 (hno x hxZ hx.1))
    have hE : ∀ e ∈ endpts I, e ∉ Set.Icc (((y - 1 : ℕ) : ℝ) / n) ((y : ℝ) / n) :=
      fun e he hx => hnoZ e hx (by
        rw [hZ₂, mstarBreaks]; exact Finset.mem_union_left _ (Finset.mem_union_right _ he))
    have hyc : (y : ℝ) / n ≤ c₀ := by
      rw [div_le_iff₀ hn']
      have : (y : ℝ) < N := by exact_mod_cast hyN
      linarith
    have hle : ((y - 1 : ℕ) : ℝ) / n ≤ (y : ℝ) / n := by
      apply div_le_div_of_nonneg_right _ hn'.le; exact_mod_cast Nat.sub_le y 1
    have hlo : ((y - 1 : ℕ) : ℝ) / n ∈ Set.Icc (((y - 1 : ℕ) : ℝ) / n) ((y : ℝ) / n) :=
      ⟨le_rfl, hle⟩
    have hhi : (y : ℝ) / n ∈ Set.Icc (((y - 1 : ℕ) : ℝ) / n) ((y : ℝ) / n) := ⟨hle, le_rfl⟩
    by_cases hoff : ∃ w ∈ Set.Icc (((y - 1 : ℕ) : ℝ) / n) ((y : ℝ) / n), w ∉ S
    · -- all of the interval is off `S`: both labels are `2 β`, and `β` is constant
      obtain ⟨w, hw, hwS⟩ := hoff
      have hall := no_S_of_no_endpts (I := I) hw (by rw [← hSI]; exact hwS) hE
      have hall' : ∀ x ∈ Set.Icc (((y - 1 : ℕ) : ℝ) / n) ((y : ℝ) / n), x ∉ S := by
        intro x hx; rw [hSI]; exact hall x hx
      have hcond : ∀ x ∈ Set.Icc (((y - 1 : ℕ) : ℝ) / n) ((y : ℝ) / n),
          x ∉ S ∧ x ∉ (Z : Set ℝ) := by
        intro x hx
        refine ⟨hall' x hx, fun hxZ => hnoZ x hx ?_⟩
        rw [hZ₂, mstarBreaks]
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_coe.1 hxZ))
      have hβeq := hβZ _ _ (by positivity) hle hyc hcond
      apply hne
      show mstarLabel S β θ n y = mstarLabel S β θ n (y - 1)
      rw [mstarLabel_off (hall' _ hhi), mstarLabel_off (hall' _ hlo), hβeq]
    · -- all of the interval is in `S`: no multiple of `θ` separates the two slots
      push Not at hoff
      have hyS := hoff _ hhi
      have hy1S := hoff _ hlo
      apply hne
      show mstarLabel S β θ n y = mstarLabel S β θ n (y - 1)
      rw [mstarLabel_on hyS, mstarLabel_on hy1S]
      congr 2
      by_contra hk
      set k := ⌊(y : ℝ) / n / θ⌋₊ with hkdef
      set k' := ⌊((y - 1 : ℕ) : ℝ) / n / θ⌋₊ with hk'def
      have hmono : k' ≤ k := Nat.floor_le_floor (div_le_div_of_nonneg_right hle hθ.le)
      have hlt : k' < k := lt_of_le_of_ne hmono (Ne.symm hk)
      have h1 : (k : ℝ) * θ ≤ (y : ℝ) / n := by
        have := Nat.floor_le (show 0 ≤ (y : ℝ) / n / θ by positivity)
        rw [← hkdef, le_div_iff₀ hθ] at this; exact this
      have h2 : ((y - 1 : ℕ) : ℝ) / n < (k : ℝ) * θ := by
        have := Nat.lt_floor_add_one (((y - 1 : ℕ) : ℝ) / n / θ)
        rw [← hk'def] at this
        have hk1 : (k' : ℝ) + 1 ≤ k := by exact_mod_cast hlt
        have : ((y - 1 : ℕ) : ℝ) / n / θ < k := lt_of_lt_of_le this hk1
        rwa [div_lt_iff₀ hθ] at this
      have hkJ : k < ⌈c₀ / θ⌉₊ + 1 := by
        have : (k : ℝ) ≤ c₀ / θ := by
          rw [le_div_iff₀ hθ]; linarith
        have : k ≤ ⌈c₀ / θ⌉₊ := by
          have := Nat.le_ceil (c₀ / θ)
          exact_mod_cast le_trans ‹(k : ℝ) ≤ c₀ / θ› this
        omega
      exact hnoZ ((k : ℝ) * θ) ⟨h2.le, h1⟩ (by
        rw [hZ₂, mstarBreaks]
        exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, Finset.mem_range.2 hkJ, rfl⟩))
  calc labelChanges lab N = CH.card := rfl
    _ ≤ B.card := by
        apply Finset.card_le_card_of_injOn (fun y => y - 1)
        · intro y hy; exact hmaps y hy
        · intro y hy y' hy' h
          simp only at h
          have := (Finset.mem_filter.1 hy).2.1
          have := (Finset.mem_filter.1 hy').2.1
          omega
    _ ≤ 2 * Z₂.card := bad_count hn Z₂ N

/-- **Class sizes** of the M* labelling: at most `⌊θ n⌋ + 2 |Z ∪ ∂S| + 1` slots per label. -/
theorem mstar_class_le (hθ : 0 < θ) (hn : 0 < n) (hN : (N : ℝ) ≤ c₀ * n)
    (hSI : S = ⋃ x ∈ I, Set.Icc x.1 x.2)
    (hβZ : ∀ u v, 0 ≤ u → u ≤ v → v ≤ c₀ → (∀ x ∈ Set.Icc u v, x ∉ S ∧ x ∉ (Z : Set ℝ)) →
      β u = β v)
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 c₀ ∧ u ∉ S ∧ β u = ℓ} ≤ ENNReal.ofReal θ)
    (ℓ : ℕ) :
    ((Finset.range N).filter (fun y => mstarLabel S β θ n y = ℓ)).card ≤
      ⌊θ * n⌋₊ + 2 * (Z ∪ endpts I).card + 1 := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set Cl := (Finset.range N).filter (fun y => mstarLabel S β θ n y = ℓ) with hCl
  rcases Nat.even_or_odd ℓ with ⟨v, hv⟩ | ⟨j, hj⟩
  · -- even label `2 v`: slots off `S` with `β = v`
    have hoff : ∀ y ∈ Cl, (y : ℝ) / n ∉ S ∧ β ((y : ℝ) / n) = v := by
      intro y hy
      rw [hCl, Finset.mem_filter] at hy
      by_cases hS : (y : ℝ) / n ∈ S
      · rw [mstarLabel_on hS] at hy; omega
      · rw [mstarLabel_off hS] at hy; exact ⟨hS, by omega⟩
    set Z₃ := Z ∪ endpts I
    set Bd := Cl.filter (fun y : ℕ => ∃ z ∈ Z₃, (y : ℝ) / n ≤ z ∧ z ≤ ((y : ℝ) + 1) / n)
    set Gd := Cl.filter (fun y : ℕ => ¬∃ z ∈ Z₃, (y : ℝ) / n ≤ z ∧ z ≤ ((y : ℝ) + 1) / n)
    have hBd : Bd.card ≤ 2 * Z₃.card := by
      refine le_trans (Finset.card_le_card ?_) (bad_count hn Z₃ N)
      intro y hy
      rw [Finset.mem_filter] at hy ⊢
      exact ⟨(Finset.mem_filter.1 hy.1).1, hy.2⟩
    have hGd : (Gd.card : ℝ≥0∞) ≤ n * ENNReal.ofReal θ := by
      refine le_trans (good_count hn Gd {u | u ∈ Set.Icc 0 c₀ ∧ u ∉ S ∧ β u = v} ?_)
        (by gcongr; exact hclass v)
      intro y hy u hu
      rw [Finset.mem_filter] at hy
      obtain ⟨hyCl, hno⟩ := hy
      push Not at hno
      obtain ⟨hyS, hyβ⟩ := hoff y hyCl
      have hyN : (y : ℝ) + 1 ≤ N := by
        have := (Finset.mem_range.1 (Finset.mem_filter.1 hyCl).1); exact_mod_cast this
      have hle : (y : ℝ) / n ≤ ((y : ℝ) + 1) / n :=
        div_le_div_of_nonneg_right (by linarith) hn'.le
      have hnoZ : ∀ x ∈ Set.Icc ((y : ℝ) / n) (((y : ℝ) + 1) / n), x ∉ Z₃ := by
        intro x hx hxZ
        exact absurd hx.2 (not_le.2 (hno x hxZ hx.1))
      have hE : ∀ e ∈ endpts I, e ∉ Set.Icc ((y : ℝ) / n) (((y : ℝ) + 1) / n) :=
        fun e he hx => hnoZ e hx (Finset.mem_union_right _ he)
      have hall := no_S_of_no_endpts (I := I) ⟨le_rfl, hle⟩ (by rw [← hSI]; exact hyS) hE
      have hc : ((y : ℝ) + 1) / n ≤ c₀ := by
        rw [div_le_iff₀ hn']; linarith
      have huIcc : u ∈ Set.Icc ((y : ℝ) / n) (((y : ℝ) + 1) / n) := ⟨hu.1, hu.2.le⟩
      refine ⟨⟨le_trans (by positivity) hu.1, le_trans hu.2.le hc⟩,
        by rw [hSI]; exact hall u huIcc, ?_⟩
      rw [← hyβ]
      symm
      apply hβZ _ _ (by positivity) hu.1 (le_trans hu.2.le hc)
      intro x hx
      have hx' : x ∈ Set.Icc ((y : ℝ) / n) (((y : ℝ) + 1) / n) := ⟨hx.1, le_trans hx.2 hu.2.le⟩
      exact ⟨by rw [hSI]; exact hall x hx', fun hxZ => hnoZ x hx'
        (Finset.mem_union_left _ (Finset.mem_coe.1 hxZ))⟩
    have hGd' : Gd.card ≤ ⌊θ * n⌋₊ := by
      apply Nat.le_floor
      have h1 : ENNReal.ofReal (Gd.card : ℝ) ≤ ENNReal.ofReal (θ * n) := by
        rw [ENNReal.ofReal_natCast, ENNReal.ofReal_mul hθ.le, ENNReal.ofReal_natCast, mul_comm]
        exact hGd
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
    have hsplit : Cl.card = Bd.card + Gd.card := (Finset.card_filter_add_card_filter_not _).symm
    omega
  · -- odd label `2 j + 1`: slots in `S` with `⌊(y/n)/θ⌋ = j`
    have hon : ∀ y ∈ Cl, (j : ℝ) * θ * n ≤ y ∧ (y : ℝ) < ((j : ℝ) + 1) * θ * n := by
      intro y hy
      rw [hCl, Finset.mem_filter] at hy
      by_cases hS : (y : ℝ) / n ∈ S
      · rw [mstarLabel_on hS] at hy
        have hfl : ⌊(y : ℝ) / n / θ⌋₊ = j := by omega
        have hy0 : 0 ≤ (y : ℝ) / n / θ := by positivity
        obtain ⟨h1, h2⟩ := (Nat.floor_eq_iff hy0).1 hfl
        rw [le_div_iff₀ hθ, le_div_iff₀ hn'] at h1
        rw [div_lt_iff₀ hθ, div_lt_iff₀ hn'] at h2
        constructor <;> nlinarith
      · rw [mstarLabel_off hS] at hy; omega
    calc Cl.card ≤ (Finset.range (⌊θ * n⌋₊ + 1)).card := by
          apply Finset.card_le_card_of_injOn (fun y => y - ⌈(j : ℝ) * θ * n⌉₊)
          · intro y hy
            have hy' := hon y hy
            rw [Finset.mem_coe, Finset.mem_range]
            have hc1 : ⌈(j : ℝ) * θ * n⌉₊ ≤ y := Nat.ceil_le.2 hy'.1
            have hc2 : (j : ℝ) * θ * n ≤ ⌈(j : ℝ) * θ * n⌉₊ := Nat.le_ceil _
            have : ((y - ⌈(j : ℝ) * θ * n⌉₊ : ℕ) : ℝ) ≤ θ * n := by
              rw [Nat.cast_sub hc1]; nlinarith
            have := Nat.le_floor this
            show y - ⌈(j : ℝ) * θ * n⌉₊ < ⌊θ * n⌋₊ + 1
            omega
          · intro y hy y' hy' h
            have h' : y - ⌈(j : ℝ) * θ * n⌉₊ = y' - ⌈(j : ℝ) * θ * n⌉₊ := h
            have h1 := Nat.ceil_le.2 (hon y hy).1
            have h2 := Nat.ceil_le.2 (hon y' hy').1
            omega
      _ = ⌊θ * n⌋₊ + 1 := Finset.card_range _
      _ ≤ _ := by omega

open Classical in
/-- **Slots in `S`** number at most `n |S ∩ [0, c₀]| + 2 |∂S|`. -/
theorem slots_in_S_le (hn : 0 < n) (hN : (N : ℝ) ≤ c₀ * n)
    (hSI : S = ⋃ x ∈ I, Set.Icc x.1 x.2) :
    (((Finset.range N).filter (fun y : ℕ => (y : ℝ) / n ∈ S)).card : ℝ) ≤
      n * (volume (S ∩ Set.Icc 0 c₀)).toReal + 2 * (endpts I).card := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set YS := (Finset.range N).filter (fun y : ℕ => (y : ℝ) / n ∈ S)
  set Bd := YS.filter (fun y : ℕ => ∃ z ∈ endpts I, (y : ℝ) / n ≤ z ∧ z ≤ ((y : ℝ) + 1) / n)
  set Gd := YS.filter (fun y : ℕ => ¬∃ z ∈ endpts I, (y : ℝ) / n ≤ z ∧ z ≤ ((y : ℝ) + 1) / n)
  have hBd : Bd.card ≤ 2 * (endpts I).card := by
    refine le_trans (Finset.card_le_card ?_) (bad_count hn (endpts I) N)
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨(Finset.mem_filter.1 hy.1).1, hy.2⟩
  have hGd : (Gd.card : ℝ≥0∞) ≤ n * volume (S ∩ Set.Icc 0 c₀) := by
    apply good_count hn
    intro y hy u hu
    rw [Finset.mem_filter] at hy
    obtain ⟨hyS, hno⟩ := hy
    push Not at hno
    rw [Finset.mem_filter, Finset.mem_range] at hyS
    obtain ⟨hyN, hyS⟩ := hyS
    have hyN' : (y : ℝ) + 1 ≤ N := by exact_mod_cast hyN
    have hle : (y : ℝ) / n ≤ ((y : ℝ) + 1) / n :=
      div_le_div_of_nonneg_right (by linarith) hn'.le
    have hE : ∀ e ∈ endpts I, e ∉ Set.Icc ((y : ℝ) / n) (((y : ℝ) + 1) / n) :=
      fun e he hx => absurd hx.2 (not_le.2 (hno e he hx.1))
    have hc : ((y : ℝ) + 1) / n ≤ c₀ := by
      rw [div_le_iff₀ hn']; linarith
    have huIcc : u ∈ Set.Icc ((y : ℝ) / n) (((y : ℝ) + 1) / n) := ⟨hu.1, hu.2.le⟩
    refine ⟨?_, le_trans (by positivity) hu.1, le_trans hu.2.le hc⟩
    by_contra huS
    have hall := no_S_of_no_endpts (I := I) huIcc (by rw [← hSI]; exact huS) hE
    exact hall _ ⟨le_rfl, hle⟩ (by rw [← hSI]; exact hyS)
  have hfin : volume (S ∩ Set.Icc 0 c₀) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono Set.inter_subset_right)
  have hGd' : (Gd.card : ℝ) ≤ n * (volume (S ∩ Set.Icc 0 c₀)).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hfin) hGd
    rwa [ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_natCast] at this
  have hsplit : YS.card = Bd.card + Gd.card := (Finset.card_filter_add_card_filter_not _).symm
  have : (YS.card : ℝ) = Bd.card + Gd.card := by exact_mod_cast hsplit
  have : (Bd.card : ℝ) ≤ 2 * (endpts I).card := by exact_mod_cast hBd
  linarith

end Labelling

end Transpose.Tape.Impl

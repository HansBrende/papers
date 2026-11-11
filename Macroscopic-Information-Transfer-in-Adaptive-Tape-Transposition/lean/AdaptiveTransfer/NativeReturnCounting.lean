import AdaptiveTransfer.NativeSlabClasses
import AdaptiveTransfer.NativeReplayEstimates

/-! The finite return bound on original adaptive executions. Native slab
selection, bounded metadata extraction, return/tag accounting and the finite
union are combined here; no common detailed trace is assumed. -/

namespace AdaptiveTransfer
open Transpose MergeDepth BoundedNesting NativeRelations Finset LeanMachine
open scoped BigOperators

noncomputable def returnTime (P : ℕ) (c : ℝ) : ℕ := ⌊c * ((P : ℝ) + 1)⌋₊

noncomputable def slabSaving (d b a : ℕ) (c : ℝ) : ℝ :=
  (d * d * b : ℕ) / (4 * (slabRunCap a c : ℝ)) -
    3 * (slabRunCap a c : ℝ) * d * b - a

def returnSparseMenu (k T J A : ℕ) : ℕ :=
  ∑ j ∈ range (min (k * T) J + 1), (k * T).choose j * A ^ j

theorem returnSparseMenu_pos (k T J A : ℕ) : 0 < returnSparseMenu k T J A := by
  have hh : (k * T).choose 0 * A ^ 0 ≤
      ∑ j ∈ range (min (k * T) J + 1), (k * T).choose j * A ^ j :=
    single_le_sum (f := fun j => (k * T).choose j * A ^ j) (a := 0)
      (fun _ _ => Nat.zero_le _) (mem_range.mpr (Nat.succ_pos _))
  simpa only [Nat.choose_zero_right, pow_zero, mul_one, returnSparseMenu,
    Nat.lt_iff_add_one_le, zero_add] using hh

theorem replayMetadataSize_pos {k T W N : ℕ} (hk : 1 ≤ k) :
    0 < replayMetadataSize k T W N := by
  unfold replayMetadataSize
  positivity

/-- Positive geometric saving selects a nonempty literal native slab. The
returned observation contains only actual run data, not a decoding premise. -/
theorem native_positive_saving_observation {M : TM} {d b a H J : ℕ} {c : ℝ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hP : 2 ≤ d * d * b) (ha : 1 ≤ a) (hc : 1 ≤ c)
    {X : Fin (d * d * b) → Bool} (hcorrect : TransposesInput M d b c X)
    (hreturns : ∃ f : Fin M.k,
      (offCarrierReturns (trace M (List.ofFn X)).work f (trace M (List.ofFn X)).haltTime H).card ≤ J)
    (hsaving : 0 < slabSaving d b a c) :
    ∃ g : SlabObservation (trace M (List.ofFn X)) (returnTime (d * d * b) c)
      (slabWidth (d * d * b) a c) (slabRunCap a c),
      g.finish ≤ (trace M (List.ofFn X)).haltTime ∧
      (offCarrierReturns (trace M (List.ofFn X)).work g.free
        (trace M (List.ofFn X)).haltTime H).card ≤ J ∧
      slabSaving d b a c ≤
        ((omittedSlabBits d b (trace M (List.ofFn X)).input
          (fun j => appendTime (trace M (List.ofFn X))
            (trace M (List.ofFn X)).haltTime j.val) g.times).card : ℝ) -
        (a : ℝ) * (if g.start = 0 then 0 else (slabWidth (d * d * b) a c : ℝ)) := by
  obtain ⟨f, hf⟩ := hreturns
  obtain ⟨ell, s, e, hse, he, _hhalf, hruns, hmargin⟩ :=
    native_slab_geometry (a := (a : ℝ)) hd hb hP (by exact_mod_cast ha) hc hcorrect f
  have hne : (selectedSlab ((trace M (List.ofFn X)).work f)
      (slabWidth (d * d * b) a c) ell s e).Nonempty := by
    by_contra hn
    have hemp := not_nonempty_iff_eq_empty.mp hn
    have hU : omittedSlabBits d b (trace M (List.ofFn X)).input
        (fun j => appendTime (trace M (List.ofFn X)) (trace M (List.ofFn X)).haltTime j.val)
        (selectedSlab ((trace M (List.ofFn X)).work f) (slabWidth (d * d * b) a c) ell s e) = ∅ := by
      simp [omittedSlabBits, outIn, hemp]
    change slabSaving d b a c ≤ _ at hmargin
    rw [hU, card_empty, Nat.cast_zero] at hmargin
    have hcost : 0 ≤ (a : ℝ) * (if s = 0 then 0 else (slabWidth (d * d * b) a c : ℝ)) := by
      split_ifs <;> positivity
    linarith
  let g : SlabObservation (trace M (List.ofFn X)) (returnTime (d * d * b) c)
      (slabWidth (d * d * b) a c) (slabRunCap a c) :=
    ⟨f, ell, s, e, hse, he.trans (timely_native_data hcorrect).1, hne, hruns⟩
  exact ⟨g, he, hf, hmargin⟩

/-- The finite union of ACTUAL replay classes, after each input has selected
its native slab by the proved geometry theorem. -/
theorem native_return_union_bound {M : TM} {d b a q H J : ℕ} {c : ℝ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hP : 2 ≤ d * d * b)
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hq : M.q + 1 ≤ 2 ^ q) (hA : M.g + 1 ≤ 2 ^ a)
    (D : Finset (Fin (d * d * b) → Bool))
    (correct : ∀ X : D, TransposesInput M d b c X.val)
    (returns : ∀ X : D, ∃ f : Fin M.k,
      (offCarrierReturns (trace M (List.ofFn X.val)).work f
        (trace M (List.ofFn X.val)).haltTime H).card ≤ J)
    (hsaving : 0 < slabSaving d b a c) :
    (D.card : ℝ) ≤
      (replayMetadataSize M.k (returnTime (d * d * b) c)
        (slabWidth (d * d * b) a c) (slabRunCap a c) : ℝ) *
      ((2 : ℝ) ^ ((d * d * b : ℕ) - slabSaving d b a c +
          (slabRunCap a c : ℝ) * q + (a : ℝ) * (M.k - 1 : ℕ) *
            (slabRunCap a c : ℝ) * (2 * H + 1)) *
        (returnSparseMenu M.k (returnTime (d * d * b) c) J (M.g + 1) : ℝ)) := by
  classical
  rcases D.eq_empty_or_nonempty with hD | hD
  · rw [hD, card_empty, Nat.cast_zero]
    positivity
  let P := d * d * b
  let T := returnTime P c
  let W := slabWidth P a c
  let N := slabRunCap a c
  have hex (X : D) := native_positive_saving_observation hd hb hP ha hc
    (correct X) (returns X) hsaving
  let obs (X : D) : SlabObservation (trace M (List.ofFn X.val)) T W N := (hex X).choose
  have hfinish (X : D) : (obs X).finish ≤ (trace M (List.ofFn X.val)).haltTime :=
    (hex X).choose_spec.1
  have hreturns (X : D) := (hex X).choose_spec.2.1
  have hmargin (X : D) := (hex X).choose_spec.2.2
  let X₀ : D := ⟨hD.choose, hD.choose_spec⟩
  let encoding (X : Fin P → Bool) : ReplayMetadata M.k T W N :=
    if hX : X ∈ D then (obs ⟨X, hX⟩).encode else (obs X₀).encode
  have henc (X : D) : encoding X.val = (obs X).encode := by
    simp only [encoding, dite_eq_left X.property]
  let cost : ℝ := (2 : ℝ) ^ ((P : ℝ) - slabSaving d b a c + (N : ℝ) * q +
    (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * H + 1)) *
      (returnSparseMenu M.k T J (M.g + 1) : ℝ)
  have hfibre (σ : ReplayMetadata M.k T W N) :
      ((D.filter fun X => encoding X = σ).card : ℝ) ≤ cost := by
    let F := D.filter fun X => encoding X = σ
    rcases F.eq_empty_or_nonempty with hF | hF
    · change (F.card : ℝ) ≤ cost
      rw [hF, card_empty, Nat.cast_zero]
      dsimp [cost]
      positivity
    let lift (X : F) : D := ⟨X.val, (mem_filter.mp X.property).1⟩
    let X₁ : F := ⟨hF.choose, hF.choose_spec⟩
    have hsame (X : F) : (obs (lift X)).encode = (obs (lift X₁)).encode := by
      rw [← henc (lift X), ← henc (lift X₁)]
      exact (mem_filter.mp X.property).2.trans (mem_filter.mp X₁.property).2.symm
    let G := constantSlabClass F (fun X => correct (lift X)) (fun X => obs (lift X))
      (fun X => hfinish (lift X)) (fun X => hreturns (lift X)) X₁ hsame
    have hsave : slabSaving d b a c ≤ (G.omitted.card : ℝ) -
        (a : ℝ) * (if G.start = 0 then 0 else (G.cells.card : ℝ)) := by
      dsimp only [G]
      rw [constantSlabClass_omitted]
      simpa only [constantSlabClass, integerSlab_card] using hmargin (lift X₁)
    exact G.saving_card_bound q a N hq hA (obs (lift X₁)).run_cap _ hsave
  have hcard : D.card = ∑ σ : ReplayMetadata M.k T W N, (D.filter fun X => encoding X = σ).card :=
    card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
  have hsum : (D.card : ℝ) ≤ (replayMetadataSize M.k T W N : ℝ) * cost := by
    rw [hcard, Nat.cast_sum]
    calc
      _ ≤ ∑ _σ : ReplayMetadata M.k T W N, cost := sum_le_sum (fun σ _ => hfibre σ)
      _ = _ := by simp only [sum_const, card_univ, replayMetadata_card, nsmul_eq_mul]
  exact hsum

/-- The finite native bound, including the small-dimension case in which the
geometric saving is nonpositive and the full Boolean cube bound suffices. -/
theorem native_finite_return_product_bound {M : TM} {d b a q H J : ℕ} {c : ℝ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hP : 2 ≤ d * d * b) (hk : 1 ≤ M.k)
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hq : M.q + 1 ≤ 2 ^ q) (hA : M.g + 1 ≤ 2 ^ a)
    (D : Finset (Fin (d * d * b) → Bool))
    (correct : ∀ X : D, TransposesInput M d b c X.val)
    (returns : ∀ X : D, ∃ f : Fin M.k,
      (offCarrierReturns (trace M (List.ofFn X.val)).work f
        (trace M (List.ofFn X.val)).haltTime H).card ≤ J) :
    (D.card : ℝ) ≤
      (replayMetadataSize M.k (returnTime (d * d * b) c)
        (slabWidth (d * d * b) a c) (slabRunCap a c) : ℝ) *
      ((2 : ℝ) ^ ((d * d * b : ℕ) - slabSaving d b a c +
          (slabRunCap a c : ℝ) * q + (a : ℝ) * (M.k - 1 : ℕ) *
            (slabRunCap a c : ℝ) * (2 * H + 1)) *
        (returnSparseMenu M.k (returnTime (d * d * b) c) J (M.g + 1) : ℝ)) := by
  by_cases hs : 0 < slabSaving d b a c
  · exact native_return_union_bound hd hb hP ha hc hq hA D correct returns hs
  · have hs' : slabSaving d b a c ≤ 0 := le_of_not_gt hs
    let P := d * d * b
    let N := slabRunCap a c
    let E : ℝ := (P : ℝ) - slabSaving d b a c + (N : ℝ) * q +
      (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * H + 1)
    let m := replayMetadataSize M.k (returnTime P c) (slabWidth P a c) N
    let s := returnSparseMenu M.k (returnTime P c) J (M.g + 1)
    have he : (P : ℝ) ≤ E := by
      dsimp [E]
      have hnq : 0 ≤ (N : ℝ) * q := by positivity
      have han : 0 ≤ (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * H + 1) := by positivity
      linarith
    have hm : 1 ≤ m := replayMetadataSize_pos hk
    have hsp : 1 ≤ s := returnSparseMenu_pos _ _ _ _
    have hms : (1 : ℝ) ≤ (m : ℝ) * (s : ℝ) := by
      exact_mod_cast Nat.mul_le_mul hm hsp
    have hcard : (D.card : ℝ) ≤ (2 : ℝ) ^ (P : ℝ) := by
      have hh : D.card ≤ 2 ^ P := by
        simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using card_le_univ D
      rw [Real.rpow_natCast]
      exact_mod_cast hh
    calc
      (D.card : ℝ) ≤ (2 : ℝ) ^ (P : ℝ) := hcard
      _ ≤ (2 : ℝ) ^ E := Real.rpow_le_rpow_of_exponent_le (by norm_num) he
      _ ≤ (2 : ℝ) ^ E * ((m : ℝ) * (s : ℝ)) := le_mul_of_one_le_right (by positivity) hms
      _ = _ := by change (2 : ℝ) ^ E * ((m : ℝ) * (s : ℝ)) = (m : ℝ) * ((2 : ℝ) ^ E * (s : ℝ)); ring

/-- Exact manuscript exponent: the finite menu and sparse joint record each
contribute their single base-two logarithm. -/
theorem native_finite_return_bound {M : TM} {d b a q H J : ℕ} {c : ℝ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hP : 2 ≤ d * d * b) (hk : 1 ≤ M.k)
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hq : M.q + 1 ≤ 2 ^ q) (hA : M.g + 1 ≤ 2 ^ a)
    (D : Finset (Fin (d * d * b) → Bool))
    (correct : ∀ X : D, TransposesInput M d b c X.val)
    (returns : ∀ X : D, ∃ f : Fin M.k,
      (offCarrierReturns (trace M (List.ofFn X.val)).work f
        (trace M (List.ofFn X.val)).haltTime H).card ≤ J) :
    let P := d * d * b
    let T := returnTime P c
    let W := slabWidth P a c
    let N := slabRunCap a c
    (D.card : ℝ) ≤ (2 : ℝ) ^ ((P : ℝ) - (P : ℝ) / (4 * (N : ℝ)) +
      (3 * (N : ℝ) * d * b + a + (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * H + 1) +
        (N : ℝ) * q + Real.logb 2 (replayMetadataSize M.k T W N) +
          Real.logb 2 (returnSparseMenu M.k T J (M.g + 1)))) := by
  let P := d * d * b
  let T := returnTime P c
  let W := slabWidth P a c
  let N := slabRunCap a c
  let m := replayMetadataSize M.k T W N
  let s := returnSparseMenu M.k T J (M.g + 1)
  have hm : (0 : ℝ) < m := by exact_mod_cast replayMetadataSize_pos (T := T) (W := W) (N := N) hk
  have hs : (0 : ℝ) < s := by exact_mod_cast returnSparseMenu_pos M.k T J (M.g + 1)
  have hh := native_finite_return_product_bound hd hb hP hk ha hc hq hA D correct returns
  change (D.card : ℝ) ≤ (2 : ℝ) ^ ((P : ℝ) - (P : ℝ) / (4 * (N : ℝ)) +
      (3 * (N : ℝ) * d * b + a + (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * H + 1) +
        (N : ℝ) * q + Real.logb 2 m + Real.logb 2 s))
  have he : (P : ℝ) - (P : ℝ) / (4 * (N : ℝ)) +
      (3 * (N : ℝ) * d * b + a + (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * H + 1) +
        (N : ℝ) * q + Real.logb 2 m + Real.logb 2 s) =
      ((P : ℝ) - slabSaving d b a c + (N : ℝ) * q +
        (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * H + 1)) + Real.logb 2 m + Real.logb 2 s := by
    dsimp [slabSaving, P, N]
    ring
  rw [he, Real.rpow_add (by norm_num), Real.rpow_add (by norm_num),
    Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hm,
    Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hs]
  convert hh using 1; ring

end AdaptiveTransfer

import AdaptiveTransfer.GetterNativeClasses
import AdaptiveTransfer.GetterMetadataRates

/-! The finite native getter theorem: select the actual slab, encode its
literal geometry, apply replay inside each fibre, and sum the exact menu.
Carrier and label are chosen once per original whole run.
-/

namespace AdaptiveTransfer.Getter
open Transpose MergeDepth NativeRelations Finset LeanMachine
open scoped BigOperators

variable {M : TM} {U Λ : Type*} [Fintype U] [Fintype Λ]
  {v R d b a q z H J : ℕ} {c : ℝ}

theorem native_getter_union_bound
    (hd : 1 ≤ d) (hb : 1 ≤ b) (ha : 1 ≤ a) (hP : 4 * (v + 1) ≤ d * d * b)
    (hc : 1 ≤ c) (hR : R ≤ (d * d * b) / (8 * (v + 1) * portRunCap a (v + 1) c))
    (A : Observer M U v R) (G : Fin M.k → Getters M U Λ v R)
    (hq : (M.q + 1) * Fintype.card U ≤ 2 ^ q) (hz : Fintype.card Λ ≤ 2 ^ z)
    (hA : M.g + 1 ≤ 2 ^ a)
    (D : Finset (Fin (d * d * b) → Bool))
    (correct : ∀ X : D, TransposesInput M d b c X.val)
    (errors : ∀ X : D, ∃ f : Fin M.k, ∃ label : Λ,
      (nativeErrors A (G f) f label (List.ofFn X.val) (trace M (List.ofFn X.val)).haltTime H).card ≤ J)
    (hsaving : 0 < portSaving d b a (v + 1) c) :
    (D.card : ℝ) ≤
      (portMetadataSize M.k (v + 1) (returnTime (d * d * b) c)
        (portSlabWidth (d * d * b) a (v + 1) c) (portRunCap a (v + 1) c) : ℝ) *
      ((2 : ℝ) ^ ((d * d * b : ℕ) - portSaving d b a (v + 1) c + z +
          (portRunCap a (v + 1) c : ℝ) * q +
          (a : ℝ) * (M.k - 1 : ℕ) * portRunCap a (v + 1) c * (2 * H + 1)) *
        (returnSparseMenu M.k (returnTime (d * d * b) c) J (M.g + 1) : ℝ)) := by
  classical
  rcases D.eq_empty_or_nonempty with hD | hD
  · rw [hD, card_empty, Nat.cast_zero]
    positivity
  let P := d * d * b
  let T := returnTime P c
  let W := portSlabWidth P a (v + 1) c
  let N := portRunCap a (v + 1) c
  choose f labels herr using errors
  have hex (X : D) := native_port_observation hd hb ha hP hc hR A (G (f X))
    (correct X) (f X) (labels X) (herr X) hsaving
  let obs (X : D) : SlabObservation (trace M (List.ofFn X.val)) T W N := (hex X).choose
  have hfree (X : D) : (obs X).free = f X := (hex X).choose_spec.1
  have hfinish (X : D) : (obs X).finish ≤ (trace M (List.ofFn X.val)).haltTime := (hex X).choose_spec.2.1
  have herror (X : D) :
      (nativeErrors A (G (obs X).free) (obs X).free (labels X) (List.ofFn X.val)
        (trace M (List.ofFn X.val)).haltTime H).card ≤ J := by
    rw [hfree X]
    exact herr X
  have hmargin (X : D) := (hex X).choose_spec.2.2.2
  let X₀ : D := ⟨hD.choose, hD.choose_spec⟩
  let encodeObs (X : D) := Observation.encode (obs X) (A.paths (List.ofFn X.val))
    A.publicOrigins (A.paths_walk _) (A.paths_zero _)
  let encoding (X : Fin P → Bool) : PortMetadata M.k (v + 1) T W N :=
    if hX : X ∈ D then encodeObs ⟨X, hX⟩ else encodeObs X₀
  have henc (X : D) : encoding X.val = encodeObs X := by simp only [encoding, dite_eq_left X.property]
  let cost : ℝ := (2 : ℝ) ^ ((P : ℝ) - portSaving d b a (v + 1) c + z + (N : ℝ) * q +
    (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * H + 1)) * (returnSparseMenu M.k T J (M.g + 1) : ℝ)
  have hfibre (σ : PortMetadata M.k (v + 1) T W N) :
      ((D.filter fun X => encoding X = σ).card : ℝ) ≤ cost := by
    let F := D.filter fun X => encoding X = σ
    rcases F.eq_empty_or_nonempty with hF | hF
    · change (F.card : ℝ) ≤ cost
      rw [hF, card_empty, Nat.cast_zero]
      dsimp [cost]
      positivity
    let lift (X : F) : D := ⟨X.val, (mem_filter.mp X.property).1⟩
    let X₁ : F := ⟨hF.choose, hF.choose_spec⟩
    have hsame (X : F) : encodeObs (lift X) = encodeObs (lift X₁) := by
      rw [← henc (lift X), ← henc (lift X₁)]
      exact (mem_filter.mp X.property).2.trans (mem_filter.mp X₁.property).2.symm
    have hf (X : F) : (obs (lift X)).free = (obs (lift X₁)).free :=
      Observation.free_eq _ _ _ _ _ (hsame X)
    have he (X : F) :
        (nativeErrors A (G (obs (lift X₁)).free) (obs (lift X)).free (labels (lift X))
          (List.ofFn X.val) (trace M (List.ofFn X.val)).haltTime H).card ≤ J := by
      have hh := herror (lift X)
      rw [hf X] at hh ⊢
      exact hh
    exact native_port_class_saving A (G (obs (lift X₁)).free) F (fun X => correct (lift X))
      (fun X => labels (lift X)) (fun X => obs (lift X)) (fun X => hfinish (lift X)) he X₁ hsame
      hq hz hA (portSaving d b a (v + 1) c) (hmargin (lift X₁))
  have hcard : D.card = ∑ σ : PortMetadata M.k (v + 1) T W N, (D.filter fun X => encoding X = σ).card :=
    card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
  rw [hcard, Nat.cast_sum]
  calc
    _ ≤ ∑ _σ : PortMetadata M.k (v + 1) T W N, cost := sum_le_sum (fun σ _ => hfibre σ)
    _ = _ := by simp only [sum_const, card_univ, portMetadata_card, nsmul_eq_mul]; rfl

theorem native_getter_product_bound
    (hd : 1 ≤ d) (hb : 1 ≤ b) (ha : 1 ≤ a) (hk : 1 ≤ M.k)
    (hP : 4 * (v + 1) ≤ d * d * b) (hc : 1 ≤ c)
    (hR : R ≤ (d * d * b) / (8 * (v + 1) * portRunCap a (v + 1) c))
    (A : Observer M U v R) (G : Fin M.k → Getters M U Λ v R)
    (hq : (M.q + 1) * Fintype.card U ≤ 2 ^ q) (hz : Fintype.card Λ ≤ 2 ^ z)
    (hA : M.g + 1 ≤ 2 ^ a)
    (D : Finset (Fin (d * d * b) → Bool))
    (correct : ∀ X : D, TransposesInput M d b c X.val)
    (errors : ∀ X : D, ∃ f : Fin M.k, ∃ label : Λ,
      (nativeErrors A (G f) f label (List.ofFn X.val) (trace M (List.ofFn X.val)).haltTime H).card ≤ J) :
    (D.card : ℝ) ≤
      (portMetadataSize M.k (v + 1) (returnTime (d * d * b) c)
        (portSlabWidth (d * d * b) a (v + 1) c) (portRunCap a (v + 1) c) : ℝ) *
      ((2 : ℝ) ^ ((d * d * b : ℕ) - portSaving d b a (v + 1) c + z +
          (portRunCap a (v + 1) c : ℝ) * q +
          (a : ℝ) * (M.k - 1 : ℕ) * portRunCap a (v + 1) c * (2 * H + 1)) *
        (returnSparseMenu M.k (returnTime (d * d * b) c) J (M.g + 1) : ℝ)) := by
  by_cases hs : 0 < portSaving d b a (v + 1) c
  · exact native_getter_union_bound hd hb ha hP hc hR A G hq hz hA D correct errors hs
  · have hs' : portSaving d b a (v + 1) c ≤ 0 := le_of_not_gt hs
    let P := d * d * b
    let N := portRunCap a (v + 1) c
    let E : ℝ := (P : ℝ) - portSaving d b a (v + 1) c + z + (N : ℝ) * q +
      (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * H + 1)
    let m := portMetadataSize M.k (v + 1) (returnTime P c) (portSlabWidth P a (v + 1) c) N
    let s := returnSparseMenu M.k (returnTime P c) J (M.g + 1)
    have he : (P : ℝ) ≤ E := by
      dsimp [E]
      have h₁ : 0 ≤ (N : ℝ) * q := by positivity
      have h₂ : 0 ≤ (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * H + 1) := by positivity
      linarith [show (0 : ℝ) ≤ z from Nat.cast_nonneg z]
    have hm : 1 ≤ m := portMetadataSize_pos hk
    have hsp : 1 ≤ s := returnSparseMenu_pos _ _ _ _
    have hms : (1 : ℝ) ≤ (m : ℝ) * (s : ℝ) := by exact_mod_cast Nat.mul_le_mul hm hsp
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

/-- The exact manuscript finite exponent, valid for every declared native
observer/getter system and every individual timely-correct input set. -/
theorem native_finite_getter_bound
    (hd : 1 ≤ d) (hb : 1 ≤ b) (ha : 1 ≤ a) (hk : 1 ≤ M.k)
    (hP : 4 * (v + 1) ≤ d * d * b) (hc : 1 ≤ c)
    (hR : R ≤ (d * d * b) / (8 * (v + 1) * portRunCap a (v + 1) c))
    (A : Observer M U v R) (G : Fin M.k → Getters M U Λ v R)
    (hq : (M.q + 1) * Fintype.card U ≤ 2 ^ q) (hz : Fintype.card Λ ≤ 2 ^ z)
    (hA : M.g + 1 ≤ 2 ^ a)
    (D : Finset (Fin (d * d * b) → Bool))
    (correct : ∀ X : D, TransposesInput M d b c X.val)
    (errors : ∀ X : D, ∃ f : Fin M.k, ∃ label : Λ,
      (nativeErrors A (G f) f label (List.ofFn X.val) (trace M (List.ofFn X.val)).haltTime H).card ≤ J) :
    let P := d * d * b
    let T := returnTime P c
    let W := portSlabWidth P a (v + 1) c
    let N := portRunCap a (v + 1) c
    (D.card : ℝ) ≤ (2 : ℝ) ^ ((P : ℝ) - (P : ℝ) / (4 * (N : ℝ)) +
      (3 * (N : ℝ) * d * b + a + (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * H + 1) +
        (N : ℝ) * q + z + Real.logb 2 (portMetadataSize M.k (v + 1) T W N) +
          Real.logb 2 (returnSparseMenu M.k T J (M.g + 1)))) := by
  let P := d * d * b
  let T := returnTime P c
  let W := portSlabWidth P a (v + 1) c
  let N := portRunCap a (v + 1) c
  let m := portMetadataSize M.k (v + 1) T W N
  let s := returnSparseMenu M.k T J (M.g + 1)
  have hm : (0 : ℝ) < m := by exact_mod_cast portMetadataSize_pos (p := v + 1) (T := T) (W := W) (N := N) hk
  have hs : (0 : ℝ) < s := by exact_mod_cast returnSparseMenu_pos M.k T J (M.g + 1)
  have hh := native_getter_product_bound hd hb ha hk hP hc hR A G hq hz hA D correct errors
  change (D.card : ℝ) ≤ (2 : ℝ) ^ ((P : ℝ) - (P : ℝ) / (4 * (N : ℝ)) +
    (3 * (N : ℝ) * d * b + a + (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * H + 1) +
      (N : ℝ) * q + z + Real.logb 2 m + Real.logb 2 s))
  have he : (P : ℝ) - (P : ℝ) / (4 * (N : ℝ)) +
      (3 * (N : ℝ) * d * b + a + (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * H + 1) +
        (N : ℝ) * q + z + Real.logb 2 m + Real.logb 2 s) =
      ((P : ℝ) - portSaving d b a (v + 1) c + z + (N : ℝ) * q +
        (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * H + 1)) + Real.logb 2 m + Real.logb 2 s := by
    dsimp [portSaving, P, N]; ring
  rw [he, Real.rpow_add (by norm_num), Real.rpow_add (by norm_num),
    Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hm,
    Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hs]
  convert hh using 1; ring

end AdaptiveTransfer.Getter

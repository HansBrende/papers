import AdaptiveTransfer.EnlargedClasses
import AdaptiveTransfer.GetterMetadataRates

/-! The finite bound for the entire enlarged rule, including its own port
updates, prior-output access and one immutable label. All motion, output
coverage, slab selection, geometry and replay maps are constructed here.
-/

namespace AdaptiveTransfer.Enlarged
open Transpose MergeDepth NativeRelations Finset Getter
open scoped BigOperators

variable {Q Γ Λ : Type*} [Fintype Q] [Fintype Γ] [Fintype Λ]
  {p R d b a q z : ℕ} {c : ℝ}
  (M : System Q Γ Λ 1 p R)

theorem union_bound
    (hd : 1 ≤ d) (hb : 1 ≤ b) (ha : 1 ≤ a) (hp : 1 ≤ p)
    (hP : 4 * p ≤ d * d * b) (hc : 1 ≤ c)
    (hR : R ≤ (d * d * b) / (8 * p * portRunCap a p c))
    (hq : Fintype.card Q ≤ 2 ^ q) (hz : Fintype.card Λ ≤ 2 ^ z)
    (hA : Fintype.card Γ ≤ 2 ^ a)
    (D : Finset (Fin (d * d * b) → Bool))
    (correct : ∀ X : D, ∃ label : Λ, M.OutputBy (tposOf d b) (returnTime (d * d * b) c) X.val label)
    (hsaving : 0 < portSaving d b a p c) :
    (D.card : ℝ) ≤
      (portMetadataSize 1 p (returnTime (d * d * b) c)
        (portSlabWidth (d * d * b) a p c) (portRunCap a p c) : ℝ) *
        (2 : ℝ) ^ ((d * d * b : ℕ) - portSaving d b a p c + z + (portRunCap a p c : ℝ) * q) := by
  classical
  rcases D.eq_empty_or_nonempty with hD | hD
  · rw [hD, card_empty, Nat.cast_zero]; positivity
  let P := d * d * b
  let T := returnTime P c
  let W := portSlabWidth P a p c
  let N := portRunCap a p c
  choose labels hout using correct
  choose finish hfinish successful output using hout
  have hex (X : D) := M.port_observation hd hb ha hp hP hc hR (hfinish X) (output X) hsaving
  let obs (X : D) : SlabObservation (M.motionTrace (labels X) (List.ofFn X.val)) T W N := (hex X).choose
  have hlast (X : D) : (obs X).finish ≤ finish X := (hex X).choose_spec.1
  have hmargin (X : D) := (hex X).choose_spec.2
  let X₀ : D := ⟨hD.choose, hD.choose_spec⟩
  let encodeObs (X : D) := Observation.encode (obs X) (M.portPaths (labels X) (List.ofFn X.val))
    M.origins (M.portPaths_walk _ _) (M.portPaths_zero _ _)
  let encoding (X : Fin P → Bool) : PortMetadata 1 p T W N :=
    if hX : X ∈ D then encodeObs ⟨X, hX⟩ else encodeObs X₀
  have henc (X : D) : encoding X.val = encodeObs X := by simp only [encoding, dite_eq_left X.property]
  let cost : ℝ := (2 : ℝ) ^ ((P : ℝ) - portSaving d b a p c + z + (N : ℝ) * q)
  have hfibre (σ : PortMetadata 1 p T W N) :
      ((D.filter fun X => encoding X = σ).card : ℝ) ≤ cost := by
    let F := D.filter fun X => encoding X = σ
    rcases F.eq_empty_or_nonempty with hF | hF
    · change (F.card : ℝ) ≤ cost
      rw [hF, card_empty, Nat.cast_zero]; dsimp [cost]; positivity
    let lift (X : F) : D := ⟨X.val, (mem_filter.mp X.property).1⟩
    let X₁ : F := ⟨hF.choose, hF.choose_spec⟩
    have hsame (X : F) : encodeObs (lift X) = encodeObs (lift X₁) := by
      rw [← henc (lift X), ← henc (lift X₁)]
      exact (mem_filter.mp X.property).2.trans (mem_filter.mp X₁.property).2.symm
    exact class_saving_bound M F (fun X => labels (lift X)) (fun X => finish (lift X))
      (fun X => successful (lift X)) (fun X => output (lift X)) (fun X => obs (lift X))
      (fun X => hlast (lift X)) X₁ hsame q z a hq hz hA (portSaving d b a p c) (hmargin (lift X₁))
  have hcard : D.card = ∑ σ : PortMetadata 1 p T W N, (D.filter fun X => encoding X = σ).card :=
    card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
  rw [hcard, Nat.cast_sum]
  calc
    _ ≤ ∑ _σ : PortMetadata 1 p T W N, cost := sum_le_sum (fun σ _ => hfibre σ)
    _ = _ := by simp only [sum_const, card_univ, portMetadata_card, nsmul_eq_mul]; rfl

theorem product_bound
    (hd : 1 ≤ d) (hb : 1 ≤ b) (ha : 1 ≤ a) (hp : 1 ≤ p)
    (hP : 4 * p ≤ d * d * b) (hc : 1 ≤ c)
    (hR : R ≤ (d * d * b) / (8 * p * portRunCap a p c))
    (hq : Fintype.card Q ≤ 2 ^ q) (hz : Fintype.card Λ ≤ 2 ^ z)
    (hA : Fintype.card Γ ≤ 2 ^ a)
    (D : Finset (Fin (d * d * b) → Bool))
    (correct : ∀ X : D, ∃ label : Λ, M.OutputBy (tposOf d b) (returnTime (d * d * b) c) X.val label) :
    (D.card : ℝ) ≤
      (portMetadataSize 1 p (returnTime (d * d * b) c)
        (portSlabWidth (d * d * b) a p c) (portRunCap a p c) : ℝ) *
        (2 : ℝ) ^ ((d * d * b : ℕ) - portSaving d b a p c + z + (portRunCap a p c : ℝ) * q) := by
  by_cases hs : 0 < portSaving d b a p c
  · exact union_bound M hd hb ha hp hP hc hR hq hz hA D correct hs
  · have hs' : portSaving d b a p c ≤ 0 := le_of_not_gt hs
    have hcube : (D.card : ℝ) ≤ (2 : ℝ) ^ (d * d * b : ℕ) := by
      exact_mod_cast (show D.card ≤ 2 ^ (d * d * b) from
        by simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using card_le_univ D)
    have he : ((d * d * b : ℕ) : ℝ) ≤
        (d * d * b : ℕ) - portSaving d b a p c + z + (portRunCap a p c : ℝ) * q := by
      have hq' : 0 ≤ (portRunCap a p c : ℝ) * q := by positivity
      linarith [show (0 : ℝ) ≤ z from Nat.cast_nonneg z]
    have hm : (1 : ℝ) ≤ (portMetadataSize 1 p (returnTime (d * d * b) c)
        (portSlabWidth (d * d * b) a p c) (portRunCap a p c) : ℝ) := by
      exact_mod_cast portMetadataSize_pos (k := 1) (p := p) (T := returnTime (d * d * b) c)
        (W := portSlabWidth (d * d * b) a p c) (N := portRunCap a p c) (by omega)
    rw [← Real.rpow_natCast] at hcube
    exact hcube.trans ((Real.rpow_le_rpow_of_exponent_le (by norm_num) he).trans
      (le_mul_of_one_le_left (by positivity) hm))

/-- The exact enlarged-rule finite exponent. For k=1 the menu has neither
noncarrier pre-entry intervals nor correction records. -/
theorem finite_bound
    (hd : 1 ≤ d) (hb : 1 ≤ b) (ha : 1 ≤ a) (hp : 1 ≤ p)
    (hP : 4 * p ≤ d * d * b) (hc : 1 ≤ c)
    (hR : R ≤ (d * d * b) / (8 * p * portRunCap a p c))
    (hq : Fintype.card Q ≤ 2 ^ q) (hz : Fintype.card Λ ≤ 2 ^ z)
    (hA : Fintype.card Γ ≤ 2 ^ a)
    (D : Finset (Fin (d * d * b) → Bool))
    (correct : ∀ X : D, ∃ label : Λ, M.OutputBy (tposOf d b) (returnTime (d * d * b) c) X.val label) :
    let P := d * d * b
    let T := returnTime P c
    let W := portSlabWidth P a p c
    let N := portRunCap a p c
    (D.card : ℝ) ≤ (2 : ℝ) ^ ((P : ℝ) - (P : ℝ) / (4 * (N : ℝ)) +
      3 * (N : ℝ) * d * b + a + (N : ℝ) * q + z + Real.logb 2
        ((N + 1) * (2 * T + W + 2) * (T + 1) ^ 2 * ((T + 1) ^ 4 * (2 * T + 1) ^ (1 + 3 * p)) ^ N : ℕ)) := by
  let P := d * d * b
  let T := returnTime P c
  let W := portSlabWidth P a p c
  let N := portRunCap a p c
  let m := portMetadataSize 1 p T W N
  have hm : (0 : ℝ) < m := by exact_mod_cast portMetadataSize_pos (k := 1) (p := p) (T := T) (W := W) (N := N) (by omega)
  have hh := product_bound M hd hb ha hp hP hc hR hq hz hA D correct
  have hmdef : m = (N + 1) * (2 * T + W + 2) * (T + 1) ^ 2 *
      ((T + 1) ^ 4 * (2 * T + 1) ^ (1 + 3 * p)) ^ N := by simp only [m, portMetadataSize, one_mul, Nat.sub_self, pow_zero, mul_one]
  change (D.card : ℝ) ≤ (2 : ℝ) ^ ((P : ℝ) - (P : ℝ) / (4 * (N : ℝ)) +
    3 * (N : ℝ) * d * b + a + (N : ℝ) * q + z + Real.logb 2 _)
  rw [← hmdef]
  have he : (P : ℝ) - (P : ℝ) / (4 * (N : ℝ)) + 3 * (N : ℝ) * d * b + a + (N : ℝ) * q + z =
      (P : ℝ) - portSaving d b a p c + z + (N : ℝ) * q := by dsimp [portSaving, P, N]; ring
  rw [he, Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hm]
  convert hh using 1; ring

end AdaptiveTransfer.Enlarged

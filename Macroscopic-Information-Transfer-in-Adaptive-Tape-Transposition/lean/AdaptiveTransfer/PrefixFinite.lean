import AdaptiveTransfer.PrefixGeometry
import AdaptiveTransfer.EnlargedObservationUnion
import AdaptiveTransfer.ReturnTail

/-! Prefix-assisted one-head counting with the original native constants.
The whole-rule replay is reused; only its geometry specialization changes.
-/

namespace AdaptiveTransfer.Enlarged
open Transpose MergeDepth NativeRelations Finset Getter

theorem one_port_metadata (T W N : ℕ) : portMetadataSize 1 1 T W N = replayMetadataSize 1 T W N := by
  simp only [portMetadataSize, replayMetadataSize, Nat.sub_self, pow_zero, mul_one]

variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] {d b a q : ℕ} {c : ℝ}
  (M : System Q Γ Unit 1 1 0)

theorem prefix_product_bound (hd : 1 ≤ d) (hb : 1 ≤ b) (ha : 1 ≤ a)
    (hP : 2 ≤ d * d * b) (hc : 1 ≤ c) (hq : Fintype.card Q ≤ 2 ^ q) (hA : Fintype.card Γ ≤ 2 ^ a)
    (D : Finset (Fin (d * d * b) → Bool))
    (correct : ∀ X : D, M.OutputBy (tposOf d b) (returnTime (d * d * b) c) X.val ()) :
    (D.card : ℝ) ≤
      (replayMetadataSize 1 (returnTime (d * d * b) c) (slabWidth (d * d * b) a c) (slabRunCap a c) : ℝ) *
        (2 : ℝ) ^ ((d * d * b : ℕ) - slabSaving d b a c + (slabRunCap a c : ℝ) * q) := by
  by_cases hs : 0 < slabSaving d b a c
  · classical
    choose finish hfinish successful output using correct
    have hex (X : D) := M.prefix_observation hd hb ha hP hc (hfinish X) (output X) hs
    let obs (X : D) : SlabObservation (M.motionTrace () (List.ofFn X.val)) (returnTime (d * d * b) c)
        (slabWidth (d * d * b) a c) (slabRunCap a c) := (hex X).choose
    have hh := actual_observation_union (q := q) (z := 0) (a := a) M D (fun _ => ()) finish
      successful output obs (fun X => (hex X).choose_spec.1) hq (by simp) hA (slabSaving d b a c)
      (fun X => (hex X).choose_spec.2)
    simpa only [one_port_metadata, Nat.cast_zero, add_zero] using hh
  · have hs' : slabSaving d b a c ≤ 0 := le_of_not_gt hs
    have hcube : (D.card : ℝ) ≤ (2 : ℝ) ^ (d * d * b : ℕ) := by
      exact_mod_cast (show D.card ≤ 2 ^ (d * d * b) from
        by simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using card_le_univ D)
    have he : ((d * d * b : ℕ) : ℝ) ≤
        (d * d * b : ℕ) - slabSaving d b a c + (slabRunCap a c : ℝ) * q := by
      have hh : 0 ≤ (slabRunCap a c : ℝ) * q := by positivity
      linarith
    have hm : (1 : ℝ) ≤ (replayMetadataSize 1 (returnTime (d * d * b) c)
        (slabWidth (d * d * b) a c) (slabRunCap a c) : ℝ) := by
      exact_mod_cast replayMetadataSize_pos (k := 1) (T := returnTime (d * d * b) c)
        (W := slabWidth (d * d * b) a c) (N := slabRunCap a c) (by omega)
    rw [← Real.rpow_natCast] at hcube
    exact hcube.trans ((Real.rpow_le_rpow_of_exponent_le (by norm_num) he).trans
      (le_mul_of_one_le_left (by positivity) hm))

/-- The original one-head finite bound remains valid for the entire strict
prefix-assisted rule. It is harmlessly stronger also to supply public time
and positions; there is still no uncharged mutable register or label. -/
theorem prefix_finite_bound (hd : 1 ≤ d) (hb : 1 ≤ b) (ha : 1 ≤ a)
    (hP : 2 ≤ d * d * b) (hc : 1 ≤ c) (hq : Fintype.card Q ≤ 2 ^ q) (hA : Fintype.card Γ ≤ 2 ^ a)
    (D : Finset (Fin (d * d * b) → Bool))
    (correct : ∀ X : D, M.OutputBy (tposOf d b) (returnTime (d * d * b) c) X.val ()) :
    let P := d * d * b
    let T := returnTime P c
    let W := slabWidth P a c
    let N := slabRunCap a c
    (D.card : ℝ) ≤ (2 : ℝ) ^ ((P : ℝ) - (P : ℝ) / (4 * (N : ℝ)) +
      3 * (N : ℝ) * d * b + a + (N : ℝ) * q + Real.logb 2 (replayMetadataSize 1 T W N)) := by
  let P := d * d * b
  let T := returnTime P c
  let W := slabWidth P a c
  let N := slabRunCap a c
  let m := replayMetadataSize 1 T W N
  have hm : (0 : ℝ) < m := by exact_mod_cast replayMetadataSize_pos (k := 1) (T := T) (W := W) (N := N) (by omega)
  have hh := prefix_product_bound M hd hb ha hP hc hq hA D correct
  change (D.card : ℝ) ≤ (2 : ℝ) ^ ((P : ℝ) - (P : ℝ) / (4 * (N : ℝ)) +
    3 * (N : ℝ) * d * b + a + (N : ℝ) * q + Real.logb 2 m)
  have he : (P : ℝ) - (P : ℝ) / (4 * (N : ℝ)) + 3 * (N : ℝ) * d * b + a + (N : ℝ) * q =
      (P : ℝ) - slabSaving d b a c + (N : ℝ) * q := by dsimp [slabSaving, P, N]; ring
  rw [he, Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hm]
  convert hh using 1; ring

end AdaptiveTransfer.Enlarged

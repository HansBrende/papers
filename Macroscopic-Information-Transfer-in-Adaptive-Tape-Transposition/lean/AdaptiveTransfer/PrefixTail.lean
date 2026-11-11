import AdaptiveTransfer.PrefixFinite

/-! The original small-controller one-head tail survives strict prior-output
assistance, with exactly the original constants and geometry menu.
-/

namespace AdaptiveTransfer.Enlarged
open Transpose MergeDepth NativeRelations Finset

universe u v

theorem prefix_macroscopic_tail (a : ℕ) {c : ℝ} (ha : 1 ≤ a) (hc : 1 ≤ c) :
    let N := slabRunCap a c
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b →
      ∀ (Q : Type u) (Γ : Type v) [Fintype Q] [Fintype Γ],
      ∀ q : ℕ, Fintype.card Q ≤ 2 ^ q → Fintype.card Γ ≤ 2 ^ a →
        (q : ℝ) ≤ (d * d * b : ℕ) / (64 * (N : ℝ) ^ 2) →
      ∀ (M : System Q Γ Unit 1 1 0) (D : Finset (Fin (d * d * b) → Bool)),
        (∀ X : D, M.OutputBy (tposOf d b) (returnTime (d * d * b) c) X.val ()) →
        (D.card : ℝ) < (2 : ℝ) ^ ((1 - returnTailEta N) * (d * d * b : ℕ)) := by
  let N := slabRunCap a c
  have hN : 1 ≤ N := by dsimp [N, slabRunCap]; omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨P₀, hmeta⟩ := native_metadata_logb_small 1 N a (by omega) ha hc
    (show (0 : ℝ) < 1 / (64 * (N : ℝ)) by positivity)
  let d₀ := 2 + 192 * N ^ 2 + P₀ + 64 * N * a
  refine ⟨d₀, ?_⟩
  intro d hd b hb Q Γ _ _ q hq hA hqbudget M D correct
  have hd2 : 2 ≤ d := by dsimp [d₀] at hd; omega
  have hdN : 192 * N ^ 2 ≤ d := by dsimp [d₀] at hd; omega
  have hdP₀ : P₀ ≤ d := by dsimp [d₀] at hd; omega
  have hda : 64 * N * a ≤ d := by dsimp [d₀] at hd; omega
  let P := d * d * b
  let T := returnTime P c
  let W := slabWidth P a c
  let m := replayMetadataSize 1 T W N
  let E : ℝ := (P : ℝ) - slabSaving d b a c + (N : ℝ) * q
  have hdP : d ≤ P := by dsimp [P]; nlinarith
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hm : Real.logb 2 m ≤ (P : ℝ) / (64 * (N : ℝ)) := by
    simpa only [one_div_mul_eq_div] using hmeta P (hdP₀.trans hdP)
  have hgeometry : 3 * (N : ℝ) * d * b ≤ (P : ℝ) / (64 * (N : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * (N : ℝ))).mpr
    have hh := mul_le_mul_of_nonneg_right (show 192 * (N : ℝ) ^ 2 ≤ d by exact_mod_cast hdN)
      (show 0 ≤ (d : ℝ) * b by positivity)
    dsimp [P]; push_cast; nlinarith
  have hconstant : (a : ℝ) ≤ (P : ℝ) / (64 * (N : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * (N : ℝ))).mpr
    have hh : (64 : ℝ) * N * a ≤ P := by exact_mod_cast hda.trans hdP
    nlinarith
  have hcontroller : (N : ℝ) * q ≤ (P : ℝ) / (64 * (N : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hqbudget hNr.le
    have he : (N : ℝ) * ((P : ℝ) / (64 * (N : ℝ) ^ 2)) = (P : ℝ) / (64 * (N : ℝ)) := by field_simp
    exact he ▸ hh
  have hexponent : E + Real.logb 2 m < (1 - returnTailEta N) * P := by
    have hgap : (0 : ℝ) < P / (64 * (N : ℝ)) := by positivity
    change (P : ℝ) - ((P : ℝ) / (4 * (N : ℝ)) - 3 * (N : ℝ) * d * b - a) +
      (N : ℝ) * q + Real.logb 2 m < _
    unfold returnTailEta
    ring_nf at hgeometry hconstant hm hcontroller hgap ⊢
    nlinarith
  have hf := prefix_product_bound M (by omega) hb ha (hd2.trans hdP) hc hq hA D correct
  have hmp : (0 : ℝ) < m := by exact_mod_cast replayMetadataSize_pos (k := 1) (T := T) (W := W) (N := N) (by omega)
  have heq : (m : ℝ) * (2 : ℝ) ^ E = (2 : ℝ) ^ (E + Real.logb 2 m) := by
    conv_rhs => rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hmp]
    ring
  change (D.card : ℝ) ≤ (m : ℝ) * (2 : ℝ) ^ E at hf
  rw [heq] at hf
  exact hf.trans_lt (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexponent)

end AdaptiveTransfer.Enlarged

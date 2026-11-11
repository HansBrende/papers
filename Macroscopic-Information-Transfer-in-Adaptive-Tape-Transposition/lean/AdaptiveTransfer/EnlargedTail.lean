import AdaptiveTransfer.EnlargedFinite
import AdaptiveTransfer.GetterTail

/-! Uniform small-controller tail for the entire enlarged transition. -/

namespace AdaptiveTransfer.Enlarged
open Transpose MergeDepth NativeRelations Finset Getter

universe u v w

theorem macroscopic_tail (a p : ℕ) {c : ℝ} (ha : 1 ≤ a) (hp : 1 ≤ p) (hc : 1 ≤ c) :
    let N := portRunCap a p c
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b →
      ∀ (Q : Type u) (Γ : Type v) (Λ : Type w) [Fintype Q] [Fintype Γ] [Fintype Λ],
      ∀ q z R : ℕ, Fintype.card Q ≤ 2 ^ q → Fintype.card Λ ≤ 2 ^ z → Fintype.card Γ ≤ 2 ^ a →
        (q : ℝ) ≤ (d * d * b : ℕ) / (64 * (N : ℝ) ^ 2) →
        (z : ℝ) ≤ (d * d * b : ℕ) / (64 * (N : ℝ)) → R ≤ (d * d * b) / (8 * p * N) →
      ∀ (M : System Q Γ Λ 1 p R) (D : Finset (Fin (d * d * b) → Bool)),
        (∀ X : D, ∃ label, M.OutputBy (tposOf d b) (returnTime (d * d * b) c) X.val label) →
        (D.card : ℝ) < (2 : ℝ) ^ ((1 - returnTailEta N) * (d * d * b : ℕ)) := by
  let N := portRunCap a p c
  have hN : 1 ≤ N := by dsimp [N, portRunCap]; omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨P₀, hmeta⟩ := port_metadata_logb_small 1 p N ⌈c⌉₊ (by omega)
    (show (0 : ℝ) < 1 / (64 * (N : ℝ)) by positivity)
  let d₀ := 4 * p + 2 + 192 * N ^ 2 + P₀ + 64 * N * a
  refine ⟨d₀, ?_⟩
  intro d hd b hb Q Γ Λ _ _ _ q z R hq hz hA hqbudget hzbudget hR M D correct
  have hd2 : 2 ≤ d := by dsimp [d₀] at hd; omega
  have hdp : 4 * p ≤ d := by dsimp [d₀] at hd; omega
  have hdN : 192 * N ^ 2 ≤ d := by dsimp [d₀] at hd; omega
  have hdP₀ : P₀ ≤ d := by dsimp [d₀] at hd; omega
  have hda : 64 * N * a ≤ d := by dsimp [d₀] at hd; omega
  let P := d * d * b
  let T := returnTime P c
  let W := portSlabWidth P a p c
  let m := portMetadataSize 1 p T W N
  let E : ℝ := (P : ℝ) - portSaving d b a p c + z + (N : ℝ) * q
  have hdP : d ≤ P := by dsimp [P]; nlinarith
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hm : Real.logb 2 m ≤ (P : ℝ) / (64 * (N : ℝ)) := by
    simpa only [one_div_mul_eq_div] using hmeta P T W (hdP₀.trans hdP)
      (returnTime_le_integer_linear (by linarith)) (portSlabWidth_le_length_add_one ha hp hc)
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
  change (z : ℝ) ≤ (P : ℝ) / (64 * (N : ℝ)) at hzbudget
  have hexponent : E + Real.logb 2 m < (1 - returnTailEta N) * P := by
    have hgap : (0 : ℝ) < P / (64 * (N : ℝ)) := by positivity
    change (P : ℝ) - ((P : ℝ) / (4 * (N : ℝ)) - 3 * (N : ℝ) * d * b - a) + z +
      (N : ℝ) * q + Real.logb 2 m < _
    unfold returnTailEta
    ring_nf at hgeometry hconstant hm hcontroller hzbudget hgap ⊢
    nlinarith
  have hf := product_bound M (by omega) hb ha hp (hdp.trans hdP) hc hR hq hz hA D correct
  have hmp : (0 : ℝ) < m := by exact_mod_cast portMetadataSize_pos (k := 1) (p := p) (T := T) (W := W) (N := N) (by omega)
  have heq : (m : ℝ) * (2 : ℝ) ^ E = (2 : ℝ) ^ (E + Real.logb 2 m) := by
    conv_rhs => rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hmp]
    ring
  change (D.card : ℝ) ≤ (m : ℝ) * (2 : ℝ) ^ E at hf
  rw [heq] at hf
  exact hf.trans_lt (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexponent)

end AdaptiveTransfer.Enlarged

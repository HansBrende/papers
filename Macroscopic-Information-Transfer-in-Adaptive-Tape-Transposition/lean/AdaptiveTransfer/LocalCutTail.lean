import AdaptiveTransfer.NativeSlabCutCounting
import AdaptiveTransfer.ReturnTail

/-! The exact localized native bound has a uniform small-density exponential
tail. The threshold works for every positive entry width; all original
valid chunks and free-head choices are counted in one bad event. -/

namespace AdaptiveTransfer
open Transpose MergeDepth NativeRelations Finset

/-- Fixed controller and alphabet resources, epsilon from the macroscopic
return theorem, eta=1/(8N), and one positive original-cut density. -/
theorem native_local_cut_tail (k a q : ℕ) {c : ℝ}
    (hk : 1 ≤ k) (ha : 1 ≤ a) (hc : 1 ≤ c) :
    let N := slabRunCap a c
    ∃ lam : ℝ, 0 < lam ∧ ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b →
      ∀ (M : TM), M.k = k → M.q + 1 ≤ 2 ^ q → M.g + 1 ≤ 2 ^ a →
      ((nativeBadSlabCuts M d b a c ⌊returnTailEpsilon k a N * (d * d * b : ℕ)⌋₊
        ⌊lam * (d * d * b : ℕ)⌋₊).card : ℝ) <
          (2 : ℝ) ^ ((1 - returnTailEta N) * (d * d * b : ℕ)) := by
  classical
  let N := slabRunCap a c
  have hN : 1 ≤ N := by dsimp [N, slabRunCap]; omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨lam, hlam, P₁, hmenu⟩ := geometry_cut_menus_logb_small k (q + k * a + 2) N
    (max 1 ⌈c⌉₊) (le_max_left _ _) (show (0 : ℝ) < 1 / (32 * (N : ℝ)) by positivity)
  obtain ⟨P₀, hmeta⟩ := native_metadata_logb_small k N a hk ha hc
    (show (0 : ℝ) < 1 / (96 * (N : ℝ)) by positivity)
  let K := a + a * (k - 1) * N + N * q
  let d₀ := 2 + 288 * N ^ 2 + P₀ + P₁ + 96 * N * K
  refine ⟨lam, hlam, d₀, ?_⟩
  intro d hd b hb M hMk hq hA
  have hd2 : 2 ≤ d := by dsimp [d₀] at hd; omega
  have hdN : 288 * N ^ 2 ≤ d := by dsimp [d₀] at hd; omega
  have hdP₀ : P₀ ≤ d := by dsimp [d₀] at hd; omega
  have hdP₁ : P₁ ≤ d := by dsimp [d₀] at hd; omega
  have hdK : 96 * N * K ≤ d := by dsimp [d₀] at hd; omega
  let P := d * d * b
  have hdP : d ≤ P := by dsimp [P]; nlinarith
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  let H := ⌊returnTailEpsilon k a N * (P : ℝ)⌋₊
  let r := ⌊lam * (P : ℝ)⌋₊
  let m := replayMetadataSize k (returnTime P c) (slabWidth P a c) N
  let l := localCutMenu k (q + k * a + 2) P (returnTime P c) N r
  have hH : (H : ℝ) ≤ returnTailEpsilon k a N * P := Nat.floor_le (by
    exact mul_nonneg (returnTailEpsilon_pos ha hN).le hPr.le)
  have hr : (r : ℝ) ≤ lam * P := Nat.floor_le (by positivity)
  have ht : returnTime P c ≤ max 1 ⌈c⌉₊ * (P + 1) :=
    (returnTime_le_integer_linear (by linarith)).trans (Nat.mul_le_mul_right _ (le_max_right _ _))
  have hl : Real.logb 2 (l : ℕ) ≤ (P : ℝ) / (32 * (N : ℝ)) := by
    simpa only [one_div_mul_eq_div] using (hmenu P (returnTime P c) r (hdP₁.trans hdP) ht hr).2
  have hm : Real.logb 2 (m : ℕ) ≤ (P : ℝ) / (96 * (N : ℝ)) := by
    simpa only [one_div_mul_eq_div] using hmeta P (hdP₀.trans hdP)
  have hgeometry : 3 * (N : ℝ) * d * b ≤ (P : ℝ) / (96 * (N : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 96 * (N : ℝ))).mpr
    have hdn : 288 * (N : ℝ) ^ 2 ≤ d := by exact_mod_cast hdN
    have hh := mul_le_mul_of_nonneg_right hdn (show 0 ≤ (d : ℝ) * b by positivity)
    dsimp [P]
    push_cast
    nlinarith
  have hconstant : (a : ℝ) + (a : ℝ) * (k - 1 : ℕ) * N + (N : ℝ) * q ≤
      (P : ℝ) / (96 * (N : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 96 * (N : ℝ))).mpr
    have hh : 96 * (N : ℝ) * ((a : ℝ) + (a : ℝ) * (k - 1 : ℕ) * N + (N : ℝ) * q) ≤ P := by
      exact_mod_cast hdK.trans hdP
    nlinarith
  have hw := return_window_budget ha hN hH
  have hfinite := native_bad_slab_cut_bound (M := M) (d := d) (b := b)
    (a := a) (q := q) (H := H) (r := r) (c := c) hq hA
  rw [hMk] at hfinite
  have hmpos : (0 : ℝ) < (m : ℕ) := by
    exact_mod_cast replayMetadataSize_pos (T := returnTime P c) (W := slabWidth P a c) (N := N) hk
  have hlpos : (0 : ℝ) < (l : ℕ) := by exact_mod_cast localCutMenu_pos k (q + k * a + 2) P (returnTime P c) N r
  have hexponent : (P : ℝ) - slabSaving d b a c + (N : ℝ) * q +
      (a : ℝ) * (k - 1 : ℕ) * N * (2 * H + 1) + Real.logb 2 m + Real.logb 2 l <
      (1 - returnTailEta N) * P := by
    have hgap : (0 : ℝ) < P / (32 * (N : ℝ)) := by positivity
    change (P : ℝ) - ((P : ℝ) / (4 * (N : ℝ)) - 3 * (N : ℝ) * d * b - a) +
      (N : ℝ) * q + (a : ℝ) * (k - 1 : ℕ) * N * (2 * H + 1) + Real.logb 2 m +
        Real.logb 2 l < (1 - 1 / (8 * (N : ℝ))) * P
    ring_nf at hgeometry hconstant hm hw hl hgap ⊢
    nlinarith
  have heq : (m : ℝ) * ((2 : ℝ) ^ ((P : ℝ) - slabSaving d b a c + (N : ℝ) * q +
        (a : ℝ) * (k - 1 : ℕ) * N * (2 * H + 1)) * (l : ℝ)) =
      (2 : ℝ) ^ ((P : ℝ) - slabSaving d b a c + (N : ℝ) * q +
        (a : ℝ) * (k - 1 : ℕ) * N * (2 * H + 1) + Real.logb 2 m + Real.logb 2 l) := by
    symm
    rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num),
      Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hmpos,
      Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hlpos]
    ring
  change ((nativeBadSlabCuts M d b a c H r).card : ℝ) ≤ _ at hfinite
  rw [heq] at hfinite
  exact hfinite.trans_lt (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexponent)

end AdaptiveTransfer

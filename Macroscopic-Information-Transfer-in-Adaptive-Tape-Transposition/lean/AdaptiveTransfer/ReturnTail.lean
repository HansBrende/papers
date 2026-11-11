import AdaptiveTransfer.MetadataRates

/-! Macroscopic-return exponential tails with a dimension threshold uniform
in every positive entry width. All sparse, geometry and controller costs
are bounded quantitatively before applying the actual native finite theorem. -/

namespace AdaptiveTransfer
open Transpose MergeDepth NativeRelations Finset LeanMachine

noncomputable def returnTailEpsilon (k a N : ℕ) : ℝ :=
  1 / (64 * (a : ℝ) * (max 1 (k - 1) : ℕ) * (N : ℝ) ^ 2)

noncomputable def returnTailEta (N : ℕ) : ℝ := 1 / (8 * (N : ℝ))

theorem returnTailEpsilon_pos {k a N : ℕ} (ha : 1 ≤ a) (hN : 1 ≤ N) :
    0 < returnTailEpsilon k a N := by
  unfold returnTailEpsilon
  have hm : 0 < max 1 (k - 1) := by omega
  positivity

theorem returnTailEta_pos {N : ℕ} (hN : 1 ≤ N) : 0 < returnTailEta N := by
  unfold returnTailEta
  positivity

/-- The proportional part of all entry-window costs is at most P/(32N). -/
theorem return_window_budget {k a N P H : ℕ} (ha : 1 ≤ a) (hN : 1 ≤ N)
    (hH : (H : ℝ) ≤ returnTailEpsilon k a N * P) :
    (a : ℝ) * (k - 1 : ℕ) * N * (2 * H + 1) ≤
      (P : ℝ) / (32 * (N : ℝ)) + (a : ℝ) * (k - 1 : ℕ) * N := by
  have hap : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hNp : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hmp : ((max 1 (k - 1) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : max 1 (k - 1) ≠ 0)
  have hcoef : 2 * (a : ℝ) * (k - 1 : ℕ) * N * returnTailEpsilon k a N ≤
      1 / (32 * (N : ℝ)) := by
    calc
      _ ≤ 2 * (a : ℝ) * (max 1 (k - 1) : ℕ) * N * returnTailEpsilon k a N := by
        gcongr
        · exact (returnTailEpsilon_pos ha hN).le
        · exact_mod_cast le_max_right 1 (k - 1)
      _ = _ := by unfold returnTailEpsilon; field_simp; ring
  have hw := mul_le_mul_of_nonneg_left hH
    (show 0 ≤ 2 * (a : ℝ) * (k - 1 : ℕ) * N by positivity)
  have hp := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg P)
  ring_nf at hw hp ⊢
  nlinarith

noncomputable def nativeBadInputs (M : TM) (d b : ℕ) (c : ℝ) (H J : ℕ) :
    Finset (Fin (d * d * b) → Bool) := by
  classical
  exact univ.filter fun X => TransposesInput M d b c X ∧ ∃ f : Fin M.k,
    (offCarrierReturns (trace M (List.ofFn X)).work f (trace M (List.ofFn X)).haltTime H).card ≤ J

/-- The exact constants of the macroscopic-return theorem: epsilon is the
stated reciprocal, eta=1/(8N), and one positive density and dimension threshold
work for every b>=1 and every individual machine in the state budget. -/
theorem native_macroscopic_return_tail (k a : ℕ) {c : ℝ}
    (hk : 1 ≤ k) (ha : 1 ≤ a) (hc : 1 ≤ c) :
    let N := slabRunCap a c
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 / 2 ∧ ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b →
      ∀ (M : TM), M.k = k → ∀ q : ℕ, M.q + 1 ≤ 2 ^ q → M.g + 1 ≤ 2 ^ a →
        (q : ℝ) ≤ (d * d * b : ℕ) / (64 * (N : ℝ) ^ 2) →
      ((nativeBadInputs M d b c ⌊returnTailEpsilon k a N * (d * d * b : ℕ)⌋₊
        ⌊γ * (d * d * b : ℕ)⌋₊).card : ℝ) <
          (2 : ℝ) ^ ((1 - returnTailEta N) * (d * d * b : ℕ)) := by
  classical
  let N := slabRunCap a c
  have hN : 1 ≤ N := by dsimp [N, slabRunCap]; omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨δ, hδ, hsparse⟩ := native_sparse_logb_small k (2 ^ a)
    (show 0 < c by linarith) (show (0 : ℝ) < 1 / (32 * (N : ℝ)) by positivity)
  let γ := min δ (1 / 2)
  have hγ : 0 < γ := lt_min hδ (by norm_num)
  obtain ⟨P₀, hmeta⟩ := native_metadata_logb_small k N a hk ha hc
    (show (0 : ℝ) < 1 / (192 * (N : ℝ)) by positivity)
  let K := a + a * (k - 1) * N
  let d₀ := 2 + 576 * N ^ 2 + P₀ + 192 * N * K
  refine ⟨γ, hγ, min_le_right _ _, d₀, ?_⟩
  intro d hd b hb M hMk q hq hA hqbudget
  have hd2 : 2 ≤ d := by dsimp [d₀] at hd; omega
  have hdN : 576 * N ^ 2 ≤ d := by dsimp [d₀] at hd; omega
  have hdP₀ : P₀ ≤ d := by dsimp [d₀] at hd; omega
  have hdK : 192 * N * K ≤ d := by dsimp [d₀] at hd; omega
  let P := d * d * b
  have hdP : d ≤ P := by dsimp [P]; nlinarith
  have hP : 2 ≤ P := hd2.trans hdP
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  let H := ⌊returnTailEpsilon k a N * (P : ℝ)⌋₊
  let J := ⌊γ * (P : ℝ)⌋₊
  let D := nativeBadInputs M d b c H J
  have hH : (H : ℝ) ≤ returnTailEpsilon k a N * P := Nat.floor_le (by
    exact mul_nonneg (returnTailEpsilon_pos ha hN).le hPr.le)
  have hJ : (J : ℝ) ≤ δ * P := (Nat.floor_le (by positivity : 0 ≤ γ * (P : ℝ))).trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hPr.le)
  have hs : Real.logb 2 (returnSparseMenu k (returnTime P c) J (M.g + 1) : ℕ) ≤
      (P : ℝ) / (32 * (N : ℝ)) := by
    simpa only [one_div_mul_eq_div] using hsparse P J (M.g + 1) (by omega) hA hJ
  have hm : Real.logb 2 (replayMetadataSize k (returnTime P c) (slabWidth P a c) N : ℕ) ≤
      (P : ℝ) / (192 * (N : ℝ)) := by
    simpa only [one_div_mul_eq_div] using hmeta P (hdP₀.trans hdP)
  have hgeometry : 3 * (N : ℝ) * d * b ≤ (P : ℝ) / (192 * (N : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 192 * (N : ℝ))).mpr
    have hdn : 576 * (N : ℝ) ^ 2 ≤ d := by exact_mod_cast hdN
    have hh := mul_le_mul_of_nonneg_right hdn (show 0 ≤ (d : ℝ) * b by positivity)
    dsimp [P]
    push_cast
    nlinarith
  have hconstant : (a : ℝ) + (a : ℝ) * (k - 1 : ℕ) * N ≤
      (P : ℝ) / (192 * (N : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 192 * (N : ℝ))).mpr
    have hh : 192 * (N : ℝ) * ((a : ℝ) + (a : ℝ) * (k - 1 : ℕ) * N) ≤ P := by
      exact_mod_cast hdK.trans hdP
    nlinarith
  have hw := return_window_budget ha hN hH
  have hcontroller : (N : ℝ) * q ≤ (P : ℝ) / (64 * (N : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hqbudget hNr.le
    have he : (N : ℝ) * ((P : ℝ) / (64 * (N : ℝ) ^ 2)) =
        (P : ℝ) / (64 * (N : ℝ)) := by field_simp
    exact he ▸ hh
  have hfinite := native_finite_return_bound (M := M) (d := d) (b := b)
    (a := a) (q := q) (H := H) (J := J) (c := c) (by omega) hb hP
    (by simpa only [hMk] using hk) ha hc hq hA D
    (fun X => (mem_filter.mp X.property).2.1)
    (fun X => (mem_filter.mp X.property).2.2)
  dsimp only at hfinite
  rw [hMk] at hfinite
  have hexponent : (P : ℝ) - (P : ℝ) / (4 * (N : ℝ)) +
      (3 * (N : ℝ) * d * b + a + (a : ℝ) * (k - 1 : ℕ) * N * (2 * H + 1) +
        (N : ℝ) * q + Real.logb 2 (replayMetadataSize k (returnTime P c) (slabWidth P a c) N) +
          Real.logb 2 (returnSparseMenu k (returnTime P c) J (M.g + 1))) <
      (1 - returnTailEta N) * P := by
    have hgap : (0 : ℝ) < P / (32 * (N : ℝ)) := by positivity
    unfold returnTailEta
    ring_nf at hgeometry hconstant hm hw hcontroller hs hgap ⊢
    nlinarith
  exact hfinite.trans_lt (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexponent)

end AdaptiveTransfer

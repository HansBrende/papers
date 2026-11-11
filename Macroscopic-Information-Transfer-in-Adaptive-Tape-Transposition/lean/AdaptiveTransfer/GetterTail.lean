import AdaptiveTransfer.GetterSparse
import AdaptiveTransfer.ReturnTail

/-! The stated discrepancy tail with its explicit density inequality.
The length threshold precedes quantification over all source tables,
observers, labels and getters within the declared budgets.
-/

namespace AdaptiveTransfer.Getter
open Transpose MergeDepth NativeRelations Finset LeanMachine

universe u w

noncomputable def getterTailEpsilon (k a N : ℕ) : ℝ :=
  1 / (128 * (a : ℝ) * (max 1 (k - 1) : ℕ) * (N : ℝ) ^ 2)

theorem getterTailEpsilon_pos {k a N : ℕ} (ha : 1 ≤ a) (hN : 1 ≤ N) :
    0 < getterTailEpsilon k a N := by
  unfold getterTailEpsilon
  have hm : 0 < max 1 (k - 1) := by omega
  positivity

theorem getter_window_budget {k a N P H : ℕ} (ha : 1 ≤ a) (hN : 1 ≤ N)
    (hH : (H : ℝ) ≤ getterTailEpsilon k a N * P) :
    (a : ℝ) * (k - 1 : ℕ) * N * (2 * H + 1) ≤
      (P : ℝ) / (64 * (N : ℝ)) + (a : ℝ) * (k - 1 : ℕ) * N := by
  have hap : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hNp : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hmp : ((max 1 (k - 1) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : max 1 (k - 1) ≠ 0)
  have hcoef : 2 * (a : ℝ) * (k - 1 : ℕ) * N * getterTailEpsilon k a N ≤
      1 / (64 * (N : ℝ)) := by
    calc
      _ ≤ 2 * (a : ℝ) * (max 1 (k - 1) : ℕ) * N * getterTailEpsilon k a N := by
        gcongr
        · exact (getterTailEpsilon_pos ha hN).le
        · exact_mod_cast le_max_right 1 (k - 1)
      _ = _ := by unfold getterTailEpsilon; field_simp; ring
  have hw := mul_le_mul_of_nonneg_left hH
    (show 0 ≤ 2 * (a : ℝ) * (k - 1 : ℕ) * N by positivity)
  have hp := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg P)
  ring_nf at hw hp ⊢
  nlinarith

theorem portSlabWidth_le_length_add_one {P a p : ℕ} {c : ℝ}
    (ha : 1 ≤ a) (hp : 1 ≤ p) (hc : 1 ≤ c) : portSlabWidth P a p c ≤ P + 1 := by
  apply Nat.ceil_le.mpr
  have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hap : (1 : ℝ) ≤ (a : ℝ) * p := har.trans (le_mul_of_one_le_right (by positivity) hpr)
  have hden : 1 ≤ 320 * (a : ℝ) * p * c := by
    have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ 320 * (a : ℝ) * p by positivity)
    nlinarith
  exact (div_le_self (Nat.cast_nonneg P) hden).trans (by norm_num)

/-- Every density satisfying the written explicit condition gives the stated
tail, with one dimension threshold for all positive widths and all systems
in the resource budgets. -/
theorem native_macroscopic_getter_tail (k a v : ℕ) {c γ : ℝ}
    (hk : 1 ≤ k) (ha : 1 ≤ a) (hc : 1 ≤ c) (hγ : 0 < γ) (hγhalf : γ ≤ 1 / 2)
    (hγbudget : γ * ((a : ℝ) + Real.logb 2 (2 * Real.exp 1 * k * c / γ)) ≤
      1 / (64 * (portRunCap a (v + 1) c : ℝ))) :
    let N := portRunCap a (v + 1) c
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b → ∀ (M : TM), M.k = k →
      ∀ (U : Type u) (Λ : Type w) [Fintype U] [Fintype Λ], ∀ q z R : ℕ,
        (M.q + 1) * Fintype.card U ≤ 2 ^ q → Fintype.card Λ ≤ 2 ^ z → M.g + 1 ≤ 2 ^ a →
        (q : ℝ) ≤ (d * d * b : ℕ) / (64 * (N : ℝ) ^ 2) →
        (z : ℝ) ≤ (d * d * b : ℕ) / (64 * (N : ℝ)) →
        R ≤ (d * d * b) / (8 * (v + 1) * N) →
      ∀ (A : Observer M U v R) (G : Fin M.k → Getters M U Λ v R)
        (D : Finset (Fin (d * d * b) → Bool)),
        (∀ X : D, TransposesInput M d b c X.val) →
        (∀ X : D, ∃ f : Fin M.k, ∃ label : Λ,
          (nativeErrors A (G f) f label (List.ofFn X.val) (trace M (List.ofFn X.val)).haltTime
            ⌊getterTailEpsilon k a N * (d * d * b : ℕ)⌋₊).card ≤ ⌊γ * (d * d * b : ℕ)⌋₊) →
        (D.card : ℝ) < (2 : ℝ) ^ ((1 - returnTailEta N) * (d * d * b : ℕ)) := by
  let N := portRunCap a (v + 1) c
  have hN : 1 ≤ N := by dsimp [N, portRunCap]; omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨P₀, hmeta⟩ := port_metadata_logb_small k (v + 1) N ⌈c⌉₊ hk
    (show (0 : ℝ) < 1 / (192 * (N : ℝ)) by positivity)
  let K := a + a * (k - 1) * N
  let d₀ := 4 * (v + 1) + 2 + 576 * N ^ 2 + P₀ + 192 * N * K
  refine ⟨d₀, ?_⟩
  intro d hd b hb M hMk U Λ _ _ q z R hq hz hA hqbudget hzbudget hR A G D correct errors
  have hd2 : 2 ≤ d := by dsimp [d₀] at hd; omega
  have hdp : 4 * (v + 1) ≤ d := by dsimp [d₀] at hd; omega
  have hdN : 576 * N ^ 2 ≤ d := by dsimp [d₀] at hd; omega
  have hdP₀ : P₀ ≤ d := by dsimp [d₀] at hd; omega
  have hdK : 192 * N * K ≤ d := by dsimp [d₀] at hd; omega
  let P := d * d * b
  have hdP : d ≤ P := by dsimp [P]; nlinarith
  have hP : 4 * (v + 1) ≤ P := hdp.trans hdP
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  let H := ⌊getterTailEpsilon k a N * (P : ℝ)⌋₊
  let J := ⌊γ * (P : ℝ)⌋₊
  have hH : (H : ℝ) ≤ getterTailEpsilon k a N * P := Nat.floor_le
    (mul_nonneg (getterTailEpsilon_pos ha hN).le hPr.le)
  have hJ : (J : ℝ) ≤ γ * P := Nat.floor_le (by positivity)
  have hs : Real.logb 2 (returnSparseMenu k (returnTime P c) J (M.g + 1) : ℕ) ≤
      (P : ℝ) / (64 * (N : ℝ)) := getter_sparse_budget hk (by omega) hc hγ hγhalf hA hJ hγbudget
  have hm : Real.logb 2 (portMetadataSize k (v + 1) (returnTime P c) (portSlabWidth P a (v + 1) c) N : ℕ) ≤
      (P : ℝ) / (192 * (N : ℝ)) := by
    simpa only [one_div_mul_eq_div] using hmeta P _ _ (hdP₀.trans hdP)
      (returnTime_le_integer_linear (by linarith)) (portSlabWidth_le_length_add_one ha (by omega) hc)
  have hgeometry : 3 * (N : ℝ) * d * b ≤ (P : ℝ) / (192 * (N : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 192 * (N : ℝ))).mpr
    have hh := mul_le_mul_of_nonneg_right (show 576 * (N : ℝ) ^ 2 ≤ d by exact_mod_cast hdN)
      (show 0 ≤ (d : ℝ) * b by positivity)
    dsimp [P]; push_cast; nlinarith
  have hconstant : (a : ℝ) + (a : ℝ) * (k - 1 : ℕ) * N ≤ (P : ℝ) / (192 * (N : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 192 * (N : ℝ))).mpr
    have hh : 192 * (N : ℝ) * ((a : ℝ) + (a : ℝ) * (k - 1 : ℕ) * N) ≤ P := by
      exact_mod_cast hdK.trans hdP
    nlinarith
  have hw := getter_window_budget ha hN hH
  have hcontroller : (N : ℝ) * q ≤ (P : ℝ) / (64 * (N : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hqbudget hNr.le
    have he : (N : ℝ) * ((P : ℝ) / (64 * (N : ℝ) ^ 2)) = (P : ℝ) / (64 * (N : ℝ)) := by field_simp
    exact he ▸ hh
  change (z : ℝ) ≤ (P : ℝ) / (64 * (N : ℝ)) at hzbudget
  have hfinite := native_finite_getter_bound (M := M) (d := d) (b := b) (a := a)
    (q := q) (z := z) (H := H) (J := J) (c := c) (by omega) hb ha
    (by simpa only [hMk] using hk) hP hc hR A G hq hz hA D correct errors
  dsimp only at hfinite
  rw [hMk] at hfinite
  have hexponent : (P : ℝ) - (P : ℝ) / (4 * (N : ℝ)) +
      (3 * (N : ℝ) * d * b + a + (a : ℝ) * (k - 1 : ℕ) * N * (2 * H + 1) +
        (N : ℝ) * q + z + Real.logb 2 (portMetadataSize k (v + 1) (returnTime P c) (portSlabWidth P a (v + 1) c) N) +
        Real.logb 2 (returnSparseMenu k (returnTime P c) J (M.g + 1))) <
      (1 - returnTailEta N) * P := by
    have hgap : (0 : ℝ) < P / (64 * (N : ℝ)) := by positivity
    unfold returnTailEta
    ring_nf at hgeometry hconstant hm hw hcontroller hzbudget hs hgap ⊢
    nlinarith
  exact hfinite.trans_lt (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexponent)

end AdaptiveTransfer.Getter

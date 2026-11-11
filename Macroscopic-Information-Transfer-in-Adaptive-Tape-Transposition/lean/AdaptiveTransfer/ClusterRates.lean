import AdaptiveTransfer.ClusterMetadataRates
import AdaptiveTransfer.ClusterGeometry
import AdaptiveTransfer.GeometryMenuRates
import AdaptiveTransfer.ReturnTail

/-! Complete ordinary rate assembly for coherent clusters. The exact
metadata, sparse-import and cut menus are bounded before the dimension
threshold is chosen. These estimates apply to every positive entry width;
native source injections are supplied separately by the replay theorems.
-/

namespace AdaptiveTransfer

theorem clusterRunCap_one_le (k a : ℕ) (c : ℝ) : 1 ≤ clusterRunCap k a c := by
  unfold clusterRunCap slabRunCap
  omega

/-- Exact return-method budgets with a variable controller cost. The one
density and dimension threshold precede every width, controller and actual
alphabet below the fixed bound. -/
theorem cluster_return_rates (k a : ℕ) {c : ℝ}
    (hk : 1 ≤ k) (ha : 1 ≤ a) (hc : 1 ≤ c) :
    let N := clusterRunCap k a c
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 / 2 ∧ ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b →
      let P := d * d * b
      (P : ℝ) / (8 * (N : ℝ)) ≤ clusterSaving d b k a c ∧
      0 < clusterSaving d b k a c ∧
      ∀ q B : ℕ, (q : ℝ) ≤ (P : ℝ) / (64 * (N : ℝ) ^ 2) → B ≤ 2 ^ a →
        (P : ℝ) - clusterSaving d b k a c +
          (a : ℝ) * N * k *
            (max (4 * ⌈clusterEpsilon k a N * P⌉₊ + 2)
              (2 * ⌊clusterEpsilon k a N * P⌋₊ + 1) : ℕ) +
          (N : ℝ) * q +
          Real.logb 2 (clusterMetadataSize k (returnTime P c) (slabWidth P a c) N
            ⌈clusterEpsilon k a N * P⌉₊ : ℕ) +
          Real.logb 2 (returnSparseMenu k (returnTime P c) ⌊γ * P⌋₊ B : ℕ) <
            (1 - returnTailEta N) * P := by
  let N := clusterRunCap k a c
  have hN : 1 ≤ N := clusterRunCap_one_le k a c
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨δ, hδ, hsparse⟩ := native_sparse_logb_small k (2 ^ a)
    (show 0 < c by linarith) (show (0 : ℝ) < 1 / (32 * (N : ℝ)) by positivity)
  let γ := min δ (1 / 2)
  have hγ : 0 < γ := lt_min hδ (by norm_num)
  obtain ⟨P₀, hmeta⟩ := native_cluster_metadata_logb_small k N a hk hN ha hc
    (show (0 : ℝ) < 1 / (192 * (N : ℝ)) by positivity)
  let K := a * (k + 1) + 6 * a * N * k
  let d₀ := 2 + 576 * N ^ 2 + P₀ + 192 * N * K
  refine ⟨γ, hγ, min_le_right _ _, d₀, ?_⟩
  intro d hd b hb
  have hd2 : 2 ≤ d := by dsimp [d₀] at hd; omega
  have hdN : 3 * 192 * N ^ 2 ≤ d := by dsimp [d₀] at hd; omega
  have hdP₀ : P₀ ≤ d := by dsimp [d₀] at hd; omega
  have hdK : 192 * N * K ≤ d := by dsimp [d₀] at hd; omega
  let P := d * d * b
  have hdP : d ≤ P := by dsimp [P]; nlinarith
  have hP : 2 ≤ P := hd2.trans hdP
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hgeometry : 3 * (N : ℝ) * d * b ≤ (P : ℝ) / (192 * (N : ℝ)) :=
    cluster_geometry_budget (by norm_num) hN hdN
  have hconstant : (a : ℝ) * (k + 1) + 6 * a * N * k ≤
      (P : ℝ) / (192 * (N : ℝ)) := by
    simpa only [P, K, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      cluster_constant_budget (by norm_num : 1 ≤ 192) hN (by omega) hb hdK
  have hm : Real.logb 2 (clusterMetadataSize k (returnTime P c) (slabWidth P a c) N
      ⌈clusterEpsilon k a N * P⌉₊ : ℕ) ≤ (P : ℝ) / (192 * (N : ℝ)) := by
    simpa only [one_div_mul_eq_div] using hmeta P (hdP₀.trans hdP)
  have hsave : (P : ℝ) / (8 * (N : ℝ)) ≤ clusterSaving d b k a c := by
    change (P : ℝ) / (8 * (N : ℝ)) ≤ (P : ℝ) / (4 * (N : ℝ)) -
      3 * (N : ℝ) * d * b - (a : ℝ) * (k + 1)
    have hn : (0 : ℝ) ≤ 6 * a * N * k := by positivity
    have hp : (0 : ℝ) ≤ P / (N : ℝ) := by positivity
    ring_nf at hgeometry hconstant hp ⊢
    nlinarith
  have hsavepos : 0 < clusterSaving d b k a c :=
    (show (0 : ℝ) < P / (8 * (N : ℝ)) by positivity).trans_le hsave
  refine ⟨hsave, hsavepos, ?_⟩
  intro q B hq hB
  have hJ : (⌊γ * (P : ℝ)⌋₊ : ℝ) ≤ δ * P :=
    (Nat.floor_le (by positivity : 0 ≤ γ * (P : ℝ))).trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hPr.le)
  have hs : Real.logb 2 (returnSparseMenu k (returnTime P c) ⌊γ * P⌋₊ B : ℕ) ≤
      (P : ℝ) / (32 * (N : ℝ)) := by
    simpa only [one_div_mul_eq_div] using hsparse P _ B (by omega) hB hJ
  have hw := cluster_window_budget hk ha hN P
  have hcontroller : (N : ℝ) * q ≤ (P : ℝ) / (64 * (N : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hq hNr.le
    have he : (N : ℝ) * ((P : ℝ) / (64 * (N : ℝ) ^ 2)) =
        (P : ℝ) / (64 * (N : ℝ)) := by field_simp
    exact he ▸ hh
  change (P : ℝ) - ((P : ℝ) / (4 * (N : ℝ)) - 3 * (N : ℝ) * d * b -
    (a : ℝ) * (k + 1)) + (a : ℝ) * N * k *
      (max (4 * ⌈clusterEpsilon k a N * P⌉₊ + 2)
        (2 * ⌊clusterEpsilon k a N * P⌋₊ + 1) : ℕ) + (N : ℝ) * q +
      Real.logb 2 (clusterMetadataSize k (returnTime P c) (slabWidth P a c) N
        ⌈clusterEpsilon k a N * P⌉₊ : ℕ) +
      Real.logb 2 (returnSparseMenu k (returnTime P c) ⌊γ * P⌋₊ B : ℕ) <
        (1 - returnTailEta N) * P
  have hgap : (0 : ℝ) < P / (32 * (N : ℝ)) := by positivity
  unfold returnTailEta
  ring_nf at hgeometry hconstant hm hw hcontroller hs hgap ⊢
  nlinarith

/-- Local-cut budgets at fixed controller width. The cut density may
depend on that width; the dimension threshold still precedes every b≥1. -/
theorem cluster_cut_rates (k a q : ℕ) {c : ℝ}
    (hk : 1 ≤ k) (ha : 1 ≤ a) (hc : 1 ≤ c) :
    let N := clusterRunCap k a c
    ∃ δ : ℝ, 0 < δ ∧ ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b →
      let P := d * d * b
      (P : ℝ) / (8 * (N : ℝ)) ≤ clusterSaving d b k a c ∧
      0 < clusterSaving d b k a c ∧
      (P : ℝ) - clusterSaving d b k a c +
        (a : ℝ) * N * k *
          (max (4 * ⌈clusterEpsilon k a N * P⌉₊ + 2)
            (2 * ⌊clusterEpsilon k a N * P⌋₊ + 1) : ℕ) +
        (N : ℝ) * q +
        Real.logb 2 (clusterMetadataSize k (returnTime P c) (slabWidth P a c) N
          ⌈clusterEpsilon k a N * P⌉₊ : ℕ) +
        Real.logb 2 (localCutMenu k (q + k * a + 2) P (returnTime P c) N ⌊δ * P⌋₊ : ℕ) <
          (1 - returnTailEta N) * P := by
  let N := clusterRunCap k a c
  have hN : 1 ≤ N := clusterRunCap_one_le k a c
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let C := max 1 ⌈c⌉₊
  obtain ⟨δ, hδ, P₁, hcut⟩ := geometry_cut_menus_logb_small k (q + k * a + 2) N C
    (by dsimp [C]; omega) (show (0 : ℝ) < 1 / (32 * (N : ℝ)) by positivity)
  obtain ⟨P₀, hmeta⟩ := native_cluster_metadata_logb_small k N a hk hN ha hc
    (show (0 : ℝ) < 1 / (96 * (N : ℝ)) by positivity)
  let K := a * (k + 1) + 6 * a * N * k + N * q
  let d₀ := 2 + 288 * N ^ 2 + P₀ + P₁ + 96 * N * K
  refine ⟨δ, hδ, d₀, ?_⟩
  intro d hd b hb
  have hd2 : 2 ≤ d := by dsimp [d₀] at hd; omega
  have hdN : 3 * 96 * N ^ 2 ≤ d := by dsimp [d₀] at hd; omega
  have hdP₀ : P₀ ≤ d := by dsimp [d₀] at hd; omega
  have hdP₁ : P₁ ≤ d := by dsimp [d₀] at hd; omega
  have hdK : 96 * N * K ≤ d := by dsimp [d₀] at hd; omega
  let P := d * d * b
  have hdP : d ≤ P := by dsimp [P]; nlinarith
  have hP : 2 ≤ P := hd2.trans hdP
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hgeometry : 3 * (N : ℝ) * d * b ≤ (P : ℝ) / (96 * (N : ℝ)) :=
    cluster_geometry_budget (by norm_num) hN hdN
  have hconstant : (a : ℝ) * (k + 1) + 6 * a * N * k + (N : ℝ) * q ≤
      (P : ℝ) / (96 * (N : ℝ)) := by
    simpa only [P, K, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      cluster_constant_budget (by norm_num : 1 ≤ 96) hN (by omega) hb hdK
  have hm : Real.logb 2 (clusterMetadataSize k (returnTime P c) (slabWidth P a c) N
      ⌈clusterEpsilon k a N * P⌉₊ : ℕ) ≤ (P : ℝ) / (96 * (N : ℝ)) := by
    simpa only [one_div_mul_eq_div] using hmeta P (hdP₀.trans hdP)
  have hsave : (P : ℝ) / (8 * (N : ℝ)) ≤ clusterSaving d b k a c := by
    change (P : ℝ) / (8 * (N : ℝ)) ≤ (P : ℝ) / (4 * (N : ℝ)) -
      3 * (N : ℝ) * d * b - (a : ℝ) * (k + 1)
    have hn : (0 : ℝ) ≤ 6 * a * N * k + (N : ℝ) * q := by positivity
    have hp : (0 : ℝ) ≤ P / (N : ℝ) := by positivity
    ring_nf at hgeometry hconstant hp ⊢
    nlinarith
  have hsavepos : 0 < clusterSaving d b k a c :=
    (show (0 : ℝ) < P / (8 * (N : ℝ)) by positivity).trans_le hsave
  refine ⟨hsave, hsavepos, ?_⟩
  have htime : returnTime P c ≤ C * (P + 1) :=
    (returnTime_le_integer_linear (by linarith)).trans
      (Nat.mul_le_mul_right _ (Nat.le_max_right 1 ⌈c⌉₊))
  have hs : Real.logb 2 (localCutMenu k (q + k * a + 2) P (returnTime P c) N ⌊δ * P⌋₊ : ℕ) ≤
      (P : ℝ) / (32 * (N : ℝ)) := by
    simpa only [one_div_mul_eq_div] using
      (hcut P (returnTime P c) ⌊δ * P⌋₊ (hdP₁.trans hdP) htime
        (Nat.floor_le (by positivity : 0 ≤ δ * (P : ℝ)))).2
  have hw := cluster_window_budget hk ha hN P
  change (P : ℝ) - ((P : ℝ) / (4 * (N : ℝ)) - 3 * (N : ℝ) * d * b -
    (a : ℝ) * (k + 1)) + (a : ℝ) * N * k *
      (max (4 * ⌈clusterEpsilon k a N * P⌉₊ + 2)
        (2 * ⌊clusterEpsilon k a N * P⌋₊ + 1) : ℕ) + (N : ℝ) * q +
      Real.logb 2 (clusterMetadataSize k (returnTime P c) (slabWidth P a c) N
        ⌈clusterEpsilon k a N * P⌉₊ : ℕ) +
      Real.logb 2 (localCutMenu k (q + k * a + 2) P (returnTime P c) N ⌊δ * P⌋₊ : ℕ) <
        (1 - returnTailEta N) * P
  have hgap : (0 : ℝ) < P / (32 * (N : ℝ)) := by positivity
  unfold returnTailEta
  ring_nf at hgeometry hconstant hm hw hs hgap ⊢
  nlinarith

end AdaptiveTransfer

import AdaptiveTransfer.ClusterRates
import AdaptiveTransfer.NativeClusterReturnCounting
import AdaptiveTransfer.NativeClusterCutCounting

/-! All-width tails for the actual native coherent-cluster events. Charts,
slabs and cuts are selected from the original executions by the finite
counting theorems; only the fixed machine resource bounds remain as inputs.
-/

namespace AdaptiveTransfer
open Transpose

private theorem cluster_product_tail {D m l : ℕ} {x y : ℝ}
    (hm : 0 < m) (hl : 0 < l)
    (hfinite : (D : ℝ) ≤ (m : ℝ) * ((2 : ℝ) ^ x * (l : ℝ)))
    (hexponent : x + Real.logb 2 m + Real.logb 2 l < y) :
    (D : ℝ) < (2 : ℝ) ^ y := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  have heq : (m : ℝ) * ((2 : ℝ) ^ x * (l : ℝ)) =
      (2 : ℝ) ^ (x + Real.logb 2 m + Real.logb 2 l) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num),
      Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hmpos,
      Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hlpos]
    ring
  rw [heq] at hfinite
  exact hfinite.trans_lt (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexponent)

/-- One density and dimension threshold cover every positive entry width,
every actual alphabet below the bound, and every controller in the stated
variable state budget. The bad event ranges over all coherent charts. -/
theorem native_cluster_return_tail (k a : ℕ) {c : ℝ}
    (hk : 1 ≤ k) (ha : 1 ≤ a) (hc : 1 ≤ c) :
    let N := clusterRunCap k a c
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 / 2 ∧ ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b →
      ∀ (M : TM), M.k = k → ∀ q : ℕ, M.q + 1 ≤ 2 ^ q → M.g + 1 ≤ 2 ^ a →
        (q : ℝ) ≤ (d * d * b : ℕ) / (64 * (N : ℝ) ^ 2) →
        ((nativeBadClusterReturns M d b c (clusterEpsilon k a N * (d * d * b : ℕ))
          ⌊clusterEpsilon k a N * (d * d * b : ℕ)⌋₊ ⌊γ * (d * d * b : ℕ)⌋₊).card : ℝ) <
          (2 : ℝ) ^ ((1 - returnTailEta N) * (d * d * b : ℕ)) := by
  obtain ⟨γ, hγ, hγhalf, d₀, hrates⟩ := cluster_return_rates k a hk ha hc
  refine ⟨γ, hγ, hγhalf, max 2 d₀, ?_⟩
  intro d hd b hb M hMk q hq hA hqbudget
  have hd2 : 2 ≤ d := (le_max_left _ _).trans hd
  have hP : 2 ≤ d * d * b := by nlinarith
  have hr := hrates d ((le_max_right _ _).trans hd) b hb
  have hsaving : 0 < clusterSaving d b M.k a c := by simpa only [hMk] using hr.2.1
  have hfinite := native_bad_cluster_return_bound (M := M) (d := d) (b := b)
    (a := a) (q := q)
    (H := ⌊clusterEpsilon k a (clusterRunCap k a c) * (d * d * b : ℕ)⌋₊)
    (J := ⌊γ * (d * d * b : ℕ)⌋₊)
    (j := ⌈clusterEpsilon k a (clusterRunCap k a c) * (d * d * b : ℕ)⌉₊)
    (error := clusterEpsilon k a (clusterRunCap k a c) * (d * d * b : ℕ))
    (by omega) hb hP ha hc hq hA hsaving (Nat.le_ceil _)
  rw [hMk] at hfinite
  apply cluster_product_tail (clusterMetadataSize_pos ..) (returnSparseMenu_pos ..) hfinite
  have he := hr.2.2 q (M.g + 1) hqbudget hA
  convert he using 1
  ring

/-- At fixed controller width, one positive cut density and dimension
threshold cover every positive entry width and every original native cut
contained in the actual bad event. -/
theorem native_cluster_cut_tail (k a q : ℕ) {c : ℝ}
    (hk : 1 ≤ k) (ha : 1 ≤ a) (hc : 1 ≤ c) :
    let N := clusterRunCap k a c
    ∃ δ : ℝ, 0 < δ ∧ ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b →
      ∀ (M : TM), M.k = k → M.q + 1 ≤ 2 ^ q → M.g + 1 ≤ 2 ^ a →
        ((nativeBadClusterCuts M d b a c (clusterEpsilon k a N * (d * d * b : ℕ))
          ⌊clusterEpsilon k a N * (d * d * b : ℕ)⌋₊
          ⌈clusterEpsilon k a N * (d * d * b : ℕ)⌉₊ ⌊δ * (d * d * b : ℕ)⌋₊).card : ℝ) <
          (2 : ℝ) ^ ((1 - returnTailEta N) * (d * d * b : ℕ)) := by
  obtain ⟨δ, hδ, d₀, hrates⟩ := cluster_cut_rates k a q hk ha hc
  refine ⟨δ, hδ, max 2 d₀, ?_⟩
  intro d hd b hb M hMk hq hA
  have hr := hrates d ((le_max_right _ _).trans hd) b hb
  have hfinite := native_bad_cluster_cut_bound (M := M) (d := d) (b := b)
    (a := a) (q := q) (c := c)
    (H := ⌊clusterEpsilon k a (clusterRunCap k a c) * (d * d * b : ℕ)⌋₊)
    (j := ⌈clusterEpsilon k a (clusterRunCap k a c) * (d * d * b : ℕ)⌉₊)
    (r := ⌊δ * (d * d * b : ℕ)⌋₊)
    (error := clusterEpsilon k a (clusterRunCap k a c) * (d * d * b : ℕ)) hq hA
  rw [hMk] at hfinite
  apply cluster_product_tail (clusterMetadataSize_pos ..) (localCutMenu_pos ..) hfinite
  convert hr.2.2 using 1
  ring

end AdaptiveTransfer

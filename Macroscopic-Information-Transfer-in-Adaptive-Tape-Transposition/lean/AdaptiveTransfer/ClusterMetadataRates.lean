import AdaptiveTransfer.ClusterMetadata
import AdaptiveTransfer.ClusterRateBasics
import AdaptiveTransfer.MetadataRates

/-! Polynomial and logarithmic costs of the actual bounded cluster metadata.
All four chart endpoints per head are included, and the estimate uses the
literal ceiling of the stated coherence radius.
-/

namespace AdaptiveTransfer
open LeanMachine

theorem clusterMetadataSize_pos (k T W N j : ℕ) :
    1 ≤ clusterMetadataSize k T W N j := by
  have h : 0 < clusterMetadataSize k T W N j := by
    unfold clusterMetadataSize
    positivity
  omega

/-- A single polynomial bounds the exact sign/endpoint/run menu. -/
theorem clusterMetadata_polynomial_bound {k T W N j K P : ℕ}
    (hT : T ≤ K * (P + 1)) (hW : W ≤ P + 1) (hj : j ≤ P + 1) :
    clusterMetadataSize k T W N j ≤
      3 ^ k * (N + 1) * ((2 * k * K + 2 * K + 12) * (P + 1)) ^
        (3 + 4 * k + (k + 7) * N) := by
  let Z := (2 * k * K + 2 * K + 12) * (P + 1)
  have ht : T + 1 ≤ Z := by dsimp [Z]; nlinarith
  have hw : 2 * k * T + W + 2 ≤ Z := by dsimp [Z]; nlinarith
  have hc : 2 * T + 1 ≤ Z := by dsimp [Z]; nlinarith
  have he : 2 * clusterEndpointBound k T W j + 1 ≤ Z := by
    dsimp [clusterEndpointBound, Z]
    nlinarith
  calc
    _ ≤ 3 ^ k * (N + 1) * Z * Z ^ (4 * k) * Z ^ 2 *
        (Z ^ 4 * Z ^ (k + 3)) ^ N := by
      unfold clusterMetadataSize
      gcongr
    _ = _ := by
      change _ = 3 ^ k * (N + 1) * Z ^ (3 + 4 * k + (k + 7) * N)
      have hh : Z ^ 4 * Z ^ (k + 3) = Z ^ (k + 7) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hh, pow_add Z (3 + 4 * k) ((k + 7) * N), pow_add Z 3 (4 * k),
        pow_mul Z (k + 7) N]
      ring

theorem cluster_metadata_logb_small (k N K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → ∀ T W j,
      T ≤ K * (P + 1) → W ≤ P + 1 → j ≤ P + 1 →
      Real.logb 2 (clusterMetadataSize k T W N j : ℕ) ≤ ε * P := by
  have hp : 1 ≤ 3 ^ k * (N + 1) := by
    have h : 0 < 3 ^ k * (N + 1) := by positivity
    omega
  obtain ⟨P₀, h⟩ := polynomial_menu_logb_small hp
    (show 1 ≤ 2 * k * K + 2 * K + 12 by omega)
    (e := 3 + 4 * k + (k + 7) * N) hε
  exact ⟨P₀, fun P hP T W j hT hW hj => h P hP _ (clusterMetadataSize_pos ..)
    (clusterMetadata_polynomial_bound hT hW hj)⟩

/-- The time, slab width and rounded chart radius used by native clusters
are substituted before the logarithmic threshold is chosen. -/
theorem native_cluster_metadata_logb_small (k N a : ℕ) {c ε : ℝ}
    (hk : 1 ≤ k) (hN : 1 ≤ N) (ha : 1 ≤ a) (hc : 1 ≤ c) (hε : 0 < ε) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P →
      Real.logb 2 (clusterMetadataSize k (returnTime P c) (slabWidth P a c) N
        ⌈clusterEpsilon k a N * P⌉₊ : ℕ) ≤ ε * P := by
  obtain ⟨P₀, h⟩ := cluster_metadata_logb_small k N ⌈c⌉₊ hε
  exact ⟨P₀, fun P hP => h P hP _ _ _
    (returnTime_le_integer_linear (by linarith)) (slabWidth_le_length_add_one ha hc)
    ((cluster_fringe_le_length hk ha hN P).trans (Nat.le_succ _))⟩

end AdaptiveTransfer

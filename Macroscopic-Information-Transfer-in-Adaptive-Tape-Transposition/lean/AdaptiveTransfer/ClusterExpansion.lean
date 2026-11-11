import AdaptiveTransfer.ClusterTail
import AdaptiveTransfer.ClusterSingleton

/-! Complete coherent-cluster conclusions on original native runs. A single
exceptional set covers every chart, sign choice and cluster. Demand sets and
cuts remain in the original full execution, for every smaller threshold. -/
namespace AdaptiveTransfer
open Transpose MergeDepth BoundedNesting NativeRelations Finset

def OriginalClusterCutExpansion (M : TM) {P : ℕ} (X : Fin P → Bool) (π : Fin P → Fin P)
    (cluster : Finset (Fin M.k)) (U : Finset (Fin P)) (H : ℕ) (lam : ℝ) : Prop :=
  ∀ H' ≤ H, ∀ B : Finset ℕ, (∀ t ∈ B, t < (trace M (List.ofFn X)).haltTime) →
    IsMengerVertexCut (trace M (List.ofFn X)).work (trace M (List.ofFn X)).haltTime
      (nativeDemandedOutputSteps M X (trace M (List.ofFn X)).haltTime π U)
      (offClusterLowerEndpoints (trace M (List.ofFn X)).work cluster
        (trace M (List.ofFn X)).haltTime H') B → lam * P < (B.card : ℝ)

/-- Exact cluster return constants and one exceptional set for all actual
coherent charts; an all-head cluster is impossible on that good event. -/
theorem native_coherent_cluster_returns (k a : ℕ) {c : ℝ}
    (hk : 1 ≤ k) (ha : 1 ≤ a) (hc : 1 ≤ c) :
    let N := clusterRunCap k a c
    let eps := clusterEpsilon k a N
    let eta := returnTailEta N
    0 < eps ∧ 0 < eta ∧ ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 / 2 ∧ ∃ d₀ : ℕ,
      ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b → ∀ M : TM, M.k = k →
        ∀ q : ℕ, M.q + 1 ≤ 2 ^ q → M.g + 1 ≤ 2 ^ a →
          (q : ℝ) ≤ (d * d * b : ℕ) / (64 * (N : ℝ) ^ 2) →
          let P := d * d * b
          let H := ⌊eps * (P : ℝ)⌋₊
          let E := nativeBadClusterReturns M d b c (eps * P) H ⌊γ * (P : ℝ)⌋₊
          (E.card : ℝ) < (2 : ℝ) ^ ((1 - eta) * P) ∧
          ∀ X : Fin P → Bool, TransposesInput M d b c X → X ∉ E →
            ∀ chart : ClusterChart (trace M (List.ofFn X)).work
                (trace M (List.ofFn X)).haltTime (eps * P),
              γ * P < ((offClusterReturns (trace M (List.ofFn X)).work chart.included
                (trace M (List.ofFn X)).haltTime H).card : ℝ) ∧ chart.included ≠ univ := by
  have hN := clusterRunCap_one_le k a c
  obtain ⟨γ, hγ, hhalf, d₀, htail⟩ := native_cluster_return_tail k a hk ha hc
  refine ⟨clusterEpsilon_pos hk ha hN, returnTailEta_pos hN, γ, hγ, hhalf, d₀, ?_⟩
  intro d hd b hb M hMk q hq hA hbudget
  refine ⟨htail d hd b hb M hMk q hq hA hbudget, ?_⟩
  intro X hcorrect hgood chart
  exact ⟨native_good_cluster_returns hcorrect hgood chart,
    native_good_cluster_not_all hcorrect hgood chart⟩

/-- At fixed controller width, every coherent chart has a demanded set in
[P/(8N),P/2] with large endpoint-inclusive original separators. Every valid
actual chart slab has this same conclusion, simultaneously over all H'≤H. -/
theorem native_coherent_cluster_expansion (k a q : ℕ) {c : ℝ}
    (hk : 1 ≤ k) (ha : 1 ≤ a) (hc : 1 ≤ c) :
    let N := clusterRunCap k a c
    let eps := clusterEpsilon k a N
    let eta := returnTailEta N
    0 < eps ∧ 0 < eta ∧ ∃ lam : ℝ, 0 < lam ∧ ∃ d₀ : ℕ,
      ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b → ∀ M : TM,
        M.k = k → M.q + 1 ≤ 2 ^ q → M.g + 1 ≤ 2 ^ a →
        let P := d * d * b
        let H := ⌊eps * (P : ℝ)⌋₊
        let j := ⌈eps * (P : ℝ)⌉₊
        let E := nativeBadClusterCuts M d b a c (eps * P) H j ⌊lam * (P : ℝ)⌋₊
        (E.card : ℝ) < (2 : ℝ) ^ ((1 - eta) * P) ∧
        ∀ X : Fin P → Bool, TransposesInput M d b c X → X ∉ E →
          ∀ chart : ClusterChart (trace M (List.ofFn X)).work
              (trace M (List.ofFn X)).haltTime (eps * P),
            (∃ U : Finset (Fin P), (P : ℝ) / (8 * (N : ℝ)) ≤ (U.card : ℝ) ∧ U.card ≤ P / 2 ∧
              OriginalClusterCutExpansion M X (tposOf d b) chart.included U H lam) ∧
            (∀ g : NativeValidClusterSlab chart a c j,
              let U := g.obs.omittedGeometry (tposOf d b)
              (P : ℝ) / (8 * (N : ℝ)) ≤ (U.card : ℝ) ∧ U.card ≤ P / 2 ∧
              OriginalClusterCutExpansion M X (tposOf d b) chart.included U H lam) := by
  let N := clusterRunCap k a c
  have hN : 1 ≤ N := clusterRunCap_one_le k a c
  obtain ⟨lam, hlam, d₁, htail⟩ := native_cluster_cut_tail k a q hk ha hc
  obtain ⟨_δ, _hδ, d₂, hrates⟩ := cluster_cut_rates k a q hk ha hc
  refine ⟨clusterEpsilon_pos hk ha hN, returnTailEta_pos hN,
    lam, hlam, d₁ + d₂ + 2, ?_⟩
  intro d hd b hb M hMk hq hA
  have hd₁ : d₁ ≤ d := by omega
  have hd₂ : d₂ ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  let P := d * d * b
  let eps := clusterEpsilon k a N
  let H := ⌊eps * (P : ℝ)⌋₊
  let j := ⌈eps * (P : ℝ)⌉₊
  have hP : 2 ≤ P := by dsimp [P]; nlinarith
  have hs : (P : ℝ) / (8 * (clusterRunCap M.k a c : ℝ)) ≤ clusterSaving d b M.k a c := by
    simpa only [hMk] using (hrates d hd₂ b hb).1
  have hsp : 0 < clusterSaving d b M.k a c := by
    simpa only [hMk] using (hrates d hd₂ b hb).2.1
  refine ⟨htail d hd₁ b hb M hMk hq hA, ?_⟩
  intro X hcorrect hgood chart
  have hslab (g : NativeValidClusterSlab chart a c j) :
      (P : ℝ) / (8 * (N : ℝ)) ≤ ((g.obs.omittedGeometry (tposOf d b)).card : ℝ) ∧
      (g.obs.omittedGeometry (tposOf d b)).card ≤ P / 2 ∧
      OriginalClusterCutExpansion M X (tposOf d b) chart.included
        (g.obs.omittedGeometry (tposOf d b)) H lam := by
    refine ⟨?_, g.omitted_card_upper hcorrect, ?_⟩
    · simpa only [hMk] using g.omitted_card_lower hs
    · intro H' hH B hB hsep
      exact native_good_cluster_cuts hcorrect hgood chart g hH B hB hsep
  refine ⟨?_, hslab⟩
  obtain ⟨g⟩ := native_valid_cluster_exists (by omega) hb hP ha hc hcorrect hsp chart (Nat.le_ceil _)
  exact ⟨g.obs.omittedGeometry (tposOf d b), hslab g⟩

end AdaptiveTransfer

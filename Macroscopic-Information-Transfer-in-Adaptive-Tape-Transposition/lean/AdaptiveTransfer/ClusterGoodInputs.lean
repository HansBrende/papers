import AdaptiveTransfer.NativeClusterEvents
import AdaptiveTransfer.ClusterSnapshots

/-! Literal good-event consequences for every coherent chart and every
valid actual selected chunk, with original full-run cuts at all smaller
excursion thresholds. -/
namespace AdaptiveTransfer
open Transpose MergeDepth BoundedNesting NativeRelations Finset

namespace NativeValidClusterSlab
variable {M : TM} {d b a j : ℕ} {c error : ℝ} {X : Fin (d * d * b) → Bool}
  {chart : ClusterChart (trace M (List.ofFn X)).work (trace M (List.ofFn X)).haltTime error}

theorem omitted_card_upper (g : NativeValidClusterSlab chart a c j)
    (hcorrect : TransposesInput M d b c X) :
    (g.obs.omittedGeometry (tposOf d b)).card ≤ (d * d * b) / 2 := by
  classical
  let τ := trace M (List.ofFn X)
  have hlen := (fibre_haltTime (mem_fibre.mpr rfl) hcorrect).2
  change (appendList τ τ.haltTime).length = d * d * b at hlen
  rw [g.obs.omittedGeometry_eq_literal g.obs.live_le hlen.ge]
  have hinj : Function.Injective (fun j : Fin (d * d * b) => appendTime τ τ.haltTime j.val) := by
    intro i j he
    apply Fin.ext
    exact (appendTime_strictMonoOn τ τ.haltTime).injOn
      (by simpa only [Set.mem_Iio, hlen] using i.isLt)
      (by simpa only [Set.mem_Iio, hlen] using j.isLt) he
  have hout : (outIn (fun j : Fin (d * d * b) => appendTime τ τ.haltTime j.val) g.obs.times).card ≤
      g.obs.times.card := by
    apply card_le_card_of_injOn (fun j => appendTime τ τ.haltTime j.val)
    · intro j hj
      exact (mem_filter.mp hj).2
    · exact hinj.injOn
  exact (card_le_card sdiff_subset).trans ((card_image_le).trans (hout.trans g.half))

theorem omitted_card_lower (g : NativeValidClusterSlab chart a c j)
    (hs : (d * d * b : ℕ) / (8 * (clusterRunCap M.k a c : ℝ)) ≤ clusterSaving d b M.k a c) :
    (d * d * b : ℕ) / (8 * (clusterRunCap M.k a c : ℝ)) ≤
      ((g.obs.omittedGeometry (tposOf d b)).card : ℝ) := by
  have hcost : 0 ≤ (a : ℝ) *
      (if g.obs.start = 0 then 0 else (slabWidth (d * d * b) a c : ℝ) + M.k) := by
    split_ifs <;> positivity
  have hh := g.margin
  linarith

end NativeValidClusterSlab

/-- Lowering the excursion threshold only adds original long-return targets. -/
theorem offClusterLowerEndpoints_anti {k : ℕ} (xs : Fin k → ℕ → ℤ)
    (cluster : Finset (Fin k)) (T : ℕ) {H H' : ℕ} (hH : H' ≤ H) :
    offClusterLowerEndpoints xs cluster T H ⊆ offClusterLowerEndpoints xs cluster T H' := by
  apply image_subset_image
  intro e he
  simp only [offClusterReturns, mem_filter] at he ⊢
  obtain ⟨u, hu, hfar⟩ := he.2.2
  exact ⟨he.1, he.2.1, u, hu, lt_of_le_of_lt hH hfar⟩

/-- Outside the one bad event, EVERY valid actual chunk has a large original
separator, even at every smaller nonnegative integer excursion threshold. -/
theorem native_good_cluster_cuts {M : TM} {d b a H j : ℕ} {c error lam : ℝ}
    {X : Fin (d * d * b) → Bool} (hcorrect : TransposesInput M d b c X)
    (hgood : X ∉ nativeBadClusterCuts M d b a c error H j ⌊lam * (d * d * b : ℕ)⌋₊)
    (chart : ClusterChart (trace M (List.ofFn X)).work (trace M (List.ofFn X)).haltTime error)
    (g : NativeValidClusterSlab chart a c j) {H' : ℕ} (hH : H' ≤ H)
    (B : Finset ℕ) (hB : ∀ t ∈ B, t < (trace M (List.ofFn X)).haltTime)
    (hsep : IsMengerVertexCut (trace M (List.ofFn X)).work (trace M (List.ofFn X)).haltTime
      (nativeDemandedOutputSteps M X (trace M (List.ofFn X)).haltTime (tposOf d b)
        (g.obs.omittedGeometry (tposOf d b)))
      (offClusterLowerEndpoints (trace M (List.ofFn X)).work chart.included
        (trace M (List.ofFn X)).haltTime H') B) :
    lam * (d * d * b : ℕ) < (B.card : ℝ) := by
  classical
  by_contra hn
  have hb : B.card ≤ ⌊lam * (d * d * b : ℕ)⌋₊ := Nat.le_floor (le_of_not_gt hn)
  apply hgood
  apply mem_filter.mpr
  refine ⟨mem_univ _, hcorrect, ⟨chart, g, B, hB, ?_⟩, hb⟩
  intro ρ r hr hp ht
  exact hsep ρ r hr hp (offClusterLowerEndpoints_anti _ _ _ hH ht)

/-- Outside the simultaneous return event, each admitted chart has more
than the real density of completed complementary returns. -/
theorem native_good_cluster_returns {M : TM} {d b H : ℕ} {c error γ : ℝ}
    {X : Fin (d * d * b) → Bool} (hcorrect : TransposesInput M d b c X)
    (hgood : X ∉ nativeBadClusterReturns M d b c error H ⌊γ * (d * d * b : ℕ)⌋₊)
    (chart : ClusterChart (trace M (List.ofFn X)).work (trace M (List.ofFn X)).haltTime error) :
    γ * (d * d * b : ℕ) < ((offClusterReturns (trace M (List.ofFn X)).work chart.included
      (trace M (List.ofFn X)).haltTime H).card : ℝ) := by
  classical
  by_contra hn
  apply hgood
  exact mem_filter.mpr ⟨mem_univ _, hcorrect, chart, Nat.le_floor (le_of_not_gt hn)⟩

theorem offClusterReturns_univ {k : ℕ} (xs : Fin k → ℕ → ℤ) (T H : ℕ) :
    offClusterReturns xs univ T H = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  exact (mem_filter.mp he).2.1 (mem_univ _)

/-- An all-head coherent chart is itself in the bad event, because its
complement has no returns. This needs no separate union bound. -/
theorem native_good_cluster_not_all {M : TM} {d b H J : ℕ} {c error : ℝ}
    {X : Fin (d * d * b) → Bool} (hcorrect : TransposesInput M d b c X)
    (hgood : X ∉ nativeBadClusterReturns M d b c error H J)
    (chart : ClusterChart (trace M (List.ofFn X)).work (trace M (List.ofFn X)).haltTime error) :
    chart.included ≠ univ := by
  classical
  intro he
  apply hgood
  refine mem_filter.mpr ⟨mem_univ _, hcorrect, chart, ?_⟩
  rw [he, offClusterReturns_univ, card_empty]
  exact Nat.zero_le _

end AdaptiveTransfer

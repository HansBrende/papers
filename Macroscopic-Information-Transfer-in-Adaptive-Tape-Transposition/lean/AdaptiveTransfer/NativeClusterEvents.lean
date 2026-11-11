import AdaptiveTransfer.NativeClusterClasses
import AdaptiveTransfer.CoreLocalData
import AdaptiveTransfer.NativeReturnCounting

/-! Literal coherent-cluster events on original successful native runs.
The real chart is quantified freely and the finite slab is obtained from its
actual signed carrier; neither an injection nor a selected chunk is assumed. -/

namespace AdaptiveTransfer
open Transpose MergeDepth BoundedNesting NativeRelations Finset

structure NativeValidClusterSlab {M : TM} {d b : ℕ} {error : ℝ}
    {X : Fin (d * d * b) → Bool}
    (chart : ClusterChart (trace M (List.ofFn X)).work (trace M (List.ofFn X)).haltTime error)
    (a : ℕ) (c : ℝ) (j : ℕ) where
  obs : ClusterObservation chart (returnTime (d * d * b) c)
    (slabWidth (d * d * b) a c) (clusterRunCap M.k a c) j
  half : obs.times.card ≤ (d * d * b) / 2
  margin : clusterSaving d b M.k a c ≤ ((obs.omittedGeometry (tposOf d b)).card : ℝ) -
    (a : ℝ) * (if obs.start = 0 then 0 else (slabWidth (d * d * b) a c : ℝ) + M.k)

/-- Every actual coherent chart has a valid finite chunk whenever the proved
geometric saving is positive. -/
theorem native_valid_cluster_exists {M : TM} {d b a j : ℕ} {c error : ℝ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hP : 2 ≤ d * d * b) (ha : 1 ≤ a) (hc : 1 ≤ c)
    {X : Fin (d * d * b) → Bool} (hcorrect : TransposesInput M d b c X)
    (hsaving : 0 < clusterSaving d b M.k a c)
    (chart : ClusterChart (trace M (List.ofFn X)).work (trace M (List.ofFn X)).haltTime error)
    (hj : error ≤ j) : Nonempty (NativeValidClusterSlab chart a c j) := by
  obtain ⟨ell, s, e, hse, he, hhalf, hruns, hmargin⟩ :=
    native_cluster_slab_geometry hd hb hP ha hc hcorrect chart
  have hne : (selectedSlab chart.carrier (slabWidth (d * d * b) a c) ell s e).Nonempty := by
    by_contra hn
    have hemp := not_nonempty_iff_eq_empty.mp hn
    have hU : omittedSlabBits d b (trace M (List.ofFn X)).input
        (fun j => appendTime (trace M (List.ofFn X)) (trace M (List.ofFn X)).haltTime j.val)
        (selectedSlab chart.carrier (slabWidth (d * d * b) a c) ell s e) = ∅ := by
      simp [omittedSlabBits, outIn, hemp]
    rw [hU, card_empty, Nat.cast_zero] at hmargin
    have hcost : 0 ≤ (a : ℝ) * (if s = 0 then 0 else (slabWidth (d * d * b) a c : ℝ) + M.k) := by
      split_ifs <;> positivity
    linarith
  let o : ClusterObservation chart (returnTime (d * d * b) c)
      (slabWidth (d * d * b) a c) (clusterRunCap M.k a c) j :=
    ⟨ell, s, e, hse, he.trans (timely_native_data hcorrect).1, he, hj, hne, hruns⟩
  refine ⟨⟨o, hhalf, ?_⟩⟩
  rw [o.omittedGeometry_eq_literal he (fibre_haltTime (mem_fibre.mpr rfl) hcorrect).2.ge]
  exact hmargin

noncomputable def nativeBadClusterReturns (M : TM) (d b : ℕ) (c error : ℝ) (H J : ℕ) :
    Finset (Fin (d * d * b) → Bool) := by
  classical
  exact univ.filter fun X => TransposesInput M d b c X ∧
    ∃ chart : ClusterChart (trace M (List.ofFn X)).work (trace M (List.ofFn X)).haltTime error,
      (offClusterReturns (trace M (List.ofFn X)).work chart.included
        (trace M (List.ofFn X)).haltTime H).card ≤ J

structure NativeClusterCutWitness (M : TM) (d b a : ℕ) (c error : ℝ) (H j : ℕ)
    (X : Fin (d * d * b) → Bool) where
  chart : ClusterChart (trace M (List.ofFn X)).work (trace M (List.ofFn X)).haltTime error
  slab : NativeValidClusterSlab chart a c j
  cut : Finset ℕ
  cut_lt : ∀ t ∈ cut, t < (trace M (List.ofFn X)).haltTime
  separates : IsMengerVertexCut (trace M (List.ofFn X)).work (trace M (List.ofFn X)).haltTime
    (nativeDemandedOutputSteps M X (trace M (List.ofFn X)).haltTime (tposOf d b)
      (slab.obs.omittedGeometry (tposOf d b)))
    (offClusterLowerEndpoints (trace M (List.ofFn X)).work chart.included
      (trace M (List.ofFn X)).haltTime H) cut

noncomputable def nativeBadClusterCuts (M : TM) (d b a : ℕ) (c error : ℝ) (H j r : ℕ) :
    Finset (Fin (d * d * b) → Bool) := by
  classical
  exact univ.filter fun X => TransposesInput M d b c X ∧
    ∃ w : NativeClusterCutWitness M d b a c error H j X, w.cut.card ≤ r

end AdaptiveTransfer

import AdaptiveTransfer.ClusterChartMetadata

/-! Bounded metadata computed from an actual coherent-cluster slab. The
record has precisely the finite sign/endpoint/run menu used in the paper.
Equal records recover the selected times and all physical core/fringe sets,
without encoding or identifying the underlying real chart functions.
-/

namespace AdaptiveTransfer
open Finset MergeDepth BoundedNesting NativeRelations
open scoped BigOperators
attribute [local instance] Classical.propDecidable

structure ClusterMetadata (k T W N j : ℕ) where
  signature : ClusterSignature k
  ell : SlabCoordinate (k * T) W
  endpoints : Fin k → Fin 4 → HeadCoordinate (clusterEndpointBound k T W j)
  start : Fin (T + 1)
  finish : Fin (T + 1)
  count : Fin (N + 1)
  runs : Fin N → RunMetadata k T

def clusterMetadataSize (k T W N j : ℕ) : ℕ :=
  3 ^ k * (N + 1) * (2 * k * T + W + 2) *
    (2 * clusterEndpointBound k T W j + 1) ^ (4 * k) * (T + 1) ^ 2 *
    ((T + 1) ^ 4 * (2 * T + 1) ^ (k + 3)) ^ N

private def clusterMetadataEquiv (k T W N j : ℕ) : ClusterMetadata k T W N j ≃
    (ClusterSignature k × SlabCoordinate (k * T) W ×
      (Fin k → Fin 4 → HeadCoordinate (clusterEndpointBound k T W j)) ×
      Fin (T + 1) × Fin (T + 1) × Fin (N + 1) × (Fin N → RunMetadata k T)) where
  toFun g := (g.signature, g.ell, g.endpoints, g.start, g.finish, g.count, g.runs)
  invFun g := ⟨g.1, g.2.1, g.2.2.1, g.2.2.2.1, g.2.2.2.2.1, g.2.2.2.2.2.1, g.2.2.2.2.2.2⟩

noncomputable instance (k T W N j : ℕ) : Fintype (ClusterMetadata k T W N j) :=
  Fintype.ofEquiv _ (clusterMetadataEquiv k T W N j).symm

@[simp] theorem clusterMetadata_card (k T W N j : ℕ) :
    Fintype.card (ClusterMetadata k T W N j) = clusterMetadataSize k T W N j := by
  rw [Fintype.card_congr (clusterMetadataEquiv k T W N j)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_option,
    Fintype.card_bool, Nat.reduceAdd,
    slabCoordinate_card, headCoordinate_card, runMetadata_card, clusterMetadataSize, ← pow_mul]
  ring

namespace ClusterMetadata
variable {k T W N j : ℕ} (g : ClusterMetadata k T W N j)

noncomputable def times : Finset ℕ :=
  univ.biUnion fun i => if i.val < g.count.val then Ico (g.runs i).start.val (g.runs i).finish.val else ∅

noncomputable def core (h : Fin k) : Finset ℤ :=
  if g.signature h ≠ none then
    (endpointCore (fun i => (g.endpoints h i).val)).image (clusterOrient (g.signature h)) else ∅

noncomputable def fringe (h : Fin k) : Finset ℤ :=
  if g.signature h ≠ none then
    (endpointFringe (fun i => (g.endpoints h i).val)).image (clusterOrient (g.signature h)) else ∅

end ClusterMetadata

/-- The selected chunk is computed from the actual signed carrier. Its live
time and rounding assumptions are mathematical input conditions, not a supplied
chart encoding or a bounded-endpoint certificate. -/
structure ClusterObservation {k L : ℕ} {J : ℝ} {τ : Trace k}
    (chart : ClusterChart τ.work L J) (T W N j : ℕ) where
  ell : ℤ
  start : ℕ
  finish : ℕ
  start_le : start ≤ finish
  finish_le : finish ≤ T
  live_le : finish ≤ L
  error_le : J ≤ j
  nonempty : (selectedSlab chart.carrier W ell start finish).Nonempty
  run_cap : (runStarts (selectedSlab chart.carrier W ell start finish)).card ≤ N

namespace ClusterObservation
variable {k L T W N j : ℕ} {J : ℝ} {τ : Trace k} {chart : ClusterChart τ.work L J}
  (g : ClusterObservation chart T W N j)

noncomputable def times : Finset ℕ := selectedSlab chart.carrier W g.ell g.start g.finish

theorem time_finish {t : ℕ} (ht : t ∈ g.times) : t < g.finish :=
  (mem_Ico.mp (mem_filter.mp ht).1).2

theorem time_start {t : ℕ} (ht : t ∈ g.times) : g.start ≤ t :=
  (mem_Ico.mp (mem_filter.mp ht).1).1

theorem time_lt {t : ℕ} (ht : t ∈ g.times) : t < T := (g.time_finish ht).trans_le g.finish_le

theorem time_live {t : ℕ} (ht : t ∈ g.times) : t < L := (g.time_finish ht).trans_le g.live_le

theorem selected {t : ℕ} (ht : t ∈ g.times) :
    g.ell ≤ chart.carrier t ∧ chart.carrier t < g.ell + W := (mem_filter.mp ht).2

theorem ell_bound : -(k * T : ℕ) - (W : ℤ) ≤ g.ell ∧ g.ell ≤ (k * T : ℕ) + (1 : ℤ) := by
  obtain ⟨t, ht⟩ := g.nonempty
  have hs := g.selected ht
  have hb := abs_le.mp (chart.carrier_bound (fun h => trace_work_abs_bound τ (g.time_lt ht).le h))
  omega

noncomputable def endpointCode (h : Fin k) (i : Fin 4) :
    HeadCoordinate (clusterEndpointBound k T W j) :=
  if hh : chart.signature h ≠ none then
    ⟨clusterEndpoints (chart.map ⟨h, hh⟩ g.ell) (chart.map ⟨h, hh⟩ (g.ell + W)) j i,
      mem_Icc.mpr (abs_le.mp (chart.endpoint_bounds (g.time_live g.nonempty.choose_spec)
        (g.time_lt g.nonempty.choose_spec).le g.error_le (g.selected g.nonempty.choose_spec) ⟨h, hh⟩ i))⟩
  else ⟨0, by simp⟩

theorem work_bound (h : Fin k) {t : ℕ} (ht : t ≤ T) :
    -(T : ℤ) ≤ τ.work h t ∧ τ.work h t ≤ T := abs_le.mp (trace_work_abs_bound τ ht h)

theorem input_bound {t : ℕ} (ht : t ≤ T) : -(T : ℤ) ≤ τ.input t ∧ τ.input t ≤ T := by
  have hh := (show IsWalk τ.input from τ.abs_input_succ_sub_le).lip (Nat.zero_le t)
  rw [τ.input_zero] at hh
  omega

theorem run_start_bound {r : ℕ} (hr : r ∈ runStarts g.times) : r ≤ T :=
  (g.time_lt (mem_filter.mp hr).1).le

theorem run_finish_bound {r : ℕ} (hr : r ∈ runStarts g.times) : runEnd g.times g.finish r ≤ T :=
  (runEnd_spec (fun _t ht => g.time_finish ht) hr).2.1.trans g.finish_le

theorem extrema_bounds {r : ℕ} (hr : r ∈ runStarts g.times) :
    (-(T : ℤ) ≤ runRawLo τ.input g.times g.finish r ∧ runRawLo τ.input g.times g.finish r ≤ T) ∧
    (-(T : ℤ) ≤ runRawHi τ.input g.times g.finish r ∧ runRawHi τ.input g.times g.finish r ≤ T) := by
  have hend := runEnd_spec (fun _t ht => g.time_finish ht) hr
  have hne : ((Ico r (runEnd g.times g.finish r)).image τ.input).Nonempty :=
    ⟨τ.input r, mem_image.mpr ⟨r, mem_Ico.mpr ⟨le_rfl, hend.1⟩, rfl⟩⟩
  simp only [runRawLo, runRawHi, dite_eq_left hne]
  constructor
  · obtain ⟨t, ht, he⟩ := mem_image.mp (min'_mem _ hne)
    rw [← he]
    exact input_bound (τ := τ) ((mem_Ico.mp ht).2.le.trans (g.run_finish_bound hr))
  · obtain ⟨t, ht, he⟩ := mem_image.mp (max'_mem _ hne)
    rw [← he]
    exact input_bound (τ := τ) ((mem_Ico.mp ht).2.le.trans (g.run_finish_bound hr))

noncomputable def runRecord (r : ℕ) (hr : r ∈ runStarts g.times) : RunMetadata k T where
  start := ⟨r, Nat.lt_succ_of_le (g.run_start_bound hr)⟩
  finish := ⟨runEnd g.times g.finish r, Nat.lt_succ_of_le (g.run_finish_bound hr)⟩
  outLo := ⟨(appendList τ r).length, Nat.lt_succ_of_le ((length_appendList_le τ r).trans (g.run_start_bound hr))⟩
  outHi := ⟨(appendList τ (runEnd g.times g.finish r)).length,
    Nat.lt_succ_of_le ((length_appendList_le τ _).trans (g.run_finish_bound hr))⟩
  work h := ⟨τ.work h r, mem_Icc.mpr (work_bound (τ := τ) h (g.run_start_bound hr))⟩
  raw := ⟨τ.input r, mem_Icc.mpr (input_bound (τ := τ) (g.run_start_bound hr))⟩
  rawLo := ⟨runRawLo τ.input g.times g.finish r, mem_Icc.mpr (g.extrema_bounds hr).1⟩
  rawHi := ⟨runRawHi τ.input g.times g.finish r, mem_Icc.mpr (g.extrema_bounds hr).2⟩

noncomputable def encode : ClusterMetadata k T W N j where
  signature := chart.signature
  ell := ⟨g.ell, mem_Icc.mpr g.ell_bound⟩
  endpoints := g.endpointCode
  start := ⟨g.start, Nat.lt_succ_of_le (g.start_le.trans g.finish_le)⟩
  finish := ⟨g.finish, Nat.lt_succ_of_le g.finish_le⟩
  count := ⟨(runStarts g.times).card, Nat.lt_succ_of_le g.run_cap⟩
  runs i := if hi : i.val < (runStarts g.times).card then
    g.runRecord (runNumber g.times i.val) (runNumber_mem hi) else default

@[simp] theorem encode_core (h : Fin k) : g.encode.core h = chart.core g.ell W j h := by
  change (if chart.signature h ≠ none then
    (endpointCore (fun i => (g.endpointCode h i).val)).image (clusterOrient (chart.signature h)) else ∅) = _
  by_cases hh : chart.signature h ≠ none
  · rw [ite_eq_left hh]
    have he : (fun i => (g.endpointCode h i).val) =
        clusterEndpoints (chart.map ⟨h, hh⟩ g.ell) (chart.map ⟨h, hh⟩ (g.ell + W)) j := by
      funext i
      simp only [endpointCode, dite_eq_left hh]
    rw [he, endpointCore_actual]
    simp only [ClusterChart.core, dite_eq_left hh, ClusterChart.orientedCore]
  · rw [ite_eq_right hh]
    simp only [ClusterChart.core, dite_eq_right hh]

@[simp] theorem encode_fringe (h : Fin k) : g.encode.fringe h = chart.fringe g.ell W j h := by
  change (if chart.signature h ≠ none then
    (endpointFringe (fun i => (g.endpointCode h i).val)).image (clusterOrient (chart.signature h)) else ∅) = _
  by_cases hh : chart.signature h ≠ none
  · rw [ite_eq_left hh]
    have he : (fun i => (g.endpointCode h i).val) =
        clusterEndpoints (chart.map ⟨h, hh⟩ g.ell) (chart.map ⟨h, hh⟩ (g.ell + W)) j := by
      funext i
      simp only [endpointCode, dite_eq_left hh]
    rw [he, endpointFringe_actual]
    simp only [ClusterChart.fringe, dite_eq_left hh, ClusterChart.orientedFringe]
  · rw [ite_eq_right hh]
    simp only [ClusterChart.fringe, dite_eq_right hh]

@[simp] theorem encode_times : g.encode.times = g.times := by
  ext t
  simp only [ClusterMetadata.times, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, ht⟩
    by_cases hi : i.val < (runStarts g.times).card
    · simp only [encode, hi, ↓reduceIte, runRecord] at ht
      exact (runEnd_spec (fun _t ht => g.time_finish ht) (runNumber_mem hi)).2.2.2 t ht
    · simp only [encode, hi, ↓reduceIte, Finset.notMem_empty] at ht
  · intro ht
    obtain ⟨r, hr, hrt, hte⟩ := exists_run_cover (fun _t ht => g.time_finish ht) ht
    obtain ⟨i, hi, hir⟩ := exists_runNumber hr
    refine ⟨⟨i, hi.trans_le g.run_cap⟩, ?_⟩
    simp only [encode, hi, ↓reduceIte, runRecord, hir]
    exact mem_Ico.mpr ⟨hrt, hte⟩

variable {L' : ℕ} {J' : ℝ} {τ' : Trace k} {chart' : ClusterChart τ'.work L' J'}
  {g' : ClusterObservation chart' T W N j}

theorem signature_eq_of_encode_eq (he : g.encode = g'.encode) : chart.signature = chart'.signature :=
  congrArg ClusterMetadata.signature he

theorem ell_eq_of_encode_eq (he : g.encode = g'.encode) : g.ell = g'.ell :=
  congrArg (fun a => a.ell.val) he

theorem start_eq_of_encode_eq (he : g.encode = g'.encode) : g.start = g'.start :=
  congrArg (fun a => a.start.val) he

theorem finish_eq_of_encode_eq (he : g.encode = g'.encode) : g.finish = g'.finish :=
  congrArg (fun a => a.finish.val) he

theorem core_eq_of_encode_eq (he : g.encode = g'.encode) (h : Fin k) :
    chart.core g.ell W j h = chart'.core g'.ell W j h := by
  rw [← g.encode_core, ← g'.encode_core, he]

theorem fringe_eq_of_encode_eq (he : g.encode = g'.encode) (h : Fin k) :
    chart.fringe g.ell W j h = chart'.fringe g'.ell W j h := by
  rw [← g.encode_fringe, ← g'.encode_fringe, he]

theorem times_eq_of_encode_eq (he : g.encode = g'.encode) : g.times = g'.times := by
  rw [← g.encode_times, ← g'.encode_times, he]

theorem runRecord_eq_of_encode_eq (he : g.encode = g'.encode) {r : ℕ} (hr : r ∈ runStarts g.times) :
    g.runRecord r hr = g'.runRecord r (g.times_eq_of_encode_eq he ▸ hr) := by
  have hC := g.times_eq_of_encode_eq he
  obtain ⟨i, hi, hir⟩ := exists_runNumber hr
  have hi' : i < (runStarts g'.times).card := by simpa only [← hC] using hi
  have hnr : runNumber g'.times i = r := by simpa only [← hC] using hir
  have hh := congrArg (fun m => m.runs ⟨i, hi.trans_le g.run_cap⟩) he
  simpa only [encode, dite_eq_left hi, dite_eq_left hi', hir, hnr] using hh

end ClusterObservation
end AdaptiveTransfer

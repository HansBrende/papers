import AdaptiveTransfer.ReplayMetadata
import AdaptiveTransfer.GetterGeometry

/-! Exact bounded multiport metadata. Port coordinates are relative to their
public origins. Past-visit records store only the k-1 noncarrier intervals.
The k=1 specialization has no such fields and serves the entire enlarged rule.
-/

namespace AdaptiveTransfer.Getter
open Finset NativeRelations BoundedNesting MergeDepth
open scoped BigOperators

structure PortRunMetadata (k p T : ℕ) where
  start : Fin (T + 1)
  finish : Fin (T + 1)
  outLo : Fin (T + 1)
  outHi : Fin (T + 1)
  work : Fin k → HeadCoordinate T
  ports : Fin p → HeadCoordinate T
  portLo : Fin p → HeadCoordinate T
  portHi : Fin p → HeadCoordinate T
  past : Fin (k - 1) → Option (HeadCoordinate T × HeadCoordinate T)
  deriving Inhabited

private def portRunEquiv (k p T : ℕ) : PortRunMetadata k p T ≃
    (Fin (T + 1) × Fin (T + 1) × Fin (T + 1) × Fin (T + 1) ×
      (Fin k → HeadCoordinate T) × (Fin p → HeadCoordinate T) ×
      (Fin p → HeadCoordinate T) × (Fin p → HeadCoordinate T) ×
      (Fin (k - 1) → Option (HeadCoordinate T × HeadCoordinate T))) where
  toFun r := (r.start, r.finish, r.outLo, r.outHi, r.work, r.ports, r.portLo, r.portHi, r.past)
  invFun r := ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1,
    r.2.2.2.2.2.1, r.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2.2⟩

noncomputable instance (k p T : ℕ) : Fintype (PortRunMetadata k p T) :=
  Fintype.ofEquiv _ (portRunEquiv k p T).symm

@[simp] theorem portRunMetadata_card (k p T : ℕ) :
    Fintype.card (PortRunMetadata k p T) =
      (T + 1) ^ 4 * (2 * T + 1) ^ (k + 3 * p) * (1 + (2 * T + 1) ^ 2) ^ (k - 1) := by
  rw [Fintype.card_congr (portRunEquiv k p T)]
  rw [show k + 3 * p = k + p + p + p by omega]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_option,
    headCoordinate_card, pow_add, pow_succ, pow_zero]
  ring

structure PortMetadata (k p T W N : ℕ) where
  free : Fin k
  ell : SlabCoordinate T W
  start : Fin (T + 1)
  finish : Fin (T + 1)
  count : Fin (N + 1)
  runs : Fin N → PortRunMetadata k p T

def portMetadataSize (k p T W N : ℕ) : ℕ :=
  k * (N + 1) * (2 * T + W + 2) * (T + 1) ^ 2 *
    ((T + 1) ^ 4 * (2 * T + 1) ^ (k + 3 * p) * (1 + (2 * T + 1) ^ 2) ^ (k - 1)) ^ N

private def portMetadataEquiv (k p T W N : ℕ) : PortMetadata k p T W N ≃
    (Fin k × SlabCoordinate T W × Fin (T + 1) × Fin (T + 1) ×
      Fin (N + 1) × (Fin N → PortRunMetadata k p T)) where
  toFun r := (r.free, r.ell, r.start, r.finish, r.count, r.runs)
  invFun r := ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2⟩

noncomputable instance (k p T W N : ℕ) : Fintype (PortMetadata k p T W N) :=
  Fintype.ofEquiv _ (portMetadataEquiv k p T W N).symm

@[simp] theorem portMetadata_card (k p T W N : ℕ) :
    Fintype.card (PortMetadata k p T W N) = portMetadataSize k p T W N := by
  rw [Fintype.card_congr (portMetadataEquiv k p T W N)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    slabCoordinate_card, portRunMetadata_card, portMetadataSize]
  ring

noncomputable def remainingHeads {k : ℕ} (f : Fin k) : Fin (k - 1) ≃ {h : Fin k // h ≠ f} :=
  (Fintype.equivFinOfCardEq (by simp [Fintype.card_subtype_compl])).symm

noncomputable def PortMetadata.times {k p T W N : ℕ} (g : PortMetadata k p T W N) : Finset ℕ :=
  univ.biUnion fun i => if i.val < g.count.val then Ico (g.runs i).start.val (g.runs i).finish.val else ∅

namespace Observation
variable {k p T W N : ℕ} {τ : Trace k} (g : SlabObservation τ T W N)
  (xs : Fin p → ℕ → ℤ) (origin : Fin p → ℤ)
  (hx : ∀ j, IsWalk (xs j)) (hzero : ∀ j, xs j 0 = origin j)

include hx hzero in
theorem port_bound (j : Fin p) {t : ℕ} (ht : t ≤ T) :
    -(T : ℤ) ≤ xs j t - origin j ∧ xs j t - origin j ≤ T := by
  have hh := (hx j).lip (Nat.zero_le t)
  rw [hzero j] at hh
  omega

include hx hzero in
theorem port_extrema_bounds {r : ℕ} (hr : r ∈ runStarts g.times) (j : Fin p) :
    (-(T : ℤ) ≤ runRawLo (xs j) g.times g.finish r - origin j ∧
      runRawLo (xs j) g.times g.finish r - origin j ≤ T) ∧
    (-(T : ℤ) ≤ runRawHi (xs j) g.times g.finish r - origin j ∧
      runRawHi (xs j) g.times g.finish r - origin j ≤ T) := by
  have he := runEnd_spec (fun _t ht => g.time_finish ht) hr
  have hne : ((Ico r (runEnd g.times g.finish r)).image (xs j)).Nonempty :=
    ⟨xs j r, mem_image_of_mem _ (mem_Ico.mpr ⟨le_rfl, he.1⟩)⟩
  simp only [runRawLo, runRawHi, dite_eq_left hne]
  constructor
  · obtain ⟨t, ht, heq⟩ := mem_image.mp (min'_mem _ hne)
    rw [← heq]
    exact port_bound xs origin hx hzero j ((mem_Ico.mp ht).2.le.trans (g.run_finish_bound hr))
  · obtain ⟨t, ht, heq⟩ := mem_image.mp (max'_mem _ hne)
    rw [← heq]
    exact port_bound xs origin hx hzero j ((mem_Ico.mp ht).2.le.trans (g.run_finish_bound hr))

noncomputable def pastRecord (r : ℕ) (hr : r ∈ runStarts g.times) (h : Fin k) :
    Option (HeadCoordinate T × HeadCoordinate T) :=
  if hn : ((range r).image (τ.work h)).Nonempty then
    some (⟨((range r).image (τ.work h)).min' hn, mem_Icc.mpr (by
      obtain ⟨t, ht, he⟩ := mem_image.mp (min'_mem _ hn)
      rw [← he]
      exact SlabObservation.work_bound h ((mem_range.mp ht).le.trans (g.run_start_bound hr)))⟩,
    ⟨((range r).image (τ.work h)).max' hn, mem_Icc.mpr (by
      obtain ⟨t, ht, he⟩ := mem_image.mp (max'_mem _ hn)
      rw [← he]
      exact SlabObservation.work_bound h ((mem_range.mp ht).le.trans (g.run_start_bound hr)))⟩)
  else none

theorem pastRecord_value (r : ℕ) (hr : r ∈ runStarts g.times) (h : Fin k) :
    (pastRecord g r hr h).map (fun v => (v.1.val, v.2.val)) = visitInterval (τ.work h) r := by
  unfold pastRecord visitInterval
  split_ifs <;> rfl

noncomputable def runRecord (r : ℕ) (hr : r ∈ runStarts g.times) : PortRunMetadata k p T where
  start := ⟨r, Nat.lt_succ_of_le (g.run_start_bound hr)⟩
  finish := ⟨runEnd g.times g.finish r, Nat.lt_succ_of_le (g.run_finish_bound hr)⟩
  outLo := ⟨(appendList τ r).length,
    Nat.lt_succ_of_le ((length_appendList_le τ r).trans (g.run_start_bound hr))⟩
  outHi := ⟨(appendList τ (runEnd g.times g.finish r)).length,
    Nat.lt_succ_of_le ((length_appendList_le τ _).trans (g.run_finish_bound hr))⟩
  work h := ⟨τ.work h r, mem_Icc.mpr (SlabObservation.work_bound h (g.run_start_bound hr))⟩
  ports j := ⟨xs j r - origin j, mem_Icc.mpr (port_bound xs origin hx hzero j (g.run_start_bound hr))⟩
  portLo j := ⟨runRawLo (xs j) g.times g.finish r - origin j,
    mem_Icc.mpr (port_extrema_bounds g xs origin hx hzero hr j).1⟩
  portHi j := ⟨runRawHi (xs j) g.times g.finish r - origin j,
    mem_Icc.mpr (port_extrema_bounds g xs origin hx hzero hr j).2⟩
  past j := pastRecord g r hr (remainingHeads g.free j).val

noncomputable def encode : PortMetadata k p T W N where
  free := g.free
  ell := ⟨g.ell, mem_Icc.mpr g.ell_bound⟩
  start := ⟨g.start, Nat.lt_succ_of_le (g.start_le.trans g.finish_le)⟩
  finish := ⟨g.finish, Nat.lt_succ_of_le g.finish_le⟩
  count := ⟨(runStarts g.times).card, Nat.lt_succ_of_le g.run_cap⟩
  runs i := if hi : i.val < (runStarts g.times).card then
    runRecord g xs origin hx hzero (runNumber g.times i.val) (runNumber_mem hi) else default

@[simp] theorem encode_times : (encode g xs origin hx hzero).times = g.times := by
  classical
  ext t
  simp only [PortMetadata.times, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, ht⟩
    by_cases hi : i.val < (runStarts g.times).card
    · simp only [encode, hi, ↓reduceIte, runRecord] at ht
      exact (runEnd_spec (fun _t ht => g.time_finish ht) (runNumber_mem hi)).2.2.2 t ht
    · simp only [encode, hi, ↓reduceIte, notMem_empty] at ht
  · intro ht
    obtain ⟨r, hr, hrt, hte⟩ := exists_run_cover (fun _t ht => g.time_finish ht) ht
    obtain ⟨i, hi, hir⟩ := exists_runNumber hr
    refine ⟨⟨i, hi.trans_le g.run_cap⟩, ?_⟩
    simp only [encode, hi, ↓reduceIte, runRecord, hir]
    exact mem_Ico.mpr ⟨hrt, hte⟩

variable {τ' : Trace k} {g' : SlabObservation τ' T W N}
  {ys : Fin p → ℕ → ℤ} {hy : ∀ j, IsWalk (ys j)} {hyzero : ∀ j, ys j 0 = origin j}

theorem times_eq_of_encode_eq
    (he : encode g xs origin hx hzero = encode g' ys origin hy hyzero) : g.times = g'.times := by
  rw [← encode_times g xs origin hx hzero, ← encode_times g' ys origin hy hyzero, he]

theorem runRecord_eq_of_encode_eq
    (he : encode g xs origin hx hzero = encode g' ys origin hy hyzero)
    {r : ℕ} (hr : r ∈ runStarts g.times) :
    runRecord g xs origin hx hzero r hr =
      runRecord g' ys origin hy hyzero r (times_eq_of_encode_eq g xs origin hx hzero he ▸ hr) := by
  have hC := times_eq_of_encode_eq g xs origin hx hzero he
  obtain ⟨i, hi, hir⟩ := exists_runNumber hr
  have hi' : i < (runStarts g'.times).card := by simpa only [← hC] using hi
  have hnr : runNumber g'.times i = r := by simpa only [← hC] using hir
  have hh := congrArg (fun m => m.runs ⟨i, hi.trans_le g.run_cap⟩) he
  simpa only [encode, dite_eq_left hi, dite_eq_left hi', hir, hnr] using hh

theorem free_eq (he : encode g xs origin hx hzero = encode g' ys origin hy hyzero) : g.free = g'.free :=
  congrArg PortMetadata.free he

theorem ell_eq (he : encode g xs origin hx hzero = encode g' ys origin hy hyzero) : g.ell = g'.ell :=
  congrArg (fun m => m.ell.val) he

theorem start_eq (he : encode g xs origin hx hzero = encode g' ys origin hy hyzero) : g.start = g'.start :=
  congrArg (fun m => m.start.val) he

theorem finish_eq (he : encode g xs origin hx hzero = encode g' ys origin hy hyzero) : g.finish = g'.finish :=
  congrArg (fun m => m.finish.val) he

theorem work_eq (he : encode g xs origin hx hzero = encode g' ys origin hy hyzero)
    {r : ℕ} (hr : r ∈ runStarts g.times) (h : Fin k) : τ.work h r = τ'.work h r :=
  congrArg (fun m => (m.work h).val) (runRecord_eq_of_encode_eq g xs origin hx hzero he hr)

theorem ports_eq (he : encode g xs origin hx hzero = encode g' ys origin hy hyzero)
    {r : ℕ} (hr : r ∈ runStarts g.times) (j : Fin p) : xs j r = ys j r := by
  have hh := congrArg (fun m => (m.ports j).val) (runRecord_eq_of_encode_eq g xs origin hx hzero he hr)
  exact sub_left_inj.mp hh

theorem portLo_eq (he : encode g xs origin hx hzero = encode g' ys origin hy hyzero)
    {r : ℕ} (hr : r ∈ runStarts g.times) (j : Fin p) :
    runRawLo (xs j) g.times g.finish r = runRawLo (ys j) g'.times g'.finish r := by
  have hh := congrArg (fun m => (m.portLo j).val) (runRecord_eq_of_encode_eq g xs origin hx hzero he hr)
  exact sub_left_inj.mp hh

theorem portHi_eq (he : encode g xs origin hx hzero = encode g' ys origin hy hyzero)
    {r : ℕ} (hr : r ∈ runStarts g.times) (j : Fin p) :
    runRawHi (xs j) g.times g.finish r = runRawHi (ys j) g'.times g'.finish r := by
  have hh := congrArg (fun m => (m.portHi j).val) (runRecord_eq_of_encode_eq g xs origin hx hzero he hr)
  exact sub_left_inj.mp hh

theorem outLo_eq (he : encode g xs origin hx hzero = encode g' ys origin hy hyzero)
    {r : ℕ} (hr : r ∈ runStarts g.times) : (appendList τ r).length = (appendList τ' r).length :=
  congrArg (fun m => m.outLo.val) (runRecord_eq_of_encode_eq g xs origin hx hzero he hr)

theorem outHi_eq (he : encode g xs origin hx hzero = encode g' ys origin hy hyzero)
    {r : ℕ} (hr : r ∈ runStarts g.times) :
    (appendList τ (runEnd g.times g.finish r)).length =
      (appendList τ' (runEnd g'.times g'.finish r)).length :=
  congrArg (fun m => m.outHi.val) (runRecord_eq_of_encode_eq g xs origin hx hzero he hr)

theorem past_eq (he : encode g xs origin hx hzero = encode g' ys origin hy hyzero)
    {r : ℕ} (hr : r ∈ runStarts g.times) (h : Fin k) (hf : h ≠ g.free) :
    visitInterval (τ.work h) r = visitInterval (τ'.work h) r := by
  let j := (remainingHeads g.free).symm ⟨h, hf⟩
  have hj : (remainingHeads g.free j).val = h := congrArg Subtype.val ((remainingHeads g.free).apply_symm_apply ⟨h, hf⟩)
  have hj' : (remainingHeads g'.free j).val = h := by
    rw [← free_eq g xs origin hx hzero he]
    exact hj
  have hh := congrArg (fun m => (m.past j).map (fun x => (x.1.val, x.2.val)))
    (runRecord_eq_of_encode_eq g xs origin hx hzero he hr)
  simpa only [runRecord, pastRecord_value, hj, hj'] using hh

end Observation
end AdaptiveTransfer.Getter

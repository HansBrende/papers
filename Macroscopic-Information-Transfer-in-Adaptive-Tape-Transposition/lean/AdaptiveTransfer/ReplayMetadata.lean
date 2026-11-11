import AdaptiveTransfer.SlabGeometryAdapters

/-! Bounded geometry records built from actual unit-walk observations.
The metadata stores run endpoints, counters and extrema, not a detailed trace. -/

namespace AdaptiveTransfer

open Transpose Finset NativeRelations BoundedNesting MergeDepth

abbrev HeadCoordinate (T : ℕ) := ↑(Icc (-(T : ℤ)) (T : ℤ))
abbrev SlabCoordinate (T W : ℕ) := ↑(Icc (-(T : ℤ) - W) ((T : ℤ) + 1))

@[simp] theorem headCoordinate_card (T : ℕ) : Fintype.card (HeadCoordinate T) = 2 * T + 1 := by
  simp only [HeadCoordinate, Fintype.card_coe, Int.card_Icc]
  omega

@[simp] theorem slabCoordinate_card (T W : ℕ) :
    Fintype.card (SlabCoordinate T W) = 2 * T + W + 2 := by
  simp only [SlabCoordinate, Fintype.card_coe, Int.card_Icc]
  omega

instance (T : ℕ) : Inhabited (HeadCoordinate T) := ⟨⟨0, by simp⟩⟩

structure RunMetadata (k T : ℕ) where
  start : Fin (T + 1)
  finish : Fin (T + 1)
  outLo : Fin (T + 1)
  outHi : Fin (T + 1)
  work : Fin k → HeadCoordinate T
  raw : HeadCoordinate T
  rawLo : HeadCoordinate T
  rawHi : HeadCoordinate T
  deriving Inhabited

private def runMetadataEquiv (k T : ℕ) : RunMetadata k T ≃
    (Fin (T + 1) × Fin (T + 1) × Fin (T + 1) × Fin (T + 1) ×
      (Fin k → HeadCoordinate T) × HeadCoordinate T × HeadCoordinate T × HeadCoordinate T) where
  toFun r := (r.start, r.finish, r.outLo, r.outHi, r.work, r.raw, r.rawLo, r.rawHi)
  invFun r := ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1,
    r.2.2.2.2.2.1, r.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2⟩

noncomputable instance (k T : ℕ) : Fintype (RunMetadata k T) := by
  classical
  exact Fintype.ofEquiv _ (runMetadataEquiv k T).symm

@[simp] theorem runMetadata_card (k T : ℕ) :
    Fintype.card (RunMetadata k T) = (T + 1) ^ 4 * (2 * T + 1) ^ (k + 3) := by
  rw [Fintype.card_congr (runMetadataEquiv k T)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, headCoordinate_card,
    pow_succ, pow_zero]
  ring

structure ReplayMetadata (k T W N : ℕ) where
  free : Fin k
  ell : SlabCoordinate T W
  start : Fin (T + 1)
  finish : Fin (T + 1)
  count : Fin (N + 1)
  runs : Fin N → RunMetadata k T

def replayMetadataSize (k T W N : ℕ) : ℕ :=
  k * (N + 1) * (2 * T + W + 2) * (T + 1) ^ 2 *
    ((T + 1) ^ 4 * (2 * T + 1) ^ (k + 3)) ^ N

private def replayMetadataEquiv (k T W N : ℕ) : ReplayMetadata k T W N ≃
    (Fin k × SlabCoordinate T W × Fin (T + 1) × Fin (T + 1) ×
      Fin (N + 1) × (Fin N → RunMetadata k T)) where
  toFun g := (g.free, g.ell, g.start, g.finish, g.count, g.runs)
  invFun g := ⟨g.1, g.2.1, g.2.2.1, g.2.2.2.1, g.2.2.2.2.1, g.2.2.2.2.2⟩

noncomputable instance (k T W N : ℕ) : Fintype (ReplayMetadata k T W N) := by
  classical
  exact Fintype.ofEquiv _ (replayMetadataEquiv k T W N).symm

@[simp] theorem replayMetadata_card (k T W N : ℕ) :
    Fintype.card (ReplayMetadata k T W N) = replayMetadataSize k T W N := by
  rw [Fintype.card_congr (replayMetadataEquiv k T W N)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    slabCoordinate_card, runMetadata_card, replayMetadataSize]
  ring

noncomputable def ReplayMetadata.times {k T W N : ℕ} (g : ReplayMetadata k T W N) : Finset ℕ :=
  univ.biUnion fun i => if i.val < g.count.val then Ico (g.runs i).start.val (g.runs i).finish.val else ∅

noncomputable def runNumber (C : Finset ℕ) (i : ℕ) : ℕ :=
  if hi : i < (runStarts C).card then
    ((Fintype.equivFin (runStarts C)).symm ⟨i, by simpa only [Fintype.card_coe] using hi⟩).val else 0

theorem runNumber_mem {C : Finset ℕ} {i : ℕ} (hi : i < (runStarts C).card) :
    runNumber C i ∈ runStarts C := by
  simp only [runNumber, dite_eq_left hi]
  exact ((Fintype.equivFin (runStarts C)).symm ⟨i, by simpa only [Fintype.card_coe] using hi⟩).property

theorem exists_runNumber {C : Finset ℕ} {r : ℕ} (hr : r ∈ runStarts C) :
    ∃ i < (runStarts C).card, runNumber C i = r := by
  let i := Fintype.equivFin (runStarts C) ⟨r, hr⟩
  have hi : i.val < (runStarts C).card := by simpa only [Fintype.card_coe] using i.isLt
  refine ⟨i.val, hi, ?_⟩
  simp only [runNumber, dite_eq_left hi]
  exact congrArg Subtype.val ((Fintype.equivFin (runStarts C)).symm_apply_apply ⟨r, hr⟩)

/-- A genuine slab observation; all subsequent run records are computed. -/
structure SlabObservation {k : ℕ} (τ : Trace k) (T W N : ℕ) where
  free : Fin k
  ell : ℤ
  start : ℕ
  finish : ℕ
  start_le : start ≤ finish
  finish_le : finish ≤ T
  nonempty : (selectedSlab (τ.work free) W ell start finish).Nonempty
  run_cap : (runStarts (selectedSlab (τ.work free) W ell start finish)).card ≤ N

namespace SlabObservation

variable {k T W N : ℕ} {τ : Trace k} (g : SlabObservation τ T W N)

def times : Finset ℕ := selectedSlab (τ.work g.free) W g.ell g.start g.finish

theorem time_finish {t : ℕ} (ht : t ∈ g.times) : t < g.finish :=
  (mem_Ico.mp (mem_filter.mp ht).1).2

theorem time_start {t : ℕ} (ht : t ∈ g.times) : g.start ≤ t :=
  (mem_Ico.mp (mem_filter.mp ht).1).1

theorem time_lt {t : ℕ} (ht : t ∈ g.times) : t < T := (g.time_finish ht).trans_le g.finish_le

theorem work_bound (h : Fin k) {t : ℕ} (ht : t ≤ T) :
    -(T : ℤ) ≤ τ.work h t ∧ τ.work h t ≤ T := by
  have hh := (τ.work_isWalk h).lip (Nat.zero_le t)
  rw [τ.work_zero h] at hh
  omega

theorem input_bound {t : ℕ} (ht : t ≤ T) : -(T : ℤ) ≤ τ.input t ∧ τ.input t ≤ T := by
  have hh := (show IsWalk τ.input from τ.abs_input_succ_sub_le).lip (Nat.zero_le t)
  rw [τ.input_zero] at hh
  omega

theorem ell_bound : -(T : ℤ) - W ≤ g.ell ∧ g.ell ≤ (T : ℤ) + 1 := by
  obtain ⟨t, ht⟩ := g.nonempty
  have hpos := (mem_filter.mp ht).2
  have hb := work_bound (τ := τ) g.free (g.time_lt ht).le
  omega

theorem run_start_bound {r : ℕ} (hr : r ∈ runStarts g.times) : r ≤ T :=
  (g.time_lt (mem_filter.mp hr).1).le

theorem run_finish_bound {r : ℕ} (hr : r ∈ runStarts g.times) : runEnd g.times g.finish r ≤ T :=
  (runEnd_spec (fun _t ht => g.time_finish ht) hr).2.1.trans g.finish_le

theorem extrema_bounds {r : ℕ} (hr : r ∈ runStarts g.times) :
    (-(T : ℤ) ≤ runRawLo τ.input g.times g.finish r ∧
      runRawLo τ.input g.times g.finish r ≤ T) ∧
    (-(T : ℤ) ≤ runRawHi τ.input g.times g.finish r ∧
      runRawHi τ.input g.times g.finish r ≤ T) := by
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
  outLo := ⟨(appendList τ r).length,
    Nat.lt_succ_of_le ((length_appendList_le τ r).trans (g.run_start_bound hr))⟩
  outHi := ⟨(appendList τ (runEnd g.times g.finish r)).length,
    Nat.lt_succ_of_le ((length_appendList_le τ _).trans (g.run_finish_bound hr))⟩
  work h := ⟨τ.work h r, mem_Icc.mpr (work_bound (τ := τ) h (g.run_start_bound hr))⟩
  raw := ⟨τ.input r, mem_Icc.mpr (input_bound (τ := τ) (g.run_start_bound hr))⟩
  rawLo := ⟨runRawLo τ.input g.times g.finish r, mem_Icc.mpr (g.extrema_bounds hr).1⟩
  rawHi := ⟨runRawHi τ.input g.times g.finish r, mem_Icc.mpr (g.extrema_bounds hr).2⟩

noncomputable def encode : ReplayMetadata k T W N where
  free := g.free
  ell := ⟨g.ell, mem_Icc.mpr g.ell_bound⟩
  start := ⟨g.start, Nat.lt_succ_of_le (g.start_le.trans g.finish_le)⟩
  finish := ⟨g.finish, Nat.lt_succ_of_le g.finish_le⟩
  count := ⟨(runStarts g.times).card, Nat.lt_succ_of_le g.run_cap⟩
  runs i := if hi : i.val < (runStarts g.times).card then
    g.runRecord (runNumber g.times i.val) (runNumber_mem hi) else default

@[simp] theorem encode_times : g.encode.times = g.times := by
  classical
  ext t
  simp only [ReplayMetadata.times, mem_biUnion, mem_univ, true_and]
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

/-- Equality of metadata implies equality of the entire retained time set. -/
theorem times_eq_of_encode_eq {τ' : Trace k} {g' : SlabObservation τ' T W N}
    (he : g.encode = g'.encode) : g.times = g'.times := by
  rw [← g.encode_times, ← g'.encode_times, he]

/-- Each actual run entry has its own paid record in the padded array. -/
theorem runRecord_eq_of_encode_eq {τ' : Trace k} {g' : SlabObservation τ' T W N}
    (he : g.encode = g'.encode) {r : ℕ} (hr : r ∈ runStarts g.times) :
    g.runRecord r hr = g'.runRecord r (g.times_eq_of_encode_eq he ▸ hr) := by
  have hC := g.times_eq_of_encode_eq he
  obtain ⟨i, hi, hir⟩ := exists_runNumber hr
  have hi' : i < (runStarts g'.times).card := by simpa only [← hC] using hi
  have hnr : runNumber g'.times i = r := by simpa only [← hC] using hir
  have hh := congrArg (fun m => m.runs ⟨i, hi.trans_le g.run_cap⟩) he
  simpa only [encode, dite_eq_left hi, dite_eq_left hi', hir, hnr] using hh

end SlabObservation
end AdaptiveTransfer

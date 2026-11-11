import AdaptiveTransfer.ReplayGeometry
import AdaptiveTransfer.SlabGeometry
import AdaptiveTransfer.ReturnImports
import MergeDepth.HCStarQ91

/-! Actual extrema and append counters for the finite slab geometry.
These adapters identify the literal visited-coordinate/append-time sets with
what the bounded replay metadata describes. -/

namespace AdaptiveTransfer

open Transpose Transpose.Tape Transpose.Tape.Impl Finset NativeRelations
  BoundedNesting MergeDepth

private theorem walk_between {x : ℕ → ℤ} (hx : IsWalk x) {u v : ℕ} {z : ℤ}
    (huz : x u ≤ z) (hzv : z ≤ x v) :
    ∃ t, min u v ≤ t ∧ t ≤ max u v ∧ x t = z := by
  by_cases he : x u = z
  · exact ⟨u, min_le_left _ _, le_max_left _ _, he⟩
  have hlu : x u ≤ z - 1 := by omega
  by_cases huv : u ≤ v
  · obtain ⟨t, hut, htv, _, hval⟩ := exists_up_crossing hx (v - u) u hlu
      (by simpa only [Nat.add_sub_cancel' huv, sub_add_cancel] using hzv)
    refine ⟨t + 1, ?_, ?_, ?_⟩
    · omega
    · omega
    · simpa only [sub_add_cancel] using hval
  · have hvu : v ≤ u := by omega
    obtain ⟨t, hvt, htu, hval, _⟩ := exists_down_crossing hx (u - v) v
      (show z - 1 + 1 ≤ x v by omega)
      (by simpa only [Nat.add_sub_cancel' hvu] using hlu)
    exact ⟨t, by omega, by omega, by simpa only [sub_add_cancel] using hval⟩

/-- The image of a nonempty interval under a native unit walk is the entire
integer interval between its attained extrema. -/
theorem walk_image_Ico_eq_Icc {x : ℕ → ℤ} (hx : IsWalk x) {a e : ℕ} (hae : a < e) :
    let V := (Ico a e).image x
    V = Icc (V.min' (by exact ⟨x a, mem_image.mpr ⟨a, mem_Ico.mpr ⟨le_rfl, hae⟩, rfl⟩⟩))
      (V.max' (by exact ⟨x a, mem_image.mpr ⟨a, mem_Ico.mpr ⟨le_rfl, hae⟩, rfl⟩⟩)) := by
  dsimp only
  ext z
  constructor
  · intro hz
    exact mem_Icc.mpr ⟨min'_le _ z hz, le_max' _ z hz⟩
  · intro hz
    obtain ⟨u, hu, hxu⟩ := mem_image.mp (min'_mem ((Ico a e).image x) _)
    obtain ⟨v, hv, hxv⟩ := mem_image.mp (max'_mem ((Ico a e).image x) _)
    obtain ⟨t, hmint, htmax, hxt⟩ := walk_between hx
      (hxu ▸ (mem_Icc.mp hz).1) (hxv ▸ (mem_Icc.mp hz).2)
    exact mem_image.mpr ⟨t, mem_Ico.mpr ⟨by have := mem_Ico.mp hu; have := mem_Ico.mp hv; omega,
      by have := mem_Ico.mp hu; have := mem_Ico.mp hv; omega⟩, hxt⟩

noncomputable def runRawLo (x : ℕ → ℤ) (C : Finset ℕ) (T r : ℕ) : ℤ :=
  if h : ((Ico r (runEnd C T r)).image x).Nonempty then
    ((Ico r (runEnd C T r)).image x).min' h else 0

noncomputable def runRawHi (x : ℕ → ℤ) (C : Finset ℕ) (T r : ℕ) : ℤ :=
  if h : ((Ico r (runEnd C T r)).image x).Nonempty then
    ((Ico r (runEnd C T r)).image x).max' h else 0

theorem runRaw_extrema {x : ℕ → ℤ} {C : Finset ℕ} {T : ℕ}
    {r t : ℕ} (ht : t ∈ Ico r (runEnd C T r)) :
    runRawLo x C T r ≤ x t ∧ x t ≤ runRawHi x C T r := by
  have hv : x t ∈ (Ico r (runEnd C T r)).image x := mem_image_of_mem _ ht
  have hne : ((Ico r (runEnd C T r)).image x).Nonempty := ⟨x t, hv⟩
  simp only [runRawLo, runRawHi, dite_eq_left hne]
  exact ⟨min'_le _ _ hv, le_max' _ _ hv⟩

/-- The run extrema describe exactly the actually read raw-coordinate set. -/
theorem rawExtent_eq_visited {x : ℕ → ℤ} (hx : IsWalk x) {C : Finset ℕ} {T : ℕ}
    (hCT : ∀ t ∈ C, t < T) :
    rawExtent C (runRawLo x C T) (runRawHi x C T) = {z | ∃ t ∈ C, x t = z} := by
  ext z
  constructor
  · rintro ⟨r, hr, hlo, hhi⟩
    have hend := runEnd_spec hCT hr
    have hne : ((Ico r (runEnd C T r)).image x).Nonempty :=
      ⟨x r, mem_image.mpr ⟨r, mem_Ico.mpr ⟨le_rfl, hend.1⟩, rfl⟩⟩
    simp only [runRawLo, runRawHi, dite_eq_left hne] at hlo hhi
    have hz : z ∈ (Ico r (runEnd C T r)).image x := by
      rw [walk_image_Ico_eq_Icc hx hend.1]
      exact mem_Icc.mpr ⟨hlo, hhi⟩
    obtain ⟨t, ht, hxt⟩ := mem_image.mp hz
    exact ⟨t, hend.2.2.2 t ht, hxt⟩
  · rintro ⟨t, ht, hxt⟩
    obtain ⟨r, hr, hrt, hte⟩ := exists_run_cover hCT ht
    exact ⟨r, hr, hxt ▸ runRaw_extrema (mem_Ico.mpr ⟨hrt, hte⟩)⟩

theorem append_length_mono {k : ℕ} (τ : Trace k) : Monotone (fun t => (appendList τ t).length) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [appendList_succ, List.length_append]
  omega

theorem appendTime_in_interval_iff {k : ℕ} (τ : Trace k) {T j a e : ℕ}
    (hj : j < (appendList τ T).length) :
    appendTime τ T j ∈ Ico a e ↔
      (appendList τ a).length ≤ j ∧ j < (appendList τ e).length := by
  have hc : (appendList τ (appendTime τ T j)).length = j := by
    have hh := appendCount_appendTime τ T hj
    simp only [appendCount] at hh
    exact_mod_cast hh
  have hf : τ.appends (appendTime τ T j) := by
    rw [appendTime_eq_getElem τ T hj]
    exact (List.mem_filter.mp (List.getElem_mem hj)).2
  have hn : (appendList τ (appendTime τ T j + 1)).length = j + 1 := by
    rw [appendList_succ, List.length_append, hc, ite_eq_left hf]
    rfl
  constructor
  · intro ht
    have h₁ := append_length_mono τ (mem_Ico.mp ht).1
    have h₂ := append_length_mono τ (show appendTime τ T j + 1 ≤ e by
      have := (mem_Ico.mp ht).2; omega)
    dsimp only at h₁ h₂
    rw [hc] at h₁
    rw [hn] at h₂
    exact ⟨h₁, by omega⟩
  · rintro ⟨h₁, h₂⟩
    apply mem_Ico.mpr
    constructor
    · by_contra h
      have hh := append_length_mono τ (show appendTime τ T j + 1 ≤ a by omega)
      dsimp only at hh
      rw [hn] at hh
      omega
    · by_contra h
      have hh := append_length_mono τ (show e ≤ appendTime τ T j by omega)
      dsimp only at hh
      rw [hc] at hh
      omega

theorem native_output_count (M : TM) (w : List Bool) (t : ℕ) :
    (run M w t).outRev.length = (appendList (trace M w) t).length := by
  rw [← List.length_reverse, outRev_reverse_eq, List.length_filterMap_eq_countP,
    List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro s _
  exact outBit_isSome_eq s

/-- The ordinal interval in each run is exactly its set of actual appends. -/
theorem recordedOrdinals_eq_outIn {k P T : ℕ} (τ : Trace k)
    (hP : P ≤ (appendList τ T).length) {C : Finset ℕ}
    (hCT : ∀ t ∈ C, t < T) :
    recordedOrdinals P C (fun r => (appendList τ r).length)
      (fun r => (appendList τ (runEnd C T r)).length) =
    outIn (fun j : Fin P => appendTime τ T j.val) C := by
  ext j
  simp only [recordedOrdinals, outIn, mem_biUnion, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨r, hr, hj⟩
    exact (runEnd_spec hCT hr).2.2.2 _
      ((appendTime_in_interval_iff τ (j.isLt.trans_le hP)).mpr hj)
  · intro hj
    obtain ⟨r, hr, hrt, hte⟩ := exists_run_cover hCT hj
    exact ⟨r, hr, (appendTime_in_interval_iff τ (j.isLt.trans_le hP)).mp
      (mem_Ico.mpr ⟨hrt, hte⟩)⟩

theorem geometryOmitted_eq_omittedSlabBits {d b T : ℕ} {k : ℕ} (τ : Trace k)
    (hP : d * d * b ≤ (appendList τ T).length) {C : Finset ℕ}
    (hCT : ∀ t ∈ C, t < T) :
    geometryOmitted (tposOf d b) C (fun r => (appendList τ r).length)
      (fun r => (appendList τ (runEnd C T r)).length)
      (runRawLo τ.input C T) (runRawHi τ.input C T) =
    omittedSlabBits d b τ.input (fun j => appendTime τ T j.val) C := by
  classical
  rw [geometryOmitted, recordedOrdinals_eq_outIn τ hP hCT,
    rawExtent_eq_visited τ.abs_input_succ_sub_le hCT]
  simp only [omittedSlabBits, inCells, Set.mem_ofPred_eq]

end AdaptiveTransfer

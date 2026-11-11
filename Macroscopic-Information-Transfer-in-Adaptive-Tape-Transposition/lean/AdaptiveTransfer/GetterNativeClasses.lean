import AdaptiveTransfer.GetterNativeGeometry
import AdaptiveTransfer.NativeReplayEstimates

/-! Equal actual port metadata yields a native getter replay class. The
ordinary imported values, virtual observer state, and strict output prefix
are all recovered by the proved replay chain rather than class fields.
-/

namespace AdaptiveTransfer.Getter
open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth BoundedNesting NativeRelations Finset LeanMachine
open scoped BigOperators

theorem omittedByExtent_eq_portBits {d b k p S T R : ℕ} (τ : Trace k)
    (hP : d * d * b ≤ (appendList τ T).length) (xs : Fin p → ℕ → ℤ)
    {C : Finset ℕ} (hCS : ∀ t ∈ C, t < S) (hCT : ∀ t ∈ C, t < T) :
    omittedByExtent (tposOf d b) C (fun r => (appendList τ r).length)
      (fun r => (appendList τ (runEnd C S r)).length)
      (portExtent C (fun r j => runRawLo (xs j) C S r) (fun r j => runRawHi (xs j) C S r) R) =
    omittedPortBits xs (fun j => appendTime τ T j.val) C S R := by
  classical
  have hO : recordedOrdinals (d * d * b) C (fun r => (appendList τ r).length)
      (fun r => (appendList τ (runEnd C S r)).length) =
      outIn (fun j : Fin (d * d * b) => appendTime τ T j.val) C := by
    rw [← recordedOrdinals_eq_outIn τ hP hCT]
    apply biUnion_congr rfl
    intro r hr
    dsimp only
    simp only [runEnd_eq_of_caps hCS hCT hr]
  unfold omittedByExtent omittedPortBits
  rw [hO]
  congr 1
  ext q
  simp only [mem_filter, mem_univ, true_and, mem_portBits_iff]

section Classes
variable {M : TM} {U Λ : Type*}
  {v R d b T W N H J q z a : ℕ} {c : ℝ}
  (A : Observer M U v R) (G : Getters M U Λ v R)
  (D : Finset (Fin (d * d * b) → Bool))
  (correct : ∀ X : D, TransposesInput M d b c X.val)
  (labels : D → Λ)
  (obs : ∀ X : D, SlabObservation (trace M (List.ofFn X.val)) T W N)
  (finish_le : ∀ X : D, (obs X).finish ≤ (trace M (List.ofFn X.val)).haltTime)
  (errors : ∀ X : D, (nativeErrors A G (obs X).free (labels X) (List.ofFn X.val)
    (trace M (List.ofFn X.val)).haltTime H).card ≤ J)
  (X₀ : D)
  (same : ∀ X : D,
    Observation.encode (obs X) (A.paths (List.ofFn X.val)) A.publicOrigins
      (A.paths_walk _) (A.paths_zero _) =
    Observation.encode (obs X₀) (A.paths (List.ofFn X₀.val)) A.publicOrigins
      (A.paths_walk _) (A.paths_zero _))

private def classPrefix (X : D) : ExecutionPrefix M (List.ofFn X.val) (obs X₀).finish :=
  ExecutionPrefix.ofRun M (List.ofFn X.val) (obs X₀).finish fun t ht =>
    (timely_native_data (correct X)).2.1 t (lt_of_lt_of_le
      (by simpa only [Observation.finish_eq _ _ _ _ _ (same X)] using ht) (finish_le X))

include same in
private theorem times_same (X : D) : (obs X).times = (obs X₀).times :=
  Observation.times_eq_of_encode_eq _ _ _ _ _ (same X)

include same in
private theorem free_same (X : D) : (obs X).free = (obs X₀).free :=
  Observation.free_eq _ _ _ _ _ (same X)

include errors in
private theorem native_port_tags (X : D) :
    (recordSupport (fun _ => none)
      (errorFields (classPrefix A D correct obs finish_le X₀ same X) A G (labels X) T H
        (obs X₀).times (replayEntry (obs X₀).times (obs X₀).finish
          (fun _t ht => (obs X₀).time_finish ht)) (obs X₀).free)).card ≤ J := by
  have hh := native_error_support (T := (trace M (List.ofFn X.val)).haltTime)
    (fun t ht => (timely_native_data (correct X)).2.1 t (lt_of_lt_of_le
      (by simpa only [Observation.finish_eq _ _ _ _ _ (same X)] using ht) (finish_le X)))
    A G (labels X) T H (obs X₀).times
    (replayEntry (obs X₀).times (obs X₀).finish (fun _t ht => (obs X₀).time_finish ht))
    (obs X₀).free (fun _t ht => (obs X₀).time_finish ht)
    (fun _t ht => (replayEntry_spec (fun _t ht => (obs X₀).time_finish ht) ht).2.1)
    (by rw [← Observation.finish_eq _ _ _ _ _ (same X)]; exact finish_le X)
  exact hh.trans (by simpa only [free_same A D obs X₀ same X] using errors X)

variable [Fintype U] [Fintype Λ]

include correct finish_le errors same in
/-- Actual equal-metadata native class, with exactly the retained bits,
one label, augmented state, snapshot and sparse correction bill. -/
theorem native_port_class_bits
    (hq : (M.q + 1) * Fintype.card U ≤ 2 ^ q) (hz : Fintype.card Λ ≤ 2 ^ z) :
    D.card ≤
      2 ^ (d * d * b - (omittedPortBits (d := d) (b := b) (A.paths (List.ofFn X₀.val))
        (fun j => appendTime (trace M (List.ofFn X₀.val)) (trace M (List.ofFn X₀.val)).haltTime j.val)
        (obs X₀).times (obs X₀).finish R).card + z + (runStarts (obs X₀).times).card * q) *
      (M.g + 1) ^ ((if (obs X₀).start = 0 then 0 else W) +
        (M.k - 1) * (runStarts (obs X₀).times).card * (2 * H + 1)) *
      ∑ j ∈ range (min ((M.k - 1) * T) J + 1), ((M.k - 1) * T).choose j * (M.g + 1) ^ j := by
  classical
  let g := obs X₀
  let τ := trace M (List.ofFn X₀.val)
  let ps := A.paths (List.ofFn X₀.val)
  have hcorrect := (timely_native_data (correct X₀)).2.2
  have happ : d * d * b = (appendList τ τ.haltTime).length := by
    rw [← native_output_count, ← List.length_reverse, hcorrect, List.length_ofFn]
  have hbound := native_fixed_geometry_bits_bound D (classPrefix A D correct obs finish_le X₀ same)
    A G labels (tposOf d b) (Function.Involutive.injective (tposOf_tposOf d b))
    g.times (Ico g.ell (g.ell + (W : ℤ))) g.start H T J q z g.free
    (fun _t ht => g.time_finish ht) (fun _t ht => g.time_start ht) g.finish_le
    (workEntry := fun r => fun h => τ.work h r)
    (portEntry := fun r j => ps j r)
    (portLo := fun r j => runRawLo (ps j) g.times g.finish r)
    (portHi := fun r j => runRawHi (ps j) g.times g.finish r)
    (past := fun r h => visitInterval (τ.work h) r)
    (outLo := fun r => (appendList τ r).length)
    (outHi := fun r => (appendList τ (runEnd g.times g.finish r)).length)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ (native_port_tags A G D correct labels obs finish_le errors X₀ same)
    (fun X => (trace M (List.ofFn X.val)).haltTime) ?_
    (fun X => (timely_native_data (correct X)).2.2) hq hz
  · rw [omittedByExtent_eq_portBits τ happ.le ps (fun _t ht => g.time_finish ht)
      (fun _t ht => (g.time_finish ht).trans_le (finish_le X₀)), integerSlab_card] at hbound
    exact hbound
  · intro X t ha ht
    dsimp only [g] at ha ⊢
    change t ∈ g.times ↔ (run M (List.ofFn X.val) t).workPos g.free ∈ _
    rw [workPos_eq_work, ← free_same A D obs X₀ same X, ← times_same A D obs X₀ same X]
    simp only [SlabObservation.times, selectedSlab, mem_filter, mem_Ico,
      Observation.start_eq _ _ _ _ _ (same X), Observation.finish_eq _ _ _ _ _ (same X),
      Observation.ell_eq _ _ _ _ _ (same X), ha, ht, true_and]
  · intro X r hr
    funext h
    change (run M (List.ofFn X.val) r).workPos h = τ.work h r
    rw [workPos_eq_work]
    exact Observation.work_eq _ _ _ _ _ (same X) (by rwa [times_same A D obs X₀ same X]) h
  · intro X r hr
    funext j
    exact Observation.ports_eq _ _ _ _ _ (same X) (by rwa [times_same A D obs X₀ same X]) j
  · intro X r hr h hf
    simp only [workPos_eq_work]
    exact Observation.past_eq _ _ _ _ _ (same X) (by rwa [times_same A D obs X₀ same X]) h
      (by simpa only [free_same A D obs X₀ same X] using hf)
  · intro X r hr
    change (run M (List.ofFn X.val) r).outRev.length = _
    rw [native_output_count]
    exact Observation.outLo_eq _ _ _ _ _ (same X) (by rwa [times_same A D obs X₀ same X])
  · intro X r hr
    change (run M (List.ofFn X.val) (runEnd g.times g.finish r)).outRev.length = _
    rw [native_output_count]
    have hh := Observation.outHi_eq _ _ _ _ _ (same X) (by rwa [times_same A D obs X₀ same X])
    simpa only [times_same A D obs X₀ same X, Observation.finish_eq _ _ _ _ _ (same X)] using hh
  · intro X r hr t ht j
    have hlo := Observation.portLo_eq _ _ _ _ _ (same X) (by rwa [times_same A D obs X₀ same X]) j
    have hhi := Observation.portHi_eq _ _ _ _ _ (same X) (by rwa [times_same A D obs X₀ same X]) j
    have hh := runRaw_extrema (x := A.paths (List.ofFn X.val) j)
      (C := (obs X).times) (T := (obs X).finish)
      (by simpa only [times_same A D obs X₀ same X, Observation.finish_eq _ _ _ _ _ (same X)] using ht)
    exact ⟨hlo ▸ hh.1, hhi ▸ hh.2⟩
  · intro X
    rw [← Observation.finish_eq _ _ _ _ _ (same X)]
    exact finish_le X

include correct finish_le errors same in
/-- The actual class estimate after its geometric snapshot saving. -/
theorem native_port_class_saving
    (hq : (M.q + 1) * Fintype.card U ≤ 2 ^ q) (hz : Fintype.card Λ ≤ 2 ^ z)
    (hA : M.g + 1 ≤ 2 ^ a) (saving : ℝ)
    (hsaving : saving ≤
      ((omittedPortBits (d := d) (b := b) (A.paths (List.ofFn X₀.val))
        (fun j => appendTime (trace M (List.ofFn X₀.val)) (trace M (List.ofFn X₀.val)).haltTime j.val)
        (obs X₀).times (obs X₀).finish R).card : ℝ) -
      (a : ℝ) * (if (obs X₀).start = 0 then 0 else (W : ℝ))) :
    (D.card : ℝ) ≤
      (2 : ℝ) ^ ((d * d * b : ℕ) - saving + z + (N : ℝ) * q +
        (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * H + 1)) *
      (returnSparseMenu M.k T J (M.g + 1) : ℝ) := by
  let u := omittedPortBits (d := d) (b := b) (A.paths (List.ofFn X₀.val))
    (fun j => appendTime (trace M (List.ofFn X₀.val)) (trace M (List.ofFn X₀.val)).haltTime j.val)
    (obs X₀).times (obs X₀).finish R
  let r := (runStarts (obs X₀).times).card
  let snap := if (obs X₀).start = 0 then 0 else W
  have hu : u.card ≤ d * d * b := by simpa only [Fintype.card_fin] using card_le_univ u
  have hsparse : (∑ j ∈ range (min ((M.k - 1) * T) J + 1),
      ((M.k - 1) * T).choose j * (M.g + 1) ^ j) ≤ returnSparseMenu M.k T J (M.g + 1) := by
    unfold returnSparseMenu
    rw [← sparseMenu_truncate, ← sparseMenu_truncate]
    exact sum_le_sum fun j _ => Nat.mul_le_mul_right _
      (Nat.choose_le_choose j (Nat.mul_le_mul_right _ (Nat.sub_le M.k 1)))
  have hh := native_port_class_bits A G D correct labels obs finish_le errors X₀ same hq hz
  have hn : D.card ≤ 2 ^ (d * d * b - u.card + z + r * q +
      a * (snap + (M.k - 1) * r * (2 * H + 1))) * returnSparseMenu M.k T J (M.g + 1) := by
    calc
      D.card ≤ _ := hh
      _ ≤ (2 ^ (d * d * b - u.card + z + r * q) *
          (2 ^ a) ^ (snap + (M.k - 1) * r * (2 * H + 1))) * returnSparseMenu M.k T J (M.g + 1) := by
        gcongr
      _ = _ := by rw [← pow_mul, ← pow_add]
  have hbits : ((d * d * b - u.card + z + r * q +
      a * (snap + (M.k - 1) * r * (2 * H + 1)) : ℕ) : ℝ) ≤
      (d * d * b : ℕ) - saving + z + (N : ℝ) * q +
        (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * H + 1) := by
    have hr : (r : ℝ) ≤ N := by exact_mod_cast (obs X₀).run_cap
    have hq' := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg q)
    have hw := mul_le_mul_of_nonneg_left hr
      (show 0 ≤ (a : ℝ) * (M.k - 1 : ℕ) * (2 * H + 1) by positivity)
    change saving ≤ (u.card : ℝ) - _ at hsaving
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hu, snap]
    split_ifs at hsaving ⊢ <;> push_cast <;> nlinarith
  have hh' : (D.card : ℝ) ≤
      (2 : ℝ) ^ ((d * d * b - u.card + z + r * q +
        a * (snap + (M.k - 1) * r * (2 * H + 1)) : ℕ) : ℝ) *
      (returnSparseMenu M.k T J (M.g + 1) : ℝ) := by exact_mod_cast hn
  exact hh'.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hbits) (by positivity))

end Classes
end AdaptiveTransfer.Getter

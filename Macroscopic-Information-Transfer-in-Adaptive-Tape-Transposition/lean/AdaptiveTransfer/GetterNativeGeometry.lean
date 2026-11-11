import AdaptiveTransfer.GetterMetadata
import AdaptiveTransfer.GetterSlabGeometry
import AdaptiveTransfer.GetterReturns
import AdaptiveTransfer.NativeTimelyData
import AdaptiveTransfer.NativeReturnCounting

/-! Canonical native observers, whole-run discrepancy events and actual
multiport slab witnesses. No common detailed trace is required.
-/

namespace AdaptiveTransfer.Getter
open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth BoundedNesting NativeRelations Finset LeanMachine

variable {M : TM} {U Λ : Type*} {v R : ℕ}

namespace Observer
variable (A : Observer M U v R)

def paths (w : List Bool) : Fin (v + 1) → ℕ → ℤ := fun j t => A.allPorts w t j
def publicOrigins : Fin (v + 1) → ℤ := Fin.cases 0 A.origins

theorem paths_walk (w : List Bool) (j : Fin (v + 1)) : IsWalk (A.paths w j) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · intro t
    change |(Transpose.Tape.run M w (t + 1)).inPos - (Transpose.Tape.run M w t).inPos| ≤ 1
    simpa only [inPos_eq_input] using (trace M w).abs_input_succ_sub_le t
  · exact fun t => A.virtual_unit w t j

theorem paths_zero (w : List Bool) (j : Fin (v + 1)) : A.paths w j 0 = A.publicOrigins j := by
  refine Fin.cases ?_ (fun _ => rfl) j
  rfl

end Observer

/-- Errors are fixed on the original entire native run, before any slab is
chosen. In particular the actual old symbol, not the final archive, is tested. -/
noncomputable def nativeErrors (A : Observer M U v R) (G : Getters M U Λ v R)
    (f : Fin M.k) (label : Λ) (w : List Bool) (T H : ℕ) : Finset (Fin M.k × ℕ × ℕ) :=
  (offCarrierReturns (trace M w).work f T H).filter fun e =>
    (run M w e.2.2).work e.1 ((run M w e.2.2).workPos e.1) ≠
      prediction A G f label w e.2.2 e.1

theorem nativeErrors_mono (A : Observer M U v R) (G : Getters M U Λ v R)
    (f : Fin M.k) (label : Λ) (w : List Bool) (H : ℕ) {S T : ℕ} (hST : S ≤ T) :
    nativeErrors A G f label w S H ⊆ nativeErrors A G f label w T H :=
  filter_subset_filter _ (offCarrierReturns_mono _ _ H hST)

theorem native_error_support {P S T : ℕ} {X : Fin P → Bool}
    (hsuccess : ∀ t < S, transAt M (List.ofFn X) t ≠ none)
    (A : Observer M U v R) (G : Getters M U Λ v R) (label : Λ)
    (N H : ℕ) (C : Finset ℕ) (entry : ℕ → ℕ) (f : Fin M.k)
    (hCT : ∀ t ∈ C, t < S) (hentry : ∀ t ∈ C, entry t ≤ t) (hST : S ≤ T) :
    (recordSupport (fun _ => none)
      (errorFields (ExecutionPrefix.ofRun M (List.ofFn X) S hsuccess)
        A G label N H C entry f)).card ≤
      (nativeErrors A G f label (List.ofFn X) T H).card := by
  have hh := error_support_le_returns (ExecutionPrefix.ofRun M (List.ofFn X) S hsuccess)
    A G label N H C entry f hCT hentry
  have he : errorReturns (ExecutionPrefix.ofRun M (List.ofFn X) S hsuccess) A G f label H =
      nativeErrors A G f label (List.ofFn X) S H := by
    simp only [errorReturns, nativeErrors, ExecutionPrefix.ofRun]
    congr 2
    funext h t
    exact workPos_eq_work h t
  rw [he] at hh
  exact hh.trans (card_le_card (nativeErrors_mono A G f label _ H hST))

/-- A maximal run endpoint is independent of a later ambient cap. -/
theorem runEnd_eq_of_caps {C : Finset ℕ} {S T r : ℕ}
    (hCS : ∀ t ∈ C, t < S) (hCT : ∀ t ∈ C, t < T) (hr : r ∈ runStarts C) :
    runEnd C S r = runEnd C T r := by
  have hs := runEnd_spec hCS hr
  have ht := runEnd_spec hCT hr
  rcases lt_trichotomy (runEnd C S r) (runEnd C T r) with h | h | h
  · exact False.elim (hs.2.2.1 (ht.2.2.2 _ (mem_Ico.mpr ⟨hs.1.le, h⟩)))
  · exact h
  · exact False.elim (ht.2.2.1 (hs.2.2.2 _ (mem_Ico.mpr ⟨ht.1.le, h⟩)))

theorem portBits_eq_of_caps {p P S T R : ℕ} (xs : Fin p → ℕ → ℤ) {C : Finset ℕ}
    (hCS : ∀ t ∈ C, t < S) (hCT : ∀ t ∈ C, t < T) :
    portBits P xs C S R = portBits P xs C T R := by
  apply biUnion_congr rfl
  intro r hr
  simp only [runRawLo, runRawHi, runEnd_eq_of_caps hCS hCT hr]

/-- Positive saving supplies a nonempty literal slab on this input's own
trace. The carrier and label have been fixed before selecting that slab. -/
theorem native_port_observation {d b a H J : ℕ} {c : ℝ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (ha : 1 ≤ a) (hP : 4 * (v + 1) ≤ d * d * b)
    (hc : 1 ≤ c) (hR : R ≤ (d * d * b) / (8 * (v + 1) * portRunCap a (v + 1) c))
    (A : Observer M U v R) (G : Getters M U Λ v R)
    {X : Fin (d * d * b) → Bool} (hcorrect : TransposesInput M d b c X)
    (f : Fin M.k) (label : Λ)
    (herrors : (nativeErrors A G f label (List.ofFn X) (trace M (List.ofFn X)).haltTime H).card ≤ J)
    (hsaving : 0 < portSaving d b a (v + 1) c) :
    ∃ g : SlabObservation (trace M (List.ofFn X)) (returnTime (d * d * b) c)
      (portSlabWidth (d * d * b) a (v + 1) c) (portRunCap a (v + 1) c),
      g.free = f ∧ g.finish ≤ (trace M (List.ofFn X)).haltTime ∧
      (nativeErrors A G g.free label (List.ofFn X) (trace M (List.ofFn X)).haltTime H).card ≤ J ∧
      portSaving d b a (v + 1) c ≤
        ((omittedPortBits (d := d) (b := b) (A.paths (List.ofFn X))
          (fun j => appendTime (trace M (List.ofFn X)) (trace M (List.ofFn X)).haltTime j.val)
          g.times g.finish R).card : ℝ) -
        (a : ℝ) * (if g.start = 0 then 0 else (portSlabWidth (d * d * b) a (v + 1) c : ℝ)) := by
  classical
  let τ := trace M (List.ofFn X)
  have hX : X ∈ fibre M (d * d * b) τ := mem_fibre.mpr rfl
  obtain ⟨hT, happ⟩ := fibre_haltTime hX hcorrect
  have hPpos : 0 < d * d * b := by nlinarith
  have hTpos := prefix_pos hd hb happ.ge
  have hot : StrictMono (fun j : Fin (d * d * b) => appendTime τ τ.haltTime j.val) := by
    intro i j hij
    exact appendTime_strictMonoOn τ τ.haltTime
      (by simpa only [Set.mem_Iio, happ] using i.isLt)
      (by simpa only [Set.mem_Iio, happ] using j.isLt) hij
  obtain ⟨ell, s, e, hse, he, _hcap, hruns, hmargin⟩ := exists_port_slab_geometry
    hd hb ha (Nat.succ_pos v) hP hc hR (A.paths_walk (List.ofFn X)) (τ.work_isWalk f) hot
    (fun j => appendTime_lt τ τ.haltTime (by simpa only [happ] using j.isLt))
    (runtime_le hPpos hTpos hT)
  let C := selectedSlab (τ.work f) (portSlabWidth (d * d * b) a (v + 1) c) ell s e
  have hne : C.Nonempty := by
    by_contra hn
    have hemp := not_nonempty_iff_eq_empty.mp hn
    have hU : omittedPortBits (d := d) (b := b) (A.paths (List.ofFn X))
        (fun j => appendTime τ τ.haltTime j.val) C τ.haltTime R = ∅ := by
      simp [omittedPortBits, outIn, hemp]
    change portSaving d b a (v + 1) c ≤
      ((omittedPortBits _ _ C _ _).card : ℝ) - _ at hmargin
    rw [hU, card_empty, Nat.cast_zero] at hmargin
    have hcost : 0 ≤ (a : ℝ) * (if s = 0 then 0 else (portSlabWidth (d * d * b) a (v + 1) c : ℝ)) := by
      split_ifs <;> positivity
    linarith
  let g : SlabObservation τ (returnTime (d * d * b) c)
      (portSlabWidth (d * d * b) a (v + 1) c) (portRunCap a (v + 1) c) :=
    ⟨f, ell, s, e, hse, he.trans (timely_native_data hcorrect).1, hne, hruns⟩
  refine ⟨g, rfl, he, herrors, ?_⟩
  have heq : portBits (d * d * b) (A.paths (List.ofFn X)) g.times g.finish R =
      portBits (d * d * b) (A.paths (List.ofFn X)) g.times τ.haltTime R :=
    portBits_eq_of_caps _ (fun _t ht => g.time_finish ht) (fun _t ht => (g.time_finish ht).trans_le he)
  simp only [omittedPortBits, heq]
  exact hmargin

end AdaptiveTransfer.Getter

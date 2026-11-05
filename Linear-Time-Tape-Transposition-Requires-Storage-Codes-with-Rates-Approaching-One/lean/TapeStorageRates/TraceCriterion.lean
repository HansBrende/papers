import BoundedStackDepth.LowAdaptivity
import MergeDepth.InputSteering

/-! # The native half-rate obstruction in terms of full motion-trace support -/

namespace TapeStorageRates

open Finset Filter MergeDepth BoundedStackDepth Transpose Transpose.Tape Transpose.Tape.Impl

set_option autoImplicit false

/-- At every scale the normalized skeleton is a function of the motion trace, including
halt time and the output counter; the values of the output bits play no role. -/
noncomputable def skeletonOfTrace {k : ℕ} (w : ℕ) (τ : Trace k) : Skeleton k where
  T := τ.haltTime
  s0 t := if t < τ.haltTime then τ.input t / w else 0
  s j t := if t < τ.haltTime then τ.work j t / w else 0
  sout t := if t < τ.haltTime then (appendList τ t).length / w else 0

/-- The physical output length counts exactly the append flags of the complete trace. -/
theorem outRev_length_eq_appendList (M : TM) (x : List Bool) (t : ℕ) :
    (run M x t).outRev.length = (appendList (trace M x) t).length := by
  rw [← List.length_reverse, outRev_reverse_eq, List.length_filterMap_eq_countP,
    List.countP_eq_length_filter]
  exact congrArg List.length (List.filter_congr fun j _ => outBit_isSome_eq j)

theorem skeletonOfTrace_eq (M : TM) (w : ℕ) (x : List Bool) :
    skeletonOfTrace w (trace M x) = runSkeleton M w x := by
  simp only [skeletonOfTrace, runSkeleton, inPos_eq_input, workPos_eq_work, outRev_length_eq_appendList]

open Classical in
/-- The complete motion-trace support bounds the entropy that Paper 14 actually measures,
also on arbitrary finite input ensembles. -/
theorem skeleton_entropy_le_trace_support {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (M : TM) (w : ℕ) (inputs : Ω → List Bool) :
    entropy (fun x => runSkeleton M w (inputs x)) ≤
      Real.logb 2 (univ.image (fun x => trace M (inputs x))).card := by
  simpa only [Function.comp_def, skeletonOfTrace_eq] using
    (entropy_comp_le (fun x => trace M (inputs x)) (skeletonOfTrace w)).trans
      (entropy_le_logb_card (fun x => trace M (inputs x)))

open Classical in
/-- A native hypothesis at the simulator's exact scale-one width and depth excludes every
source dimension property transmitted to this simulator with small trace support. Any
threshold below one half is allowed; the paper takes one quarter. -/
theorem native_exclusion_of_trace_support (N : TM) {c η : ℝ} (hc : 0 < c) (hη : η < 1/2)
    (hnative : NativeBound (fun d b => b = entryBits d) N 1
      (genieDepth N.k (blockWidth N 1) (max c 1) ((1/2-η)/2)) c)
    (Good : ℕ → Prop)
    (htransfer : ∀ᶠ d in atTop, Good d → TransposesAt N d c ∧
      Real.logb 2 (univ.image (fun x : Fin (d*d*entryBits d) → Bool => trace N (List.ofFn x))).card
        ≤ η * (d*d*entryBits d : ℕ)) :
    ∀ᶠ d in atTop, ¬ Good d := by
  obtain ⟨d₀, h₀⟩ := fSecond_native hc hη hnative
  filter_upwards [eventually_ge_atTop d₀, htransfer] with d hd h
  intro hgood
  obtain ⟨hsuccess, hsize⟩ := h hgood
  have hlow := (skeleton_entropy_le_trace_support N 1
    (fun x : Fin (d*d*entryBits d) → Bool => List.ofFn x)).trans hsize
  exact (not_lt_of_ge hlow) (h₀ d hd _ rfl (one_le_entryBits d) hsuccess.transposesInput)

end TapeStorageRates

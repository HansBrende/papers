import TapeStorageRates.NativeJointCut
import TapeStorageRates.NativeCoarseGeometry
import TapeStorageRates.NativeBatchRecordReplay

/-! # The joint-support genie for every actual compiler replay -/

namespace TapeStorageRates

open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth BoundedNesting
open BatchCoarsening NativeBatchRecord

set_option autoImplicit false
noncomputable section
open Classical

/-- Actual batch sweeps supply every geometric and local-record premise. -/
theorem native_joint_replay_cut (M : TM) {s : ℕ} (hs : 0 < s)
    (r : Fin s) (as : List (Native.Descriptor M.k))
    {X : Type*} (word : X → List Bool) (S : Finset X) {c : ℝ} {L : ℕ}
    (hsize : ((9*as.length+1 : ℕ):ℝ) ≤ (nativeJointClock c : ℝ)*L/s)
    (htrace : ∀ x ∈ S, trace (Native.machine M hs) (word x) = Native.replay r as) :
    ∃ Γ : Finset ℕ,
      ((S.image (fun x => fun t : Γ => blockVal (Native.machine M hs) 1 (word x) t)).card : ℝ) ≤
        (2:ℝ)^((L:ℝ)/s) ∧
      ∀ π, IsDepPath (Native.replay r as).work ((10*s+1)*as.length+s) π →
        LinNet.GFree Γ π → π.length ≤ jointPhysicalDepth M.k (nativeJointCoefficient M c) s+1 := by
  let C := (Native.replay_completeCover hs r as).toCoarsening
  apply exists_joint_cut_of_coarsening M hs word S (Native.replay r as)
    (by omega : 0 < 9*as.length+1) (nativeJointClock_pos c)
    (Native.coarseWork as) (Native.coarseWork_isWalk as) C hsize
    (range (as.length+1)) (fun j => (10*s+1)*j)
    (fun j => min ((10*s+1)*as.length+s) ((10*s+1)*(j+1))) ?_ htrace
    (replay_window_intervals hs r as _) ?_
  · intro q hq
    change q/9 ∈ range (as.length+1)
    rw [mem_range]
    omega
  · intro t ht
    constructor
    · simpa only [Nat.mul_comm] using Nat.div_mul_le_self t (10*s+1)
    · apply lt_min ht
      have h := (Nat.div_lt_iff_lt_mul (by omega : 0<10*s+1)).mp
        (Nat.lt_succ_self (t/(10*s+1)))
      simpa only [Nat.mul_comm] using h

end
end TapeStorageRates

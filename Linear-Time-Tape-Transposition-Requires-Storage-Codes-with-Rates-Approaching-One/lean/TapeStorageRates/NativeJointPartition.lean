import TapeStorageRates.NativeJointReplay
import TapeStorageRates.NativeJointTrace

/-! # Typical native fibres from joint batch revelation -/

namespace TapeStorageRates

open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth BoundedNesting

set_option autoImplicit false
noncomputable section
open Classical

/-- A native geometry witness on any common compiler trace of timely correct source inputs. -/
theorem native_joint_typical_cut (M : TM) {s : ℕ} (hs : 0 < s)
    {c : ℝ} (hc : 0 ≤ c) {d b : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b)
    (hL : 11*s+1 ≤ d*d*b+1)
    {S : Finset (Fin (d*d*b) → Bool)} {x₀ : Fin (d*d*b) → Bool} (hx₀ : x₀ ∈ S)
    (hsource : ∀ x ∈ S, TransposesInput M d b c x)
    (htr : ∀ x ∈ S, trace (Native.machine M hs) (List.ofFn x) =
      trace (Native.machine M hs) (List.ofFn x₀)) (θ r : ℕ) :
    Nonempty (NativeTypicalCut (Native.machine M hs) d b (11*c+1) (1/(s:ℝ)) θ r S
      (jointPhysicalDepth M.k (nativeJointCoefficient M c) s)) := by
  obtain ⟨t,ht,hhalt⟩ := (hsource x₀ hx₀).halts
  obtain ⟨as,res,hlen,hreplay⟩ := native_source_replay M hs (List.ofFn x₀) hhalt
  have htR : (t:ℝ) ≤ c*((d*d*b:ℕ)+1) :=
    (Nat.cast_le.mpr ht).trans (Nat.floor_le (by positivity))
  have hsize : ((9*as.length+1:ℕ):ℝ) ≤ (nativeJointClock c:ℝ)*(d*d*b:ℕ)/s := by
    rw [hlen]
    exact native_joint_clock_bound hc hs (by omega) htR
  obtain ⟨Γ,hcount,hpath⟩ := native_joint_replay_cut M hs res as List.ofFn S hsize
    (fun x hx => (htr x hx).trans hreplay)
  have hnative : HaltsAt (Native.machine M hs) (List.ofFn x₀) ((10*s+1)*as.length+s) :=
    (haltsAt_iff_trace _).mpr (by rw [hreplay]; exact Native.replay_haltsAt res as)
  obtain ⟨hgood,-⟩ := native_success_resources M hs hc hL S hsource
  apply native_typical_cut_of_trace_genie (Native.machine M hs) hd hb (by linarith) hx₀
    htr hgood θ r hnative Γ
  · simpa only [one_div_mul_eq_div] using hcount
  · simpa only [hreplay] using hpath

/-- One joint-support cut policy on each attained native trace, fixed before confidence levels. -/
theorem native_joint_typical_partition (M : TM) {s : ℕ} (hs : 0 < s)
    {c : ℝ} (hc : 0 ≤ c) {d b : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b)
    (hL : 11*s+1 ≤ d*d*b+1) (G : Finset (Fin (d*d*b) → Bool))
    (hsource : ∀ x ∈ G, TransposesInput M d b c x) (θ r : ℕ) :
    Nonempty (NativeTypicalPartition (Native.machine M hs) d b (11*c+1) (1/(s:ℝ)) θ r G
      (jointPhysicalDepth M.k (nativeJointCoefficient M c) s)) := by
  refine ⟨⟨fun τ => Classical.choice ?_⟩⟩
  obtain ⟨x₀,hx₀,he⟩ := mem_image.mp τ.property
  have hxS : x₀ ∈ nativeTraceSlice (Native.machine M hs) G τ := mem_filter.mpr ⟨hx₀,he⟩
  exact native_joint_typical_cut M hs hc hd hb hL hxS
    (fun x hx => hsource x (mem_filter.mp hx).1)
    (fun _ hx => (mem_filter.mp hx).2.trans he.symm) θ r

end
end TapeStorageRates

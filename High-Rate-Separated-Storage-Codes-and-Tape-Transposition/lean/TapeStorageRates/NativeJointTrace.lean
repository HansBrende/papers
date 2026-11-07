import TapeStorageRates.NativeJointCut
import TapeStorageRates.NativeTypical
import TapeStorageRates.NativeTypicalResources

/-! # Source runtimes and physical trace genies on a native skeleton -/

namespace TapeStorageRates

open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth BoundedNesting

set_option autoImplicit false
noncomputable section
open Classical

/-- The actual compiler's descriptor count is exactly determined by the source halt time. -/
theorem native_source_replay (M : TM) {s : ℕ} (hs : 0 < s) (w : List Bool)
    {t : ℕ} (ht : HaltsAt M w t) :
    ∃ (as : List (Native.Descriptor M.k)) (r : Fin s),
      as.length = t/s+1 ∧ trace (Native.machine M hs) w = Native.replay r as := by
  obtain ⟨halt, -⟩ := Native.simulates_halt M hs w ht
  obtain ⟨as,r,hlen,htr⟩ := Native.halting_trace hs w ((haltsAt_iff_trace _).mp halt)
  refine ⟨as,r,?_,htr⟩
  have hmul : (10*s+1)*as.length = (10*s+1)*(t/s+1) := by omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) hmul

/-- A scale-one skeleton retains exactly the work dependency paths of the actual trace. -/
theorem native_skeleton_path_bound {M : TM} {w : List Bool} {T D : ℕ}
    (hhalt : HaltsAt M w T) (Γ : Finset ℕ)
    (hpath : ∀ π, IsDepPath (trace M w).work T π → LinNet.GFree Γ π → π.length ≤ D+1) :
    ∀ π, IsDepPath (runSkeleton M 1 w).s (runSkeleton M 1 w).T π →
      LinNet.GFree Γ π → π.length ≤ D+1 := by
  have hclass := inClass_runSkeleton (w := 1) hhalt
  have hT : (runSkeleton M 1 w).T = T := haltsAt_unique hclass.1 hhalt
  have hagree : ∀ j u, u < (runSkeleton M 1 w).T →
      (runSkeleton M 1 w).s j u = (trace M w).work j u := by
    intro j u hu
    have h := ((hclass.2 u hu).2.1 j).symm
    simpa only [Nat.cast_one,Int.ediv_one,workPos_eq_work] using h
  intro π hp hf
  apply hpath π
  · rw [← hT]
    exact (isDepPath_congr hagree π).mp hp
  · exact hf

/-- Convert any joint-support physical genie directly into a native geometry witness. -/
theorem native_typical_cut_of_trace_genie (M : TM) {d b : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b)
    {c ε : ℝ} (hc : 0 < c) {S : Finset (Fin (d*d*b) → Bool)}
    {x₀ : Fin (d*d*b) → Bool} (hx₀ : x₀ ∈ S)
    (htr : ∀ x ∈ S, trace M (List.ofFn x) = trace M (List.ofFn x₀))
    (hgood : ∀ x ∈ S, TransposesInput M d b c x) (θ r : ℕ)
    {T D : ℕ} (hhalt : HaltsAt M (List.ofFn x₀) T) (Γ : Finset ℕ)
    (hcount : ((S.image fun x => fun t : Γ => blockVal M 1 (List.ofFn x) t).card : ℝ) ≤
      (2:ℝ)^(ε*(d*d*b : ℕ)))
    (hpath : ∀ π, IsDepPath (trace M (List.ofFn x₀)).work T π →
      LinNet.GFree Γ π → π.length ≤ D+1) :
    Nonempty (NativeTypicalCut M d b c ε θ r S D) :=
  exists_native_typical_cut_of_genie M hd hb hc hx₀ htr hgood θ r Γ hcount
    (native_skeleton_path_bound hhalt Γ hpath)

end
end TapeStorageRates

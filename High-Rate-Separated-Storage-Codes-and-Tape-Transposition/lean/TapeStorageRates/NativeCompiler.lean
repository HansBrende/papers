import TapeStorageRates.NativeSimulation
import TapeStorageRates.NativeResources

/-! The aligned compiler in the units of the source machine. -/

namespace TapeStorageRates.Native

open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth

/-- Equality of partial input/output functions, allowing arbitrary halting
times on both sides. This imposes no condition on nonhalting output streams. -/
theorem same_partial_function (M : TM) {s : ℕ} (hs : 0<s) (w out : List Bool) :
    (∃ T, ComputesWithin (machine M hs) w out T) ↔ ∃ T, ComputesWithin M w out T := by
  constructor
  · rintro ⟨T,h⟩
    obtain ⟨u,-,hu,ou⟩ := (computesWithin_iff out T).mp h
    obtain ⟨t,ht⟩ := (halts_iff M hs w).mp ⟨u,hu⟩
    obtain ⟨eqT,eo⟩ := simulates_halt M hs w ht
    have eu := haltsAt_unique hu eqT
    exact ⟨t,(computesWithin_iff out t).mpr ⟨t,le_rfl,ht,by rwa [eu,eo] at ou⟩⟩
  · rintro ⟨T,h⟩
    obtain ⟨t,-,ht,ot⟩ := (computesWithin_iff out T).mp h
    obtain ⟨hu,eo⟩ := simulates_halt M hs w ht
    exact ⟨_,(computesWithin_iff out _).mpr ⟨_,le_rfl,hu,by rwa [eo]⟩⟩

/-- Native trace count with a source-machine time bound and fixed output length. -/
theorem source_support_fixed (M : TM) {s : ℕ} (hs : 0<s) (U outLen : ℕ) :
    ∃ S : Finset (Trace M.k), S.card ≤ (1+2*3^(M.k+1))^(U/s+1) ∧
      ∀ w t, HaltsAt M w t → t ≤ U → (run M w t).outRev.length=outLen →
        trace (machine M hs) w ∈ S := by
  obtain ⟨S,cap,contains⟩ := halting_support_fixed (M := M) hs (U/s+1) outLen
  refine ⟨S,cap,?_⟩
  intro w t htime hU hlen
  obtain ⟨hu,eo⟩ := simulates_halt M hs w htime
  apply contains w _ ((haltsAt_iff_trace _).mp hu)
  · gcongr
  · simpa [eo] using hlen

/-- Allowing different source output lengths multiplies the trace count by s. -/
theorem source_support (M : TM) {s : ℕ} (hs : 0<s) (U : ℕ) :
    ∃ S : Finset (Trace M.k), S.card ≤ s*(1+2*3^(M.k+1))^(U/s+1) ∧
      ∀ w t, HaltsAt M w t → t ≤ U → trace (machine M hs) w ∈ S := by
  obtain ⟨S,cap,contains⟩ := halting_support (M := M) hs (U/s+1)
  refine ⟨S,cap,?_⟩
  intro w t htime hU
  apply contains w _ ((haltsAt_iff_trace _).mp (simulates_halt M hs w htime).1)
  gcongr

end TapeStorageRates.Native

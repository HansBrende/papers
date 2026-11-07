import TapeStorageRates.PaidClassesSchedule
import TapeStorageRates.PacketCompilerTable
import TapeStorageRates.PacketRecordBits

/-! # Encoding actual local step records as a paid packet class -/

namespace TapeStorageRates.PaidClasses

open Finset PaidInputs PacketCompiler
open Transpose Transpose.Tape

set_option autoImplicit false

/-- The finite record encoding preserves local recovery. On the actual append
slot of each demanded packet, equality of records implies equality of the two
source packets. The resulting class has exactly the given population and time. -/
theorem packet_class_of_local {M : TM} {c : ℝ} {d a s r R : ℕ}
    (ha : 0 < a) (hs : 0 < s) (hr : r < s) (z : Raw d r)
    (S : Finset (Payload d a s)) (hne : S.Nonempty)
    (hgood : S ⊆ payloadFibre (successfulInputsAt M c d (a*s+r)) z)
    (hR : ⌊c*(((d*d*(a*s+r) : ℕ) : ℝ)+1)⌋₊ / s + 1 ≤ R) (w₀ : List Bool)
    (hgeo : ∀ x ∈ S, ∀ j ≤ R, centres (raggedLayout d a s r ha) hs M (rawWord z x) j =
      centres (raggedLayout d a s r ha) hs M w₀ j)
    (val : Payload d a s → ℕ → StepRecord M s r)
    (hloc : PacketLocal (batchWalks (raggedLayout d a s r ha) hs M w₀) (11*R) S val)
    (hout : ∀ x ∈ S, ∀ b < R, (val x (11*b+10)).output =
      emitted (raggedLayout d a s r ha) hs M (rawWord z x) b) :
    ∃ W : PacketClass M.k s (recordBits M*s) d a, W.time = 11*R ∧ W.words = S := by
  classical
  let L := raggedLayout d a s r ha
  let enc := encodeRecord M hs hr
  obtain ⟨b,hb⟩ := common_crossing ha hs z S hne hgood hR w₀ hgeo
  let W : PacketClass M.k s (recordBits M*s) d a :=
    { time := 11*R
      words := S
      nonempty := hne
      walks := batchWalks L hs M w₀
      unit_walk := unit_batchWalks L hs M w₀
      record := fun x t => enc (val x t)
      local_record := by
        intro x hx y hy t ht hprev hraw
        exact congrArg enc (hloc x hx y hy t ht (fun u hu => enc.injective (hprev u hu)) hraw)
      outputTime := outputClock b
      outputPosition := by
        intro q
        rw [outputClock_at]
        refine ⟨by have := (hb q).1; omega,?_⟩
        change (MergeDepth.tpos d a q : ℤ) = (centres L hs M w₀ ((11*b q+10)/11)).output
        rw [show (11*b q+10)/11 = b q by omega]
        simpa only [MergeDepth.tposOf_val,MergeDepth.tape_tpos_eq] using (hb q).2.1.symm
      outputDetermined := by
        intro x hx y hy q hrec
        rw [outputClock_at] at hrec
        have he := congrArg StepRecord.output (enc.injective hrec)
        have ho (v) (hv : v∈S) : (val v (11*b q+10)).output = some (v q) := by
          obtain ⟨h0,h1,hbits⟩ := (hb q).2.2 v hv
          rw [hout v hv _ (hb q).1]
          simp [emitted,h0,h1,past,hbits]
        rw [ho x hx,ho y hy] at he
        exact Option.some.inj he }
  exact ⟨W,rfl,rfl⟩

end TapeStorageRates.PaidClasses

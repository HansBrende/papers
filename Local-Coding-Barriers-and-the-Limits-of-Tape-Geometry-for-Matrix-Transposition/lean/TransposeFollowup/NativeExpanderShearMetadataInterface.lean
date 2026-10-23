import TransposeFollowup.NativeExpanderShearMetadata
import TransposeFollowup.ExpanderShearOpcodeBridge

/-! Preserved metadata and the exact generated opcode representation.
These are projections of a previously proved native execution endpoint. -/
namespace TransposeFollowup.NativeExpanderShearMetadataInterface
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

@[simp] theorem dimension_tape (F : Fin (r+1) → RationalMobius) (w xs ys : List Bool) :
    NativeExpanderShearMetadata.finalBank F w xs ys .dimension=Counter.marked xs := rfl

@[simp] theorem payload_tape (F : Fin (r+1) → RationalMobius) (w xs ys : List Bool) :
    NativeExpanderShearMetadata.finalBank F w xs ys (.generator .payload)=Counter.marked w := by
  change OpcodeGenerator.finalBank F w ys .payload=_
  rw [OpcodeGenerator.retained_tapes F w ys .payload (by decide +kernel)]
  exact SchedulerSeed.ready_payload F w ys

@[simp] theorem half_tape (F : Fin (r+1) → RationalMobius) (w xs ys : List Bool) :
    NativeExpanderShearMetadata.finalBank F w xs ys (.generator (.enumeration .source))=
      Counter.marked ys := by
  change OpcodeGenerator.finalBank F w ys (.enumeration .source)=_
  rw [OpcodeGenerator.retained_tapes F w ys (.enumeration .source) (by decide +kernel)]
  rfl

theorem opcode_tape (F : Fin (r+1) → RationalMobius) (w xs ys : List Bool)
    (m : ℕ) (hv : Counter.value ys=m) :
    NativeExpanderShearMetadata.finalBank F w xs ys (.generator VertexScheduler.outputPort)=
      ⟨(symbols (NativeMatchingXorMasks.encode
        (ExpanderShearOpcodeBridge.sourceRows F m++ExpanderShearOpcodeBridge.targetRows F m))).reverse,[]⟩ := by
  change OpcodeGenerator.finalBank F w ys VertexScheduler.outputPort=_
  rw [OpcodeGenerator.output_tape,hv,ExpanderShearOpcodeBridge.encoded_tape]

end TransposeFollowup.NativeExpanderShearMetadataInterface

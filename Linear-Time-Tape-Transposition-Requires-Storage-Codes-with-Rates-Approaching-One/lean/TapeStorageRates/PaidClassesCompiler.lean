import TapeStorageRates.PaidClassesAssembly
import TapeStorageRates.PaidInputsRead
import TapeStorageRates.PacketCompilerLocal

/-! # Every native machine supplies the concrete deadline-bounded packet compiler -/

namespace TapeStorageRates.PaidClasses

open Finset PaidInputs PacketCompiler

set_option autoImplicit false

/-- The genuine eleven-tick packet computation on the native machine has
linear-width records and a uniform batch and runtime coefficient. This also
applies to arbitrary successful sets of payloads with one fixed tail. -/
theorem compiler (M : Transpose.TM) {c : ℝ} (hc : 0 ≤ c) {s : ℕ} (hs : 0<s) :
    Compiles M c s (recordBits M*s) (batchCoefficient c) (11*(batchCoefficient c : ℝ)) := by
  classical
  intro d a r ha hr z F
  let L := raggedLayout d a s r ha
  let R := ⌊c*(((d*d*(a*s+r) : ℕ):ℝ)+1)⌋₊ / s + 1
  let σ (x : Payload d a s) := schedule L hs M R (rawWord z x)
  refine ⟨R,padded_batches_le ha hs hr hc,σ,?_⟩
  intro y hy
  obtain ⟨x₀,hx₀,hσ₀⟩ := mem_image.mp hy
  let S := F.filter fun x => σ x=y
  have hne : S.Nonempty := ⟨x₀,mem_filter.mpr ⟨hx₀,hσ₀⟩⟩
  have hgeo (x) (hx : x∈S) : ∀ j ≤ R, centres L hs M (rawWord z x) j =
      centres L hs M (rawWord z x₀) j := by
    apply centres_of_schedule_eq
    exact (mem_filter.mp hx).2.trans hσ₀.symm
  have hloc := record_local L hs M (rawWord z x₀) (rawWord z) S hgeo
    (fun _ _ _ _ u h => input_cell_eq ha hs z u h)
  obtain ⟨W,ht,hwords⟩ := packet_class_of_local ha hs hr z S hne (filter_subset _ _) le_rfl
    (rawWord z x₀) hgeo (fun x => record L hs M (rawWord z x)) hloc
    (fun x _ b _ => record_emit_slot L hs M (rawWord z x) b)
  exact ⟨W,ht ▸ padded_time_le ha hs hr hc,hwords ▸ Subset.rfl⟩

end TapeStorageRates.PaidClasses

import TapeStorageRates.PacketExpansion

/-! # Coordinate relabeling of an entire index partition -/

namespace TapeStorageRates

open Finset DirectedRecovery
set_option autoImplicit false

variable {U V Y : Type*}

/-- Pull the whole input back to the original coordinate names before encoding. -/
def relabelEncoder (e : U ≃ V) (f : (U → Bool) → Y) (x : V → Bool) : Y := f (x ∘ e)

theorem relabel_isIndexCode (e : U ≃ V) {N : U → Finset U} {f : (U → Bool) → Y}
    (hf : IsIndexCode N f) : IsIndexCode (relabelRelation e N) (relabelEncoder e f) := by
  intro x y hxy q hhelp
  have h := hf (x ∘ e) (y ∘ e) hxy (e.symm q)
    (fun p hp => hhelp (e p) (mem_map.mpr ⟨p, hp, rfl⟩))
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h

open Classical in
/-- All attained labels, and hence their exact count, are unchanged. -/
theorem relabelEncoder_image [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (e : U ≃ V) (f : (U → Bool) → Y) :
    univ.image (relabelEncoder e f) = univ.image f := by
  ext z
  constructor
  · rintro hz
    obtain ⟨x, _, rfl⟩ := mem_image.mp hz
    exact mem_image_of_mem f (mem_univ (x ∘ e))
  · rintro hz
    obtain ⟨x, _, rfl⟩ := mem_image.mp hz
    refine mem_image.mpr ⟨x ∘ e.symm, mem_univ _, ?_⟩
    simp only [relabelEncoder, Function.comp_def, Equiv.symm_apply_apply]

end TapeStorageRates

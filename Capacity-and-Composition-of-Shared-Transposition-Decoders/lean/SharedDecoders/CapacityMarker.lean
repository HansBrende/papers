import SharedDecoders.CapacityTP
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-! # A one-class affine marker source over every field

The marker fixes one row, so the source is affine rather than linear. Its
complete-view decoder identifies the phase; this is not a native addressing
primitive.
-/

namespace SharedDecoders.CapacityMarker

variable (F : Type*) [Field F] (d : ℕ) [NeZero d]

def marker : ZMod d → F := fun j => if j = 0 then 1 else 0

def rowZero : State d F →ₗ[F] (ZMod d → F) where
  toFun X := X 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def direction : Submodule F (State d F) := LinearMap.ker (rowZero F d)

def basepoint : State d F := fun i j => if i = 0 then marker F d j else 0

def source : AffineSubspace F (State d F) := AffineSubspace.mk' (basepoint F d) (direction F d)

omit [NeZero d] in
theorem mem_source (X : State d F) : X ∈ source F d ↔ X 0 = marker F d := by
  change X - basepoint F d ∈ LinearMap.ker (rowZero F d) ↔ _
  change (fun j => X 0 j - basepoint F d 0 j) = 0 ↔ _
  have he : (fun j => X 0 j - basepoint F d 0 j) = X 0 - marker F d := by
    ext j
    simp [basepoint]
  rw [he, sub_eq_zero]

theorem source_finrank : Module.finrank F (source F d).direction = d * d - d := by
  have hsurj : Function.Surjective (rowZero F d) := fun y => ⟨fun _ => y, rfl⟩
  have h := (rowZero F d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h
  have hstate : Module.finrank F (State d F) = d * d := by simp [finrank_state]
  have hword : Module.finrank F (ZMod d → F) = d := by simp
  rw [hstate, hword] at h
  rw [source, AffineSubspace.direction_mk']
  change Module.finrank F (LinearMap.ker (rowZero F d)) = _
  omega

omit [NeZero d] in
theorem marker_phase_injective :
    Function.Injective (fun c : ZMod d => fun j => marker F d (j + c)) := by
  intro c e h
  have he := congrFun h (-c)
  by_contra hce
  have hn : -c + e ≠ 0 := by
    intro hz
    have : e = c := by simpa [← add_assoc] using congrArg (fun x => c + x) hz
    exact hce this.symm
  simp [marker, hn] at he

noncomputable def decoder (Y : State d F) : ZMod d → F := by
  classical
  exact if h : ∃ c : ZMod d, Y 0 = fun j => marker F d (j + c) then
      rot (-Classical.choose h) Y (Classical.choose h)
    else 0

theorem decoder_correct {X : State d F} (hX : X ∈ source F d) (c : ZMod d) :
    decoder F d (rot c X) = X c := by
  classical
  have hx := (mem_source F d X).mp hX
  have hc : rot c X 0 = fun j => marker F d (j + c) := congrArg (fun v => fun j => v (j + c)) hx
  have hex : ∃ e : ZMod d, rot c X 0 = fun j => marker F d (j + e) := ⟨c, hc⟩
  have he : Classical.choose hex = c := marker_phase_injective F d
    ((Classical.choose_spec hex).symm.trans hc)
  simp only [decoder, dite_eq_left hex, he, rot_neg_rot]

theorem exists_affine_source_decoder :
    ∃ (C : AffineSubspace F (State d F)) (f : State d F → (ZMod d → F)),
      Module.finrank F C.direction = d * d - d ∧
      ∀ X ∈ C, ∀ c, f (rot c X) = X c :=
  ⟨source F d, decoder F d, source_finrank F d, fun _ hX c => decoder_correct F d hX c⟩

end SharedDecoders.CapacityMarker

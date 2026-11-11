import SharedDecoders.CompositionExtraction

/-! # A rotation-invariant ambient derived from actual column vectors -/

namespace SharedDecoders

open Module

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A]
  {d : ℕ} [NeZero d]

abbrev ColumnAmbient (H : Submodule F (ZMod d → A)) := Unit → ZMod d → H

def columnAmbientEmbed (H : Submodule F (ZMod d → A)) :
    ColumnAmbient H →ₗ[F] State d A where
  toFun x i c := (x () c).val i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NeZero d] in
theorem columnAmbientEmbed_injective (H : Submodule F (ZMod d → A)) :
    Function.Injective (columnAmbientEmbed H) := by
  intro x y h
  funext u c
  apply Subtype.ext
  funext i
  simpa [columnAmbientEmbed] using congrFun (congrFun h i) c

omit [NeZero d] in
lemma columnAmbientEmbed_rotation (H : Submodule F (ZMod d → A)) (s : ZMod d)
    (x : ColumnAmbient H) :
    columnAmbientEmbed H (channelRotation (F := F) s x) =
      rot s (columnAmbientEmbed H x) := rfl

omit [NeZero d] in
lemma columnAmbientEmbed_rotation_pow (H : Submodule F (ZMod d → A)) (s : ZMod d)
    (j : ℕ) (x : ColumnAmbient H) :
    columnAmbientEmbed H ((channelRotation (F := F) s ^ j) x) =
      rot ((j : ZMod d) * s) (columnAmbientEmbed H x) := by
  rw [channelRotation_pow, columnAmbientEmbed_rotation]

theorem columnAmbient_finrank [FiniteDimensional F A]
    (H : Submodule F (ZMod d → A)) : finrank F (ColumnAmbient H) = d * finrank F H := by
  simp [ColumnAmbient, Module.finrank_pi_fintype, ZMod.card]

variable {b k : ℕ} {κ : Type*}

/-- The pulled-back band lands in the forced row ambient for every coefficient
vector, before imposing any correctness condition. -/
def bandPull (χ : AddChar (ZMod d) F) (p : ZMod d → κ)
    (K : State d (Fin b → F) →ₗ[F] State d (Fin b → F))
    (hK : LinearClassUniform p K) :
    (Fin k → ZMod d → Fin b → F) →ₗ[F] ColumnAmbient (bandRowSpace (b := b) χ p k) where
  toFun a _ j := ⟨fun i => swap (K (bandMap χ k a)) i j,
    swap_second_band_column_mem χ p K hK a j⟩
  map_add' a a' := by
    funext u j
    apply Subtype.ext
    funext i
    simp [map_add]
  map_smul' t a := by
    funext u j
    apply Subtype.ext
    funext i
    simp [map_smul]

omit [NeZero d] in
@[simp] lemma columnAmbientEmbed_bandPull (χ : AddChar (ZMod d) F) (p : ZMod d → κ)
    (K : State d (Fin b → F) →ₗ[F] State d (Fin b → F))
    (hK : LinearClassUniform p K) (a : Fin k → ZMod d → Fin b → F) :
    columnAmbientEmbed (bandRowSpace χ p k) (bandPull χ p K hK a) =
      swap (K (bandMap χ k a)) := rfl

end SharedDecoders

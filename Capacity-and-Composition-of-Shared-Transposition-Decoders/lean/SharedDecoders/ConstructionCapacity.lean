import SharedDecoders.ConstructionPeriodic
import SharedDecoders.ConstructionBaseChange
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Periodic capacity with the actual splitting-field hypotheses -/

namespace SharedDecoders

open Module

variable {F κ : Type*} [Field F] {m s : ℕ} [NeZero m] [NeZero s]

theorem exists_injective_character [HasEnoughRootsOfUnity F m] :
    ∃ χ : AddChar (ZMod m) F, Function.Injective χ := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F m
  refine ⟨AddChar.zmodChar m hζ.pow_eq_one, ?_⟩
  intro x y hxy
  apply ZMod.val_injective
  exact hζ.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) hxy

theorem periodic_linear_capacity_split [HasEnoughRootsOfUnity F m]
    (p : ZMod s → κ) (hc : m.Coprime s) (hm : (m : F) ≠ 0) :
    2 * dimensionCapacity (IsLinearSharedCode (F := F) (A := F) (liftedPartition hc p)) +
      m * (s * s) = (m * s) * (m * s) +
        2 * m * dimensionCapacity (IsLinearSharedCode (F := F) (A := F) p) := by
  obtain ⟨χ, hχ⟩ := exists_injective_character (F := F) (m := m)
  exact periodic_linear_capacity p hc hm χ hχ

theorem periodic_linear_capacity_lower
    (p : ZMod s → κ) (hc : m.Coprime s) (hm : (m : F) ≠ 0) :
    (m * s) * (m * s) + 2 * m * dimensionCapacity (IsLinearSharedCode (F := F) (A := F) p) ≤
      2 * dimensionCapacity (IsLinearSharedCode (F := F) (A := F) (liftedPartition hc p)) +
        m * (s * s) := by
  obtain ⟨D, hD, hdimD⟩ := dimensionCapacity_attained
    (IsLinearSharedCode (F := F) (A := F) p) (isLinearSharedCode_bot p)
  have hl := le_dimensionCapacity (hD.cyclicLiftCode hc hm)
  have heq := two_mul_finrank_cyclicLiftCode hc hm D
  rw [Module.finrank_self, mul_one, mul_one, hdimD] at heq
  omega

theorem periodic_linear_capacity_algebraicClosure_upper
    (p : ZMod s → κ) (hc : m.Coprime s) (hm : (m : F) ≠ 0) :
    2 * dimensionCapacity (IsLinearSharedCode (F := F) (A := F) (liftedPartition hc p)) +
      m * (s * s) ≤ (m * s) * (m * s) + 2 * m *
        dimensionCapacity (IsLinearSharedCode (F := AlgebraicClosure F) (A := AlgebraicClosure F) p) := by
  let : NeZero (m : F) := ⟨hm⟩
  have hmE : (m : AlgebraicClosure F) ≠ 0 := by
    intro hz
    apply hm
    apply (algebraMap F (AlgebraicClosure F)).injective
    simpa only [map_natCast, map_zero] using hz
  have hl := linear_capacity_le_scalarExtension (F := F) (E := AlgebraicClosure F)
    (liftedPartition hc p)
  have heq := periodic_linear_capacity_split (F := AlgebraicClosure F) p hc hmE
  omega

end SharedDecoders

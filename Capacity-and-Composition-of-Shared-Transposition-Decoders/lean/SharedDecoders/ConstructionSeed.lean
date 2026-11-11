import SharedDecoders.ConstructionLinearLift
import SwapRigidity.AperiodicExample

/-! # The published six-dimensional seed lifted with exactly two classes

The seed certificate and its dimension are reused from the earlier library.
No seed optimality claim is needed or imported.
-/

namespace SharedDecoders

open Module

/-- The published matrix source, with the shared model's function-space instances. -/
def binarySeedCode : Submodule (ZMod 2) (State 6 (ZMod 2)) where
  carrier := {X | X ∈ SwapRigidity.aperiodicCode}
  zero_mem' := SwapRigidity.aperiodicCode.zero_mem
  add_mem' := fun hX hY => SwapRigidity.aperiodicCode.add_mem hX hY
  smul_mem' := fun a _ hX => SwapRigidity.aperiodicCode.smul_mem a hX

def binarySeedEquiv : binarySeedCode ≃ₗ[ZMod 2] SwapRigidity.aperiodicCode where
  toFun X := ⟨X.1, X.2⟩
  invFun X := ⟨X.1, X.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

theorem finrank_binarySeedCode : finrank (ZMod 2) binarySeedCode = 25 :=
  binarySeedEquiv.finrank_eq.trans SwapRigidity.finrank_aperiodicCode

theorem isLinearSharedCode_binarySeedCode :
    IsLinearSharedCode SwapRigidity.aperiodicCls binarySeedCode := by
  refine ⟨SwapRigidity.aperiodicDec, ?_⟩
  intro X hX c
  exact SwapRigidity.row_eq_aperiodicDec_of_mem hX c

theorem binary_cast_ne_zero_of_coprime_six {m : ℕ} (hc : m.Coprime 6) :
    (m : ZMod 2) ≠ 0 := by
  intro hz
  have hdvd := (ZMod.natCast_eq_zero_iff m 2).mp hz
  have heq : 2 = 1 := Nat.eq_one_of_dvd_coprimes hc hdvd (by decide)
  omega

variable {m : ℕ} [NeZero m]

def binaryCyclicCode (hc : m.Coprime 6) : Submodule (ZMod 2) (State (m * 6) (ZMod 2)) :=
  cyclicLiftCode hc binarySeedCode

theorem binaryCyclicCode_linear (hc : m.Coprime 6) :
    IsLinearSharedCode (liftedPartition hc SwapRigidity.aperiodicCls) (binaryCyclicCode hc) :=
  isLinearSharedCode_binarySeedCode.cyclicLiftCode hc (binary_cast_ne_zero_of_coprime_six hc)

omit [NeZero m] in
theorem binaryCyclicPartition_surjective (hc : m.Coprime 6) :
    Function.Surjective (liftedPartition hc SwapRigidity.aperiodicCls) := by
  apply liftedPartition_surjective hc
  intro j
  cases j with
  | false => exact ⟨2, by decide⟩
  | true => exact ⟨0, by decide⟩

theorem finrank_binaryCyclicCode (hc : m.Coprime 6) :
    finrank (ZMod 2) (binaryCyclicCode hc) = 18 * m * m + 7 * m := by
  have hh := two_mul_finrank_cyclicLiftCode hc
    (binary_cast_ne_zero_of_coprime_six hc) binarySeedCode
  rw [Module.finrank_self, finrank_binarySeedCode] at hh
  change 2 * finrank (ZMod 2) (binaryCyclicCode hc) + m * (6 * 6 * 1) =
    (m * 6) * (m * 6) * 1 + 2 * m * 25 at hh
  nlinarith

theorem binaryCyclicCode_interval_excess (hc : m.Coprime 6) :
    2 * finrank (ZMod 2) (binaryCyclicCode hc) =
      (m * 6) * (m * 6) + 2 * (m * 6) + 2 * m := by
  rw [finrank_binaryCyclicCode]
  ring

end SharedDecoders

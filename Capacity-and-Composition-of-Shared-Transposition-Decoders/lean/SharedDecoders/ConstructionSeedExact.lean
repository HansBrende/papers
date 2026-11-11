import SharedDecoders.ConstructionSeed
import SharedDecoders.ConstructionSeedExactData
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.Tactic.FinCases

/-! # The published binary seed's whole agreement kernel

The generators already give dimension at least 25. The sparse recovery
certificate proves that every solution of the actual decoder equations
lies in their span. Kernel evaluation checks coefficients on 36 basis
matrices; no enumeration of the 2^36 inputs or trusted rank computation is used.
-/

namespace SharedDecoders

open Module
open scoped BigOperators

def binarySeedDefect : State 6 (ZMod 2) →ₗ[ZMod 2] State 6 (ZMod 2) :=
  LinearMap.id - LinearMap.pi (fun c =>
    (SwapRigidity.aperiodicDec (SwapRigidity.aperiodicCls c)).comp (rotLinear (ZMod 2) c))

def binarySeedCoordinate (p : ZMod 6 × ZMod 6) : State 6 (ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun X := X p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def binarySeedExpansion : State 6 (ZMod 2) →ₗ[ZMod 2] State 6 (ZMod 2) :=
  ∑ k : Fin 25, (binarySeedCoordinate (SwapRigidity.aperiodicPivot k)).smulRight
    (SwapRigidity.aperiodicGen k : State 6 (ZMod 2))

def binarySeedRecovery : State 6 (ZMod 2) →ₗ[ZMod 2] State 6 (ZMod 2) where
  toFun Y c r := ((binarySeedRecoverySupports.getD (6 * c.val + r.val) []).map
    fun p => Y p.1 p.2).sum
  map_add' Y Z := by
    funext c r
    simp only [Pi.add_apply, List.sum_map_add]
  map_smul' a Y := by
    funext c r
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, List.sum_map_mul_left]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem binarySeed_recovery_identity :
    binarySeedExpansion + binarySeedRecovery.comp binarySeedDefect =
      LinearMap.id (R := ZMod 2) (M := State 6 (ZMod 2)) := by
  apply (Matrix.stdBasis (ZMod 2) (ZMod 6) (ZMod 6)).ext
  intro ij
  rcases ij with ⟨i,j⟩
  rw [Matrix.stdBasis_eq_single]
  change (binarySeedExpansion + binarySeedRecovery.comp binarySeedDefect)
    (Matrix.single i j 1) = (Matrix.single i j 1 : State 6 (ZMod 2))
  funext r c
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases c <;> decide

theorem binarySeedExpansion_mem (X : State 6 (ZMod 2)) :
    binarySeedExpansion X ∈ binarySeedCode := by
  simp only [binarySeedExpansion, LinearMap.sum_apply, binarySeedCoordinate]
  apply Submodule.sum_mem
  intro k _
  exact binarySeedCode.smul_mem _ (SwapRigidity.aperiodicGen_mem_aperiodicCode k)

/-- Equality with the full kernel of the displayed rule, not an optimality claim. -/
theorem binarySeedDefect_ker : binarySeedDefect.ker = binarySeedCode := by
  apply le_antisymm
  · intro X hX
    have hzero := LinearMap.mem_ker.mp hX
    have heq := congrArg (fun f : State 6 (ZMod 2) →ₗ[ZMod 2] State 6 (ZMod 2) => f X)
      binarySeed_recovery_identity
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hzero, map_zero, add_zero,
      LinearMap.id_apply] at heq
    rw [← heq]
    exact binarySeedExpansion_mem X
  · intro X hX
    apply LinearMap.mem_ker.mpr
    funext c r
    change X c r - SwapRigidity.aperiodicDec
      (SwapRigidity.aperiodicCls c) (rot c X) r = 0
    have h := SwapRigidity.row_eq_aperiodicDec_of_mem hX c
    exact sub_eq_zero.mpr (congrFun h r)

theorem finrank_binarySeedDefect_ker :
    finrank (ZMod 2) binarySeedDefect.ker = 25 := by
  rw [binarySeedDefect_ker, finrank_binarySeedCode]

end SharedDecoders

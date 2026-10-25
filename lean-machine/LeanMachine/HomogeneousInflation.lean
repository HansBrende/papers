import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi

/-!
# Exact inflation of sheet-dependent linear checks

The coefficient space `W` can be a finite product of vertex spaces; each
coefficient map can be extended by zero from its source to its target type.
No commutativity assumption on the sheet group is made. Repeated voltages
and zero coefficients are allowed.
-/

namespace LeanMachine.HomogeneousInflation

open Module
open scoped BigOperators

variable {K Q E W : Type*} [DivisionRing K] [Group Q] [Fintype E]
    [AddCommGroup W] [Module K W]

/-- The original check, with coefficients indexed by the destination sheet. -/
def sheetCheck (g : E → Q) (C : E → Q → W →ₗ[K] W) :
    (Q → W) →ₗ[K] (Q → W) where
  toFun x t := x t - ∑ e, C e t (x ((g e)⁻¹ * t))
  map_add' x y := by ext t; simp [Finset.sum_add_distrib, sub_add_sub_comm]
  map_smul' a x := by ext t; simp [smul_sub, Finset.smul_sum]

/-- Both sheet indices move together; coefficients depend only on the internal
index, so the check is homogeneous in the external index. -/
def inflatedCheck (g : E → Q) (C : E → Q → W →ₗ[K] W) :
    (Q → Q → W) →ₗ[K] (Q → Q → W) where
  toFun x q t := x q t - ∑ e, C e t (x ((g e)⁻¹ * q) ((g e)⁻¹ * t))
  map_add' x y := by ext q t; simp [Finset.sum_add_distrib, sub_add_sub_comm]
  map_smul' a x := by ext q t; simp [smul_sub, Finset.smul_sum]

/-- Reindex by the invariant `h = q⁻¹ * t`. This is a permutation of coordinates,
not a transformation of their values. -/
def sheetReindex : (Q → Q → W) ≃ₗ[K] (Q → Q → W) where
  toFun x h t := x (t * h⁻¹) t
  invFun y q t := y (q⁻¹ * t) t
  left_inv x := by ext q t; simp [mul_inv_rev]
  right_inv y := by ext h t; simp [mul_inv_rev]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- In the new coordinates each invariant sheet carries the original check. -/
theorem reindex_inflated (g : E → Q) (C : E → Q → W →ₗ[K] W)
    (x : Q → Q → W) :
    sheetReindex (K := K) (inflatedCheck g C x) =
      fun h => sheetCheck g C (sheetReindex (K := K) x h) := by
  ext h t
  simp [sheetReindex, inflatedCheck, sheetCheck, mul_assoc]

/-- The inflated kernel consists of independent copies of the original kernel. -/
def kernelEquiv (g : E → Q) (C : E → Q → W →ₗ[K] W) :
    LinearMap.ker (inflatedCheck g C) ≃ₗ[K] (Q → LinearMap.ker (sheetCheck g C)) where
  toFun x h := ⟨sheetReindex (K := K) x.val h, by
    have hx := congrFun (reindex_inflated g C x.val) h
    rw [LinearMap.mem_ker.mp x.property, map_zero] at hx
    exact hx.symm⟩
  invFun y := ⟨(sheetReindex (K := K)).symm (fun h => (y h).val), by
    apply (sheetReindex (K := K)).injective
    rw [reindex_inflated, map_zero]
    ext h t
    simpa only [LinearEquiv.apply_symm_apply, Pi.zero_apply] using
      congrFun (LinearMap.mem_ker.mp (y h).property) t⟩
  left_inv x := by
    apply Subtype.ext
    exact (sheetReindex (K := K)).symm_apply_apply x.val
  right_inv y := by
    funext h
    apply Subtype.ext
    exact congrFun ((sheetReindex (K := K)).apply_symm_apply (fun h => (y h).val)) h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Exact kernel dimension multiplication under inflation. -/
theorem finrank_kernel_inflated [Fintype Q] [FiniteDimensional K W]
    (g : E → Q) (C : E → Q → W →ₗ[K] W) :
    finrank K (LinearMap.ker (inflatedCheck g C)) =
      Fintype.card Q * finrank K (LinearMap.ker (sheetCheck g C)) := by
  rw [(kernelEquiv g C).finrank_eq, Module.finrank_pi_fintype]
  simp

/-- A denominator-free form of rate preservation, also valid for zero widths. -/
theorem rate_cross_product [Fintype Q] [FiniteDimensional K W]
    (g : E → Q) (C : E → Q → W →ₗ[K] W) :
    finrank K (LinearMap.ker (inflatedCheck g C)) * finrank K (Q → W) =
      finrank K (LinearMap.ker (sheetCheck g C)) * finrank K (Q → Q → W) := by
  rw [finrank_kernel_inflated]
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ac_rfl

end LeanMachine.HomogeneousInflation

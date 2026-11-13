import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Linarith

/-! Trace bounds for an operator fixing a subspace. -/

namespace LeanMachine.RecoveryTrace

open Module
open scoped InnerProductSpace Matrix ComplexOrder

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- A pointwise norm bound controls the trace. -/
theorem norm_trace_le (f : E →ₗ[𝕜] E) (γ : ℝ)
    (hf : ∀ x, ‖f x‖ ≤ γ * ‖x‖) :
    ‖LinearMap.trace 𝕜 E f‖ ≤ (finrank 𝕜 E : ℝ) * γ := by
  classical
  let b := stdOrthonormalBasis 𝕜 E
  rw [LinearMap.trace_eq_sum_inner f b]
  calc
    ‖∑ i, ⟪b i, f (b i)⟫_𝕜‖ ≤ ∑ i, ‖⟪b i, f (b i)⟫_𝕜‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin (finrank 𝕜 E), γ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ‖⟪b i, f (b i)⟫_𝕜‖ ≤ ‖b i‖ * ‖f (b i)‖ := norm_inner_le_norm _ _
        _ ≤ γ := by simpa only [b.orthonormal.norm_eq_one, one_mul, mul_one] using hf (b i)
    _ = _ := by simp

/-- Only the action on the orthogonal complement of the fixed subspace needs
to satisfy a norm bound. -/
theorem norm_trace_sub_finrank_le (f : E →ₗ[𝕜] E) (C : Submodule 𝕜 E)
    (hfix : ∀ x ∈ C, f x = x) (γ : ℝ)
    (hf : ∀ x : Cᗮ, ‖f x‖ ≤ γ * ‖x‖) :
    ‖LinearMap.trace 𝕜 E f - (finrank 𝕜 C : 𝕜)‖ ≤ (finrank 𝕜 Cᗮ : ℝ) * γ := by
  let p := C.orthogonalProjectionOnto.toLinearMap
  let q := Cᗮ.orthogonalProjectionOnto.toLinearMap
  have hs : f = (f.comp C.subtype).comp p + (f.comp Cᗮ.subtype).comp q := by
    ext x
    change f x = f (C.starProjection x) + f (Cᗮ.starProjection x)
    rw [← map_add, C.starProjection_add_starProjection_orthogonal]
  have hc : p.comp (f.comp C.subtype) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change C.orthogonalProjectionOnto (f x) = x
    rw [hfix x x.property]
    exact C.orthogonalProjectionOnto_mem_subspace_eq_self x
  have ht : LinearMap.trace 𝕜 E f = (finrank 𝕜 C : 𝕜) +
      LinearMap.trace 𝕜 Cᗮ (q.comp (f.comp Cᗮ.subtype)) := by
    conv_lhs => rw [hs]
    rw [map_add, LinearMap.trace_comp_comm' p (f.comp C.subtype),
      LinearMap.trace_comp_comm' q (f.comp Cᗮ.subtype), hc,
      LinearMap.trace_id]
  rw [ht, add_sub_cancel_left]
  apply norm_trace_le
  intro x
  exact (Cᗮ.norm_orthogonalProjectionOnto_apply_le (f x)).trans (hf x)

/-- Weighted recovery bound, valid over both the real and complex numbers. -/
theorem weighted_finrank_le (f : E →ₗ[𝕜] E) (C : Submodule 𝕜 E)
    (hfix : ∀ x ∈ C, f x = x) (γ : ℝ)
    (hf : ∀ x : Cᗮ, ‖f x‖ ≤ γ * ‖x‖) :
    (1 + γ) * (finrank 𝕜 C : ℝ) ≤
      γ * (finrank 𝕜 E : ℝ) + RCLike.re (LinearMap.trace 𝕜 E f) := by
  have h := norm_trace_sub_finrank_le f C hfix γ hf
  have hr := (abs_le.mp (RCLike.abs_re_le_norm
    (LinearMap.trace 𝕜 E f - (finrank 𝕜 C : 𝕜)))).1
  simp only [map_sub, RCLike.natCast_re] at hr
  have hd : (finrank 𝕜 C : ℝ) + (finrank 𝕜 Cᗮ : ℝ) = finrank 𝕜 E := by
    exact_mod_cast C.finrank_add_finrank_orthogonal
  rw [← hd]
  nlinarith only [h, hr]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Changing from coordinate functions to Euclidean space preserves nullity. -/
theorem finrank_ker_toEuclideanLin (A : Matrix n n 𝕜) :
    finrank 𝕜 (LinearMap.ker A.toEuclideanLin) =
      finrank 𝕜 (LinearMap.ker A.mulVecLin) := by
  have h₁ := A.mulVecLin.finrank_range_add_finrank_ker
  have h₂ := A.toEuclideanLin.finrank_range_add_finrank_ker
  have hr := A.rank_eq_finrank_range_toLin
    (EuclideanSpace.basisFun n 𝕜).toBasis (EuclideanSpace.basisFun n 𝕜).toBasis
  change finrank 𝕜 (LinearMap.range A.mulVecLin) =
    finrank 𝕜 (LinearMap.range A.toEuclideanLin) at hr
  simp only [Module.finrank_pi, finrank_euclideanSpace] at h₁ h₂
  omega

/-- Matrix form of the weighted recovery bound. -/
theorem weighted_finrank_fixed_le (M : Matrix n n 𝕜) (γ : ℝ)
    (hM : ∀ x, ‖M.toEuclideanLin x‖ ≤ γ * ‖x‖) :
    (1 + γ) * (finrank 𝕜 (LinearMap.ker (1 - M).mulVecLin) : ℝ) ≤
      γ * Fintype.card n + RCLike.re M.trace := by
  let C := LinearMap.ker (1 - M).toEuclideanLin
  have h := weighted_finrank_le M.toEuclideanLin C (fun x hx => by
    have hx' := LinearMap.mem_ker.mp hx
    change (Matrix.toEuclideanLin (1 - M)) x = 0 at hx'
    have hx'' : x - M.toEuclideanLin x = 0 := by
      simpa only [map_sub, LinearMap.sub_apply, Matrix.toLpLin_one,
        LinearMap.id_apply] using hx'
    exact (sub_eq_zero.mp hx'').symm) γ
    (fun x => hM x)
  change (1 + γ) * (finrank 𝕜 (LinearMap.ker (1 - M).toEuclideanLin) : ℝ) ≤ _ at h
  rw [finrank_ker_toEuclideanLin] at h
  simpa only [finrank_euclideanSpace,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq] using h

/-- The positive-semidefinite formulation of a Euclidean contraction implies
the pointwise norm bound, without choosing a matrix norm instance. -/
theorem norm_toEuclideanLin_le (M : Matrix n n 𝕜)
    (hM : (1 - Mᴴ * M).PosSemidef) (x : EuclideanSpace 𝕜 n) :
    ‖M.toEuclideanLin x‖ ≤ ‖x‖ := by
  have h := hM.re_dotProduct_nonneg (WithLp.ofLp x)
  have he : (1 - Mᴴ * M).toEuclideanLin =
      LinearMap.id - M.toEuclideanLin.adjoint.comp M.toEuclideanLin := by
    simp only [map_sub, Matrix.toLpLin_one, Matrix.toLpLin_mul_same,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have hi : 0 ≤ RCLike.re ⟪x, (1 - Mᴴ * M).toEuclideanLin x⟫_𝕜 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, dotProduct_comm] using h
  rw [he, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    inner_sub_right, LinearMap.adjoint_inner_right, map_sub,
    ← norm_sq_eq_re_inner, ← norm_sq_eq_re_inner] at hi
  nlinarith [norm_nonneg x, norm_nonneg (M.toEuclideanLin x)]

/-- Backlog B1, also valid over the real numbers and for an empty index type. -/
theorem two_mul_finrank_fixed_le_of_contraction (M : Matrix n n 𝕜)
    (hM : (1 - Mᴴ * M).PosSemidef) :
    2 * (finrank 𝕜 (LinearMap.ker (1 - M).mulVecLin) : ℝ) ≤
      Fintype.card n + RCLike.re M.trace := by
  simpa only [one_add_one_eq_two, one_mul] using
    weighted_finrank_fixed_le M 1 (fun x => by
      simpa only [one_mul] using norm_toEuclideanLin_le M hM x)

end LeanMachine.RecoveryTrace

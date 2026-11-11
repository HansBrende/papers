import SharedDecoders.CompositionBand
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Annihilating a finite sum of exponential observations -/

namespace SharedDecoders

open Module Polynomial
open scoped BigOperators

variable {F V Z : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup Z] [Module F Z] {k : ℕ}

noncomputable def rootCoefficients (lam : Fin k → F) : Fin (k + 1) → F :=
  fun i => (∏ ν, (Polynomial.X - Polynomial.C (lam ν))).coeff i.val

lemma rootPolynomial_natDegree (lam : Fin k → F) :
    (∏ ν, (Polynomial.X - Polynomial.C (lam ν))).natDegree = k := by
  rw [Polynomial.natDegree_prod_of_monic]
  · simp
  · intro i _
    exact Polynomial.monic_X_sub_C _

lemma rootCoefficients_monic (lam : Fin k → F) : rootCoefficients lam (Fin.last k) = 1 := by
  have h := (Polynomial.monic_prod_X_sub_C lam Finset.univ).coeff_natDegree
  simpa [rootCoefficients, rootPolynomial_natDegree] using h

lemma rootCoefficients_eval (lam : Fin k → F) (ν : Fin k) :
    (∑ i : Fin (k + 1), rootCoefficients lam i * lam ν ^ i.val) = 0 := by
  have h : (∏ μ, (Polynomial.X - Polynomial.C (lam μ))).eval (lam ν) = 0 := by
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ ν) (sub_self _)
  rw [Polynomial.eval_eq_sum_range, rootPolynomial_natDegree] at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  exact h

/-- The recurrence follows from the actual available exponential observations;
no independently chosen recurrence is supplied. -/
lemma exponential_observations_recurrence
    (R : V →ₗ[F] V) (L : V →ₗ[F] Z) (lam : Fin k → F)
    (x : V) (v : Fin k → Z) {ell j : ℕ} (hj : j + k < ell)
    (hobs : ∀ t < ell, L ((R ^ t) x) = ∑ ν, lam ν ^ t • v ν) :
    L ((R ^ j) (boundedPolynomial R (rootCoefficients lam) x)) = 0 := by
  simp only [boundedPolynomial, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul]
  have hterm (i : Fin (k + 1)) : L ((R ^ j) ((R ^ i.val) x)) =
      ∑ ν, lam ν ^ (j + i.val) • v ν := by
    rw [← Module.End.mul_apply, ← pow_add]
    exact hobs _ (by omega)
  simp_rw [hterm, Finset.smul_sum]
  rw [Finset.sum_comm]
  have hz (ν : Fin k) : (∑ i : Fin (k + 1),
      rootCoefficients lam i • (lam ν ^ (j + i.val) • v ν)) = 0 := by
    simp_rw [smul_smul, pow_add]
    have hcoeff : (∑ i : Fin (k + 1),
        rootCoefficients lam i * (lam ν ^ j * lam ν ^ i.val)) = 0 := by
      calc
        _ = lam ν ^ j * (∑ i : Fin (k + 1), rootCoefficients lam i * lam ν ^ i.val) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = 0 := by rw [rootCoefficients_eval, mul_zero]
    rw [← Finset.sum_smul, hcoeff, zero_smul]
  simp_rw [hz]
  simp

end SharedDecoders

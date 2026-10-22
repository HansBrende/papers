import TransposeFollowup.SL2TriangularBicommutator
import Mathlib.LinearAlgebra.Matrix.Trace

/-! A nontrivial bicommutator has a nonzero trace test against the identity
or one of its three input matrices. This also covers nonidentity matrices
of trace2; no spectral gap or diagonalizability is assumed. -/
namespace TransposeFollowup.SL2Escape
open Classical Matrix
open scoped commutatorElement
set_option autoImplicit false

variable {K : Type*} [Field K]
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) K
local notation "M" => Matrix (Fin 2) (Fin 2) K

theorem unipotent_trace_tests_bicommutator_eq_one (B a x y : G)
    (hB : B ≠ 1) (htr : Matrix.trace (B : M) = 2)
    (ha : Matrix.trace ((B * a : G) : M) = Matrix.trace (a : M))
    (hx : Matrix.trace ((B * x : G) : M) = Matrix.trace (x : M))
    (hy : Matrix.trace ((B * y : G) : M) = Matrix.trace (y : M)) :
    ⁅⁅a, x⁆, ⁅a, y⁆⁆ = 1 := by
  have hsum : B 0 0 + B 1 1 = 2 := by
    simpa only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using htr
  have hdet : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using B.property
  have hcore : (B 0 0 - 1) ^ 2 + B 0 1 * B 1 0 = 0 := by
    linear_combination B 0 0 * hsum - hdet
  have htest (g : G) (hg : Matrix.trace ((B * g : G) : M) = Matrix.trace (g : M)) :
      (B 0 0 - 1) * g 0 0 + B 0 1 * g 1 0 + B 1 0 * g 0 1 +
        (B 1 1 - 1) * g 1 1 = 0 := by
    have hh : B 0 0 * g 0 0 + B 0 1 * g 1 0 +
        (B 1 0 * g 0 1 + B 1 1 * g 1 1) = g 0 0 + g 1 1 := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace, Matrix.diag,
        Fin.sum_univ_two, Matrix.mul_apply] using hg
    linear_combination hh
  by_cases hq : B 0 1 = 0
  · have h00 : B 0 0 = 1 := by
      have hh : (B 0 0 - 1) ^ 2 = 0 := by simpa only [hq, zero_mul, add_zero] using hcore
      exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hh)
    have h11 : B 1 1 = 1 := by linear_combination hsum - h00
    have hr : B 1 0 ≠ 0 := by
      intro hr
      apply hB
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [h00, h11, hq, hr]
    have hz (g : G) (hg : Matrix.trace ((B * g : G) : M) = Matrix.trace (g : M)) : g 0 1 = 0 := by
      have hh := htest g hg
      simp only [h00, h11, hq, sub_self, zero_mul, zero_add, add_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_left hr
    exact lower_bicommutator_eq_one (hz a ha) (hz x hx) (hz y hy)
  · let c : G := ⟨!![1, 0; (B 0 0 - 1) / B 0 1, 1], by simp [Matrix.det_fin_two]⟩
    let e := MulAut.conj c
    have hz (g : G) (hg : Matrix.trace ((B * g : G) : M) = Matrix.trace (g : M)) : e g 1 0 = 0 := by
      change ((c * g * c⁻¹ : G) : M) 1 0 = 0
      rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
      change ( (!![1, 0; (B 0 0 - 1) / B 0 1, 1] : M) * (g : M) *
        !![1, 0; -((B 0 0 - 1) / B 0 1), 1] : M) 1 0 = 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, one_mul, mul_one]
      field_simp [hq]
      linear_combination B 0 1 * (htest g hg) - B 0 1 * g 1 1 * hsum - g 0 1 * hcore
    have hh := upper_bicommutator_eq_one (hz a ha) (hz x hx) (hz y hy)
    apply e.injective
    simpa only [map_commutatorElement, map_one] using hh

theorem bicommutator_trace_certificate (a x y : G) (hne : ⁅⁅a, x⁆, ⁅a, y⁆⁆ ≠ 1) :
    let B := ⁅⁅a, x⁆, ⁅a, y⁆⁆
    ∃ g : G, (g = 1 ∨ g = a ∨ g = x ∨ g = y) ∧
      Matrix.trace ((B * g : G) : M) ≠ Matrix.trace (g : M) := by
  dsimp only
  by_contra hn
  push Not at hn
  have h1 := hn 1 (Or.inl rfl)
  have ha := hn a (Or.inr (Or.inl rfl))
  have hx := hn x (Or.inr (Or.inr (Or.inl rfl)))
  have hy := hn y (Or.inr (Or.inr (Or.inr rfl)))
  have htr : Matrix.trace ((⁅⁅a, x⁆, ⁅a, y⁆⁆ : G) : M) = 2 := by
    simpa using h1
  exact hne (unipotent_trace_tests_bicommutator_eq_one _ a x y hne htr ha hx hy)

end TransposeFollowup.SL2Escape

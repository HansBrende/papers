import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic

/-! Upper or lower triangular determinant-one matrices have trivial
bicommutators, with the unitriangular commutator calculation explicit. -/
namespace TransposeFollowup.SL2Escape
open Classical Matrix
open scoped commutatorElement
set_option autoImplicit false

variable {K : Type*} [Field K]
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) K

theorem upper_commutator_entries {a x : G} (ha : a 1 0 = 0) (hx : x 1 0 = 0) :
    ⁅a, x⁆ 0 0 = 1 ∧ ⁅a, x⁆ 1 0 = 0 ∧ ⁅a, x⁆ 1 1 = 1 := by
  have hda : a 0 0 * a 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, ha, mul_zero, sub_zero] using a.property
  have hdx : x 0 0 * x 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hx, mul_zero, sub_zero] using x.property
  have he : ((⁅a, x⁆ : G) : Matrix (Fin 2) (Fin 2) K) =
      (a : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K) *
        !![a 1 1, -a 0 1; -a 1 0, a 0 0] * !![x 1 1, -x 0 1; -x 1 0, x 0 0] := by
    rw [commutatorElement_def, Matrix.SpecialLinearGroup.SL2_inv_expl,
      Matrix.SpecialLinearGroup.SL2_inv_expl]
    rfl
  change ((⁅a, x⁆ : G) : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 ∧
    ((⁅a, x⁆ : G) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
    ((⁅a, x⁆ : G) : Matrix (Fin 2) (Fin 2) K) 1 1 = 1
  rw [he]
  constructor
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, ha, hx, neg_zero, mul_zero, add_zero]
    linear_combination (x 0 0 * x 1 1) * hda + hdx
  · constructor
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, ha, hx, neg_zero, mul_zero, zero_mul, zero_add, add_zero]
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, ha, hx, neg_zero, mul_zero, zero_mul, zero_add]
      linear_combination (x 0 0 * x 1 1) * hda + hdx

theorem upper_unitriangular_commute {p q : G}
    (hp00 : p 0 0 = 1) (hp10 : p 1 0 = 0) (hp11 : p 1 1 = 1)
    (hq00 : q 0 0 = 1) (hq10 : q 1 0 = 0) (hq11 : q 1 1 = 1) : p * q = q * p := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((p : Matrix (Fin 2) (Fin 2) K) * (q : Matrix (Fin 2) (Fin 2) K)) i j = _
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hp00, hp10, hp11, hq00, hq10, hq11, add_comm]

theorem upper_bicommutator_eq_one {a x y : G}
    (ha : a 1 0 = 0) (hx : x 1 0 = 0) (hy : y 1 0 = 0) : ⁅⁅a, x⁆, ⁅a, y⁆⁆ = 1 := by
  obtain ⟨hp00, hp10, hp11⟩ := upper_commutator_entries ha hx
  obtain ⟨hq00, hq10, hq11⟩ := upper_commutator_entries ha hy
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (upper_unitriangular_commute hp00 hp10 hp11 hq00 hq10 hq11)

theorem lower_bicommutator_eq_one {a x y : G}
    (ha : a 0 1 = 0) (hx : x 0 1 = 0) (hy : y 0 1 = 0) : ⁅⁅a, x⁆, ⁅a, y⁆⁆ = 1 := by
  let s : G := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  let e := MulAut.conj s
  have hc (g : G) : e g 1 0 = -g 0 1 := by
    change ((s * g * s⁻¹ : G) : Matrix (Fin 2) (Fin 2) K) 1 0 = _
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    change ((!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) *
      !![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) 1 0 = _
    norm_num [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have h := upper_bicommutator_eq_one (a := e a) (x := e x) (y := e y) (by simp only [hc, ha, neg_zero])
    (by simp only [hc, hx, neg_zero]) (by simp only [hc, hy, neg_zero])
  apply e.injective
  simpa only [map_commutatorElement, map_one] using h

end TransposeFollowup.SL2Escape

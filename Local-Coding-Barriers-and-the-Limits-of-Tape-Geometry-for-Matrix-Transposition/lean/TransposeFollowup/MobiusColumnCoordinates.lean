import TransposeFollowup.MobiusUnipotentMatrices

/-! Global algebraic coordinates on SL(2,R): a nonzero first column v
and a shear b, with second column Jv / (v₀² + v₁²) + b v. -/
namespace TransposeFollowup.RealMobius
open Classical
set_option autoImplicit false

def columnSqNorm (v : Fin 2 → ℝ) : ℝ := v 0 ^ 2 + v 1 ^ 2

theorem columnSqNorm_pos {v : Fin 2 → ℝ} (hv : v ≠ 0) : 0 < columnSqNorm v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simp_all
    simpa [columnSqNorm, h0] using sq_pos_of_ne_zero h1
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h0) (sq_nonneg _)

def firstColumn (g : Group) : Fin 2 → ℝ := fun i => g i 0

theorem firstColumn_ne_zero (g : Group) : firstColumn g ≠ 0 := by
  intro h
  have h0 : g 0 0 = 0 := congrFun h 0
  have h1 : g 1 0 = 0 := congrFun h 1
  have hd := determinant g
  simp [h0, h1] at hd

noncomputable def columnShear (g : Group) : ℝ :=
  (g 0 0 * g 0 1 + g 1 0 * g 1 1) / columnSqNorm (firstColumn g)

noncomputable def columnMatrix (v : Fin 2 → ℝ) (hv : v ≠ 0) (b : ℝ) : Group :=
  ⟨!![v 0, b * v 0 - v 1 / columnSqNorm v;
      v 1, b * v 1 + v 0 / columnSqNorm v], by
    have hq := (columnSqNorm_pos hv).ne'
    rw [Matrix.det_fin_two]
    dsimp
    field_simp
    simp only [columnSqNorm] at *
    ring⟩

theorem firstColumn_columnMatrix (v : Fin 2 → ℝ) (hv : v ≠ 0) (b : ℝ) :
    firstColumn (columnMatrix v hv b) = v := by
  funext i
  fin_cases i <;> rfl

theorem columnShear_columnMatrix (v : Fin 2 → ℝ) (hv : v ≠ 0) (b : ℝ) :
    columnShear (columnMatrix v hv b) = b := by
  have hq := (columnSqNorm_pos hv).ne'
  rw [columnShear, firstColumn_columnMatrix]
  change (v 0 * (b * v 0 - v 1 / columnSqNorm v) +
    v 1 * (b * v 1 + v 0 / columnSqNorm v)) / columnSqNorm v = b
  field_simp
  simp only [columnSqNorm]
  ring

theorem columnMatrix_coordinates (g : Group) :
    columnMatrix (firstColumn g) (firstColumn_ne_zero g) (columnShear g) = g := by
  have hq := (columnSqNorm_pos (firstColumn_ne_zero g)).ne'
  have hd := determinant g
  have h0 := congrArg (fun z : ℝ => g 0 0 * z) hd
  have h1 := congrArg (fun z : ℝ => g 1 0 * z) hd
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · change columnShear g * g 0 0 - g 1 0 / columnSqNorm (firstColumn g) = g 0 1
    rw [columnShear]
    field_simp
    simp only [columnSqNorm, firstColumn] at *
    nlinarith only [h1]
  · rfl
  · change columnShear g * g 1 0 + g 0 0 / columnSqNorm (firstColumn g) = g 1 1
    rw [columnShear]
    field_simp
    simp only [columnSqNorm, firstColumn] at *
    nlinarith only [h0]

theorem firstColumn_mul (g h : Group) :
    firstColumn (g * h) = Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) ℝ) (firstColumn h) := by
  funext i
  simp [firstColumn, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Matrix.mulVec,
    dotProduct]

theorem firstColumn_mul_upperUnipotent (g : Group) (b : ℝ) :
    firstColumn (g * upperUnipotent b) = firstColumn g := by
  rw [firstColumn_mul]
  funext i
  simp [firstColumn, upperUnipotent, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem columnShear_mul_upperUnipotent (g : Group) (b : ℝ) :
    columnShear (g * upperUnipotent b) = columnShear g + b := by
  have hq := (columnSqNorm_pos (firstColumn_ne_zero g)).ne'
  have he (i : Fin 2) : (g * upperUnipotent b) i 1 = g i 0 * b + g i 1 := by
    change ((g : Matrix (Fin 2) (Fin 2) ℝ) * !![1, b; 0, 1]) i 1 = _
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [columnShear, firstColumn_mul_upperUnipotent]
  have hf (i : Fin 2) : (g * upperUnipotent b) i 0 = g i 0 :=
    congrFun (firstColumn_mul_upperUnipotent g b) i
  simp only [he, hf]
  rw [columnShear]
  field_simp
  simp only [columnSqNorm, firstColumn]
  ring

theorem columnMatrix_eq_base_mul_upperUnipotent (v : Fin 2 → ℝ) (hv : v ≠ 0) (b : ℝ) :
    columnMatrix v hv b = columnMatrix v hv 0 * upperUnipotent b := by
  apply Subtype.ext
  change !![v 0, b * v 0 - v 1 / columnSqNorm v; v 1, b * v 1 + v 0 / columnSqNorm v] =
    !![v 0, 0 * v 0 - v 1 / columnSqNorm v; v 1, 0 * v 1 + v 0 / columnSqNorm v] *
      !![1, b; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end TransposeFollowup.RealMobius

import TransposeFollowup.RealMobiusAlgebra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Elementary entry bounds and identity neighborhoods of the existing real
Mobius matrix group. These definitions and proofs are shared by trace geometry
and the Haar/walk developments. -/
namespace TransposeFollowup.RealMobius
open Classical Set
set_option autoImplicit false

def mobiusIdentityDistanceSq (g : Group) : ℝ :=
  (g 0 0 - 1) ^ 2 + (g 0 1) ^ 2 + (g 1 0) ^ 2 + (g 1 1 - 1) ^ 2

def mobiusIdentityBall (η : ℝ) : Set Group := {g | mobiusIdentityDistanceSq g < η ^ 2}

theorem mobiusIdentityBall_entry_bounds {η : ℝ} (hη : 0 < η) {g : Group}
    (hg : g ∈ mobiusIdentityBall η) :
    |g 0 0 - 1| < η ∧ |g 0 1| < η ∧ |g 1 0| < η ∧ |g 1 1 - 1| < η := by
  change (g 0 0 - 1) ^ 2 + (g 0 1) ^ 2 + (g 1 0) ^ 2 + (g 1 1 - 1) ^ 2 < η ^ 2 at hg
  have h0 := sq_nonneg (g 0 0 - 1)
  have h1 := sq_nonneg (g 0 1)
  have h2 := sq_nonneg (g 1 0)
  have h3 := sq_nonneg (g 1 1 - 1)
  exact ⟨abs_lt_of_sq_lt_sq (by linarith) hη.le,
    abs_lt_of_sq_lt_sq (by linarith) hη.le,
    abs_lt_of_sq_lt_sq (by linarith) hη.le,
    abs_lt_of_sq_lt_sq (by linarith) hη.le⟩

def matrixEntryBox (B : ℝ) : Set Group := {g | ∀ i j : Fin 2, |g i j| ≤ B}

theorem one_mem_matrixEntryBox : (1 : Group) ∈ matrixEntryBox 1 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem matrixEntryBox_inv {B : ℝ} {g : Group} (hg : g ∈ matrixEntryBox B) :
    g⁻¹ ∈ matrixEntryBox B := by
  intro i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j
  · exact hg 1 1
  · change |-g 0 1| ≤ B
    simpa only [abs_neg] using hg 0 1
  · change |-g 1 0| ≤ B
    simpa only [abs_neg] using hg 1 0
  · exact hg 0 0

theorem matrixEntryBox_mul {B C : ℝ} {g h : Group}
    (hg : g ∈ matrixEntryBox B) (hh : h ∈ matrixEntryBox C) :
    g * h ∈ matrixEntryBox (2 * B * C) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hg 0 0)
  intro i j
  calc
    _ = |g i 0 * h 0 j + g i 1 * h 1 j| := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    _ ≤ |g i 0 * h 0 j| + |g i 1 * h 1 j| := abs_add_le _ _
    _ = |g i 0| * |h 0 j| + |g i 1| * |h 1 j| := by rw [abs_mul, abs_mul]
    _ ≤ B * C + B * C := add_le_add
      (mul_le_mul (hg i 0) (hh 0 j) (abs_nonneg _) hB)
      (mul_le_mul (hg i 1) (hh 1 j) (abs_nonneg _) hB)
    _ = _ := by ring

theorem mobiusIdentityBall_subset_entryBox_two {η : ℝ} (hη : 0 < η) (hηone : η ≤ 1) :
    mobiusIdentityBall η ⊆ matrixEntryBox 2 := by
  intro g hg
  obtain ⟨h00, h01, h10, h11⟩ := mobiusIdentityBall_entry_bounds hη hg
  have h00' : |g 0 0| ≤ 2 := by
    rw [abs_le]
    obtain ⟨hl, hu⟩ := abs_lt.mp h00
    constructor <;> linarith
  have h11' : |g 1 1| ≤ 2 := by
    rw [abs_le]
    obtain ⟨hl, hu⟩ := abs_lt.mp h11
    constructor <;> linarith
  have h01' : |g 0 1| ≤ 2 := by linarith
  have h10' : |g 1 0| ≤ 2 := by linarith
  intro i j
  fin_cases i <;> fin_cases j <;> assumption

end TransposeFollowup.RealMobius

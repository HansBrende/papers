import TransposeFollowup.ExpanderShearSupport
import TransposeFollowup.ShearGapEntropy

/-! The shear is columnwise and its actual inverse supports have bounded
cardinality and reuse. These properties concern the full cube. -/
namespace TransposeFollowup.ExpanderShear
open scoped BigOperators
open Classical
set_option autoImplicit false

noncomputable def inverseRows {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (r : Row m) : Finset (Row m) := Finset.univ.filter (fun c => matrix L r c ≠ 0)

theorem inverseRows_card_le {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit) (D : ℕ)
    (hrow : ∀ j, (Finset.univ.filter (fun i => L j i ≠ 0)).card ≤ D) (r : Row m) :
    (inverseRows L r).card ≤ D + 1 := matrix_row_support_le L D hrow r

theorem inverseRows_reuse_le {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit) (D : ℕ)
    (hcol : ∀ i, (Finset.univ.filter (fun j => L j i ≠ 0)).card ≤ D) (c : Row m) :
    (Finset.univ.filter (fun r => c ∈ inverseRows L r)).card ≤ D + 1 := by
  have he : Finset.univ.filter (fun r => c ∈ inverseRows L r) =
      Finset.univ.filter (fun r => matrix L r c ≠ 0) := by
    ext r
    simp [inverseRows]
  rw [he]
  exact matrix_col_support_le L D hcol c

theorem shear_row_eq_of_inverseRows {m W : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (r : Row m) (x y : Bank m W)
    (h : rowView (inverseRows L r) x = rowView (inverseRows L r) y) :
    shear L x r = shear L y r := by
  funext w
  simp only [shear_eq_mulVec, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : matrix L r c = 0
  · simp [hc]
  · have hmem : c ∈ inverseRows L r := by simp [inverseRows, hc]
    have he : x c w = y c w := congrFun (congrFun h ⟨c, hmem⟩) w
    rw [he]

/-- Full-cube inverse recovery uses exactly the declared stored-row view. -/
theorem rawRow_factorsThrough_inverseRows {m W : ℕ}
    (L : Matrix (Fin m) (Fin m) Bit) (r : Row m) :
    (fun x : Bank m W => x r).FactorsThrough
      (fun x => rowView (inverseRows L r) (shear L x)) := by
  intro x y h
  have he := shear_row_eq_of_inverseRows L r (shear L x) (shear L y) h
  rw [shear_involutive L x, shear_involutive L y] at he
  exact he

/-- A lane is independent of all other lane inputs. Grouping consecutive lanes
into matrix columns therefore gives forward column radius zero. -/
theorem shear_same_lane {m W : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (x y : Bank m W) (w : Fin W) (h : ∀ r, x r w = y r w) (r : Row m) :
    shear L x r w = shear L y r w := by
  rw [shear_eq_mulVec, shear_eq_mulVec]
  congr 1
  exact funext h

end TransposeFollowup.ExpanderShear

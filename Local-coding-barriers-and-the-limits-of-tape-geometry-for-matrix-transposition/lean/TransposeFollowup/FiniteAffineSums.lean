import TransposeFollowup.ClippedAffineRamps
import Mathlib.Algebra.BigOperators.Fin

/-! Reindex the existing range-sum cover theorem by Fin. -/
namespace TransposeFollowup.AffineMotion
open Classical Finset
set_option autoImplicit false

theorem HasAffineIntervalCover.sum_fin {J K : ℕ} {H : ℝ} (hH : 0 ≤ H)
    (f : Fin K → ℝ → ℝ) (hf : ∀ j, HasAffineIntervalCover J (f j) H) :
    HasAffineIntervalCover (J^K) (fun x => ∑ j, f j x) H := by
  let g : ℕ → ℝ → ℝ := fun j => if hj : j<K then f ⟨j,hj⟩ else fun _ => 0
  have hc := HasAffineIntervalCover.sum_range (J:=J) (Q:=K) hH g
    (fun j hj => by simpa only [g,dite_eq_left hj] using hf ⟨j,hj⟩)
  convert hc using 1
  funext x
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [g,dite_eq_left j.isLt]

end TransposeFollowup.AffineMotion

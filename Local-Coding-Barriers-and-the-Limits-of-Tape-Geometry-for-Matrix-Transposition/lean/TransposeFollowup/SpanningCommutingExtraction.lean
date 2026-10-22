import TransposeFollowup.SL2NearIdentityProducts
import TransposeFollowup.TraceCommutingExtraction

/-! The normalized mixed-product inclusion used by quantitative spanning
extraction. The earlier trimmed-extraction route is preserved in the
research archive and is no longer part of the active proof chain. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Matrix.Norms.Frobenius Pointwise ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem normalized_mixed_product_subset_power {A R : Set G} {n : ℕ} {h : G}
    (hAi : A⁻¹ = A) (hRA : R ⊆ A) (hh : h ∈ A ^ n) :
    A * ((fun x : G => h⁻¹ * x) '' R) * A⁻¹ ⊆ A ^ (n + 3) := by
  have hhi : h⁻¹ ∈ A ^ n := by
    have hx := Set.inv_mem_inv.mpr hh
    rwa [← inv_pow, hAi] at hx
  have hD : ((fun x : G => h⁻¹ * x) '' R) ⊆ A ^ (n + 1) := by
    rintro z ⟨x, hx, rfl⟩
    rw [pow_succ]
    exact Set.mul_mem_mul hhi (hRA hx)
  calc
    _ ⊆ A * A ^ (n + 1) * A :=
      Set.mul_subset_mul (Set.mul_subset_mul subset_rfl hD) hAi.subset
    _ = A ^ (1 + (n + 1) + 1) := by simp only [pow_add, pow_one, mul_assoc]
    _ = _ := by congr 1; omega


end TransposeFollowup.SL2Projection

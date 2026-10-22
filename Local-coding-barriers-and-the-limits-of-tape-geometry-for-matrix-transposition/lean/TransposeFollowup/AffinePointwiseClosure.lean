import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-! Affine functions on any real set form a finite-dimensional closed
subspace of the pointwise function space. The closure theorem is mathlib's;
only the two-coordinate evaluation map is specialized here. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Filter Topology
set_option autoImplicit false

noncomputable def affineEvaluation (D : Set ℝ) : (ℝ × ℝ) →ₗ[ℝ] (D → ℝ) where
  toFun v x := v.1*x.val+v.2
  map_add' v w := by ext x; simp; ring
  map_smul' a v := by ext x; simp; ring

theorem affine_on_of_tendsto {D : Set ℝ} {q : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hq : ∀ x ∈ D, Tendsto (fun n => q n x) atTop (𝓝 (f x)))
    (ha : ∀ᶠ n in atTop, ∃ a b : ℝ, ∀ x ∈ D, q n x=a*x+b) :
    ∃ a b : ℝ, ∀ x ∈ D, f x=a*x+b := by
  let L := affineEvaluation D
  have hc : IsClosed (L.range : Set (D → ℝ)) := L.range.closed_of_finiteDimensional
  have hconv : Tendsto (fun n (x : D) => q n x.val) atTop (𝓝 (fun x : D => f x.val)) :=
    tendsto_pi_nhds.mpr (fun x => hq x.val x.property)
  have hmem : (fun x : D => f x.val) ∈ L.range := hc.mem_of_tendsto hconv (by
    filter_upwards [ha] with n hn
    obtain ⟨a,b,hab⟩ := hn
    exact ⟨(a,b),funext (fun x => (hab x.val x.property).symm)⟩)
  obtain ⟨v,hv⟩ := hmem
  exact ⟨v.1,v.2,fun x hx => (congrFun hv ⟨x,hx⟩).symm⟩

end TransposeFollowup.AffineMotion

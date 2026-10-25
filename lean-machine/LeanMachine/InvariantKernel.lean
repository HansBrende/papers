import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Kernel dimension under an injective intertwining map whose image
contains the entire target kernel. -/

namespace LeanMachine.InvariantKernel

open Module

variable {K U W : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W]

theorem finrank_ker_eq (j : U →ₗ[K] W) (hj : Function.Injective j)
    (f : U →ₗ[K] U) (g : W →ₗ[K] W) (hcomm : g.comp j = j.comp f)
    (hcover : LinearMap.ker g ≤ LinearMap.range j) :
    finrank K (LinearMap.ker g) = finrank K (LinearMap.ker f) := by
  have heq : (LinearMap.ker f).map j = LinearMap.ker g := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      change g (j u) = 0
      have h : g (j u) = j (f u) := LinearMap.congr_fun hcomm u
      rw [h, LinearMap.mem_ker.mp hu, map_zero]
    · intro w hw
      obtain ⟨u, rfl⟩ := hcover hw
      refine ⟨u, ?_, rfl⟩
      change f u = 0
      apply hj
      rw [map_zero]
      have h : g (j u) = j (f u) := LinearMap.congr_fun hcomm u
      rw [← h]
      exact hw
  have h := LinearMap.finrank_range_of_inj (f := j.domRestrict (LinearMap.ker f))
    (fun u v h => Subtype.ext (hj h))
  rw [LinearMap.range_domRestrict, heq] at h
  exact h

end LeanMachine.InvariantKernel

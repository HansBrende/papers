import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Kernel bounds from certificates

Two facts for certifying an upper bound on the kernel of `x ↦ x B` over a field by exact computation:

* `finrank_ker_add_le_of_minor`: an invertible `r × r` minor of `B` gives
  `dim ker (x ↦ x B) + r ≤ n`.
* `connecting_injective`: kernel vectors `b` of `x ↦ x B₀`, kernel vectors `y` of `y ↦ B₀ y`, and an
  invertible matrix `C = (b_a B₁ · y_k)` make the connecting map `x₀ ↦ [x₀ B₁] ∈ coker B₀`
  injective on `ker (x ↦ x B₀)`.
-/

namespace LeanMachine.KernelCertificate

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

theorem finrank_ker_add_le_of_minor (B : Matrix (Fin n) (Fin n) K) {r : ℕ} (R S : Fin r → Fin n)
    (W : Matrix (Fin r) (Fin r) K) (hW : B.submatrix R S * W = 1) :
    Module.finrank K (LinearMap.ker (Matrix.vecMulLinear B)) + r ≤ n := by
  classical
  -- `P` places the rows `R`, `Q` picks the columns `S`
  let P : Matrix (Fin r) (Fin n) K := Matrix.of fun a i => if R a = i then 1 else 0
  let Q : Matrix (Fin n) (Fin r) K := Matrix.of fun j b => if j = S b then 1 else 0
  have hPBQ : P * B * Q = B.submatrix R S := by
    ext a b
    simp [P, Q, Matrix.mul_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']
  let ι : (Fin r → K) →ₗ[K] (Fin n → K) := Matrix.vecMulLinear P
  have hinj : Function.Injective ((Matrix.vecMulLinear B).comp ι) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : (y ᵥ* P) ᵥ* B = 0 := hy
    calc y = y ᵥ* (B.submatrix R S * W) := by rw [hW, vecMul_one]
      _ = (((y ᵥ* P) ᵥ* B) ᵥ* Q) ᵥ* W := by
        rw [← hPBQ, vecMul_vecMul, vecMul_vecMul, vecMul_vecMul, Matrix.mul_assoc,
          Matrix.mul_assoc]
      _ = 0 := by rw [h0, zero_vecMul, zero_vecMul]
  have hrange : r ≤ Module.finrank K (LinearMap.range (Matrix.vecMulLinear B)) := by
    calc r = Module.finrank K (Fin r → K) := (Module.finrank_fin_fun K).symm
      _ = Module.finrank K (LinearMap.range ((Matrix.vecMulLinear B).comp ι)) :=
        (LinearMap.finrank_range_of_inj hinj).symm
      _ ≤ Module.finrank K (LinearMap.range (Matrix.vecMulLinear B)) :=
        Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.vecMulLinear B)
  rw [Module.finrank_fin_fun] at hrn
  omega

theorem connecting_injective {q : ℕ} (B₀ B₁ : Matrix (Fin n) (Fin n) K)
    (b y : Fin q → Fin n → K) (C Cinv : Matrix (Fin q) (Fin q) K)
    (hb : ∀ a, b a ᵥ* B₀ = 0) (hy : ∀ k, B₀ *ᵥ y k = 0)
    (hC : ∀ a k, C a k = (b a ᵥ* B₁) ⬝ᵥ y k) (hCinv : C * Cinv = 1)
    (hdim : Module.finrank K (LinearMap.ker (Matrix.vecMulLinear B₀)) ≤ q)
    (x : Fin n → K) (hx : x ᵥ* B₀ = 0) (z : Fin n → K) (hz : x ᵥ* B₁ = z ᵥ* B₀) : x = 0 := by
  classical
  -- coefficients against `C` determine a combination of the `b a`
  have hcomb : ∀ c : Fin q → K, (∀ k, ((∑ a, c a • b a) ᵥ* B₁) ⬝ᵥ y k = 0) → c = 0 := by
    intro c hc
    have hcC : c ᵥ* C = 0 := by
      funext k
      have := hc k
      rw [Matrix.sum_vecMul, sum_dotProduct] at this
      calc (c ᵥ* C) k = ∑ a, c a * C a k := by simp [Matrix.vecMul, dotProduct]
        _ = ∑ a, ((c a • b a) ᵥ* B₁) ⬝ᵥ y k := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hC, Matrix.smul_vecMul, smul_dotProduct, smul_eq_mul]
        _ = 0 := this
    calc c = c ᵥ* (C * Cinv) := by rw [hCinv, vecMul_one]
      _ = 0 := by rw [← vecMul_vecMul, hcC, zero_vecMul]
  -- the `b a` are linearly independent elements of the kernel
  have hbker : ∀ a, b a ∈ LinearMap.ker (Matrix.vecMulLinear B₀) := fun a => hb a
  let b' : Fin q → LinearMap.ker (Matrix.vecMulLinear B₀) := fun a => ⟨b a, hbker a⟩
  have hli : LinearIndependent K b' := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : ∑ a, c a • b a = 0 := by
      have := congrArg Subtype.val hc
      simpa [b', Submodule.coe_sum] using this
    have : c = 0 := hcomb c (fun k => by rw [hc', zero_vecMul, zero_dotProduct])
    intro a
    simp [this]
  -- so they span the kernel
  have hspan : Submodule.span K (Set.range b') = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    have := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this ⊢
    omega
  have hxmem : (⟨x, hx⟩ : LinearMap.ker (Matrix.vecMulLinear B₀)) ∈
      Submodule.span K (Set.range b') := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hcx⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hxmem
  have hxc : ∑ a, c a • b a = x := by
    have := congrArg Subtype.val hcx
    simpa [b', Submodule.coe_sum] using this
  have hc0 : c = 0 := by
    apply hcomb c
    intro k
    rw [hxc, hz, ← dotProduct_mulVec, hy k, dotProduct_zero]
  rw [← hxc, hc0]
  simp

end LeanMachine.KernelCertificate

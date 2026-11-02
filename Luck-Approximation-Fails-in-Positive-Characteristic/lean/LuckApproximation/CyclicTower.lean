import LuckApproximation.Level1
import LeanMachine.CyclicBandedKernel
import LuckApproximation.Sanity

/-!
# Cyclic 3-power covers: the kernel stays 42, over every field of characteristic 3

`χ_j : F → C_{3^j}` sends generator `g` to `(volt g).val`. For a field `K` of characteristic 3, over
`K[C_{3^j}] = K[u]/(u^{3^j})` the operator `opK K` (the coefficients of `opA` mapped to `K`) is `Σᵢ uⁱ Bᵢ` with
the same `B₀`, `B₁` for every `j` (the coefficient of `u` in `(1+u)^v` is `v`). Injectivity of the connecting
map (`connecting_K`) then shows by induction that every kernel vector is `u^{3^j − 1}·b` with `b ∈ ker B₀`,
so the kernel has dimension at most 42 at every level, and `rk ≥ 110 − 42/3^j`.

The generic algebra (the basis `u^k` of `K[C_N]` when `uᴺ = 0`, and the banded kernel bound) is in
`LeanMachine.CyclicBandedKernel`; this file transports `φ_{F/N_j}(A)` to `K[C_{3^j}]`. Here `N_j = Ncyc j`
is called `U_j` in the paper, which reserves `N_k` for the congruence chain.
-/

namespace Luck.Op

open LeanMachine.CyclicAlg Matrix

/-- The cyclic voltage character of order `3^j`: generator `g ↦ (volt g).val`. -/
noncomputable def chiPow (j : ℕ) : F →* Multiplicative (ZMod (3 ^ j)) :=
  FreeGroup.lift fun g => Multiplicative.ofAdd (((Data.volt g).val : ℕ) : ZMod (3 ^ j))

/-- `N_j = ker χ_j`. -/
noncomputable def Ncyc (j : ℕ) : Subgroup F := (chiPow j).ker

instance Ncyc_normal (j : ℕ) : (Ncyc j).Normal := MonoidHom.normal_ker _

/-! ## `F/N_j ≅ C_{3^j}` -/

theorem volt_zero : Data.volt 0 = 1 := by decide +kernel

theorem chiPow_surjective (j : ℕ) : Function.Surjective (chiPow j) := by
  intro x
  refine ⟨FreeGroup.of 0 ^ (Multiplicative.toAdd x).val, ?_⟩
  rw [map_pow, chiPow, FreeGroup.lift_apply_of, volt_zero]
  have h1 : ((1 : ZMod 3).val : ℕ) = 1 := rfl
  rw [h1, Nat.cast_one, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]

/-- `F/N_j ≅ C_{3^j}`. -/
noncomputable def quotEquivj (j : ℕ) : F ⧸ Ncyc j ≃* Cyc (3 ^ j) :=
  QuotientGroup.quotientKerEquivOfSurjective (chiPow j) (chiPow_surjective j)

theorem quotEquivj_mk (j : ℕ) (g : F) : quotEquivj j (QuotientGroup.mk g) = chiPow j g := rfl

theorem card_quot_Ncyc (j : ℕ) : Nat.card (F ⧸ Ncyc j) = 3 ^ j := by
  rw [Nat.card_congr (quotEquivj j).toEquiv]
  simp

theorem index_Ncyc (j : ℕ) : (Ncyc j).index = 3 ^ j := by
  rw [Subgroup.index_eq_card, card_quot_Ncyc]

instance Ncyc_finiteIndex (j : ℕ) : (Ncyc j).FiniteIndex :=
  ⟨by rw [index_Ncyc]; positivity⟩

theorem isPGroup_Ncyc (j : ℕ) : IsPGroup 3 (F ⧸ Ncyc j) :=
  IsPGroup.of_card (card_quot_Ncyc j)

/-! ## The image of the operator in `K[C_{3^j}]` -/

/-- `χ_j` on the edge elements. -/
theorem chiPow_gamma (j : ℕ) (e : Fin 110) :
    chiPow j (gamma e) = Multiplicative.ofAdd (((voltE e).val : ℕ) : ZMod (3 ^ j)) := by
  unfold gamma voltE
  cases Data.edgeGen e with
  | none => simp
  | some g => simp [chiPow]

section Field

variable (K : Type*) [Field K] [CharP K 3]

/-- The operator with coefficients mapped to `K`. -/
noncomputable def opK : Matrix (Fin 110) (Fin 110) (MonoidAlgebra K F) :=
  opA.map (MonoidAlgebra.mapRingHom F (ι3 K))

/-- `single (ofAdd v) c = c (1 + v u + [v = 2] u²)` in `K[C_{3^j}]`, for `v ∈ {0, 1, 2}`. -/
theorem single_ofAdd_val (j : ℕ) (v : ZMod 3) (c : K) :
    MonoidAlgebra.single (Multiplicative.ofAdd ((v.val : ℕ) : ZMod (3 ^ j))) c =
      c • (1 : RN K (3 ^ j)) + (ι3 K v * c) • u K (3 ^ j) +
        (ι3 K (if v = 2 then 1 else 0) * c) • u K (3 ^ j) ^ 2 := by
  have hv : v = 0 ∨ v = 1 ∨ v = 2 := by revert v; decide
  have hsingle : ∀ m : ℕ, MonoidAlgebra.single
      (Multiplicative.ofAdd ((m : ℕ) : ZMod (3 ^ j))) c = c • T K (3 ^ j) ^ m := by
    intro m
    rw [T, MonoidAlgebra.single_pow, one_pow, MonoidAlgebra.smul_single', mul_one,
      ← ofAdd_nsmul, nsmul_one]
  rcases hv with rfl | rfl | rfl
  · have h0 : ((0 : ZMod 3).val : ℕ) = 0 := rfl
    have h02 : (0 : ZMod 3) ≠ 2 := by decide
    rw [h0, hsingle, pow_zero]
    simp [h02]
  · have h1 : ((1 : ZMod 3).val : ℕ) = 1 := rfl
    have h12 : (1 : ZMod 3) ≠ 2 := by decide
    rw [h1, hsingle, pow_one, T_eq]
    simp only [h12, ite_false, map_zero, zero_mul, zero_smul, add_zero, map_one, one_mul, smul_add]
    rw [add_comm]
  · have h2 : ((2 : ZMod 3).val : ℕ) = 2 := rfl
    rw [h2, hsingle, T_eq]
    simp only [ite_true, map_one, one_mul, Algebra.smul_def, map_mul, map_ofNat]
    ring

/-- The image of the operator in `K[C_{3^j}]`. -/
noncomputable def Abarj (j : ℕ) : Matrix (Fin 110) (Fin 110) (RN K (3 ^ j)) :=
  (opK K).map (MonoidAlgebra.mapDomainRingHom K (chiPow j))

theorem Abarj_apply (j : ℕ) (i k : Fin 110) :
    Abarj K j i k = (B0.map (ι3 K)) i k • (1 : RN K (3 ^ j)) + (B1.map (ι3 K)) i k • u K (3 ^ j) +
      (B2.map (ι3 K)) i k • u K (3 ^ j) ^ 2 := by
  simp only [Abarj, opK, Matrix.map_apply, opA, B0, B1, B2, Matrix.of_apply]
  cases entryEdge i k with
  | none => simp
  | some e =>
    simp only [MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, chiPow_gamma, map_mul]
    exact single_ofAdd_val K _ _ _

/-- Right multiplication by the image, as a `K`-linear map. -/
noncomputable def phiCj (j : ℕ) : (Fin 110 → RN K (3 ^ j)) →ₗ[K] (Fin 110 → RN K (3 ^ j)) where
  toFun w := w ᵥ* Abarj K j
  map_add' x y := Matrix.add_vecMul _ x y
  map_smul' c x := Matrix.smul_vecMul c x _

theorem phiCj_apply (j : ℕ) (w : Fin 110 → RN K (3 ^ j)) : phiCj K j w = w ᵥ* Abarj K j := rfl

theorem finrank_ker_phiCj_le (j : ℕ) :
    Module.finrank K (LinearMap.ker (phiCj K j)) ≤
      Module.finrank K (LinearMap.ker (Matrix.vecMulLinear (B0.map (ι3 K)))) :=
  finrank_ker_le (u_pow_eq_zero K j) (B0.map (ι3 K)) (B1.map (ι3 K)) (B2.map (ι3 K)) (Abarj K j)
    (Abarj_apply K j) (connecting_K K) (phiCj K j) (phiCj_apply K j)

/-! ## From `F/N_j` to `C_{3^j}` -/

/-- `K[F/N_j] ≅ K[C_{3^j}]` and its coordinatewise extension. -/
noncomputable def Eqj (j : ℕ) : MonoidAlgebra K (F ⧸ Ncyc j) ≃ₐ[K] RN K (3 ^ j) :=
  MonoidAlgebra.domCongr K K (quotEquivj j)

noncomputable def Lqj (j : ℕ) :
    (Fin 110 → MonoidAlgebra K (F ⧸ Ncyc j)) ≃ₗ[K] (Fin 110 → RN K (3 ^ j)) :=
  LinearEquiv.piCongrRight fun _ => (Eqj K j).toLinearEquiv

omit [CharP K 3] in
theorem Lqj_apply (j : ℕ) (w : Fin 110 → MonoidAlgebra K (F ⧸ Ncyc j)) (k : Fin 110) :
    Lqj K j w k = Eqj K j (w k) := rfl

theorem phi_apply_j (j : ℕ) (w : Fin 110 → MonoidAlgebra K (F ⧸ Ncyc j)) :
    phi K (Ncyc j) (opK K) w = w ᵥ* quotientMatrix K (Ncyc j) (opK K) := rfl

theorem Eqj_quotientMatrix (j : ℕ) (i k : Fin 110) :
    Eqj K j (quotientMatrix K (Ncyc j) (opK K) i k) = Abarj K j i k := by
  simp only [quotientMatrix, Abarj, opK, opA, Matrix.map_apply, Matrix.of_apply]
  cases entryEdge i k with
  | none => simp
  | some e =>
    simp only [MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, QuotientGroup.mk'_apply, Eqj, MonoidAlgebra.domCongr_single,
      quotEquivj_mk]

theorem phiCj_Lqj (j : ℕ) (w : Fin 110 → MonoidAlgebra K (F ⧸ Ncyc j)) :
    phiCj K j (Lqj K j w) = Lqj K j (phi K (Ncyc j) (opK K) w) := by
  funext k
  rw [phiCj_apply, phi_apply_j, Lqj_apply]
  simp only [Matrix.vecMul, dotProduct, Lqj_apply, map_sum, map_mul, Eqj_quotientMatrix]

theorem finrank_ker_phi_le_j (j : ℕ) :
    Module.finrank K (LinearMap.ker (phi K (Ncyc j) (opK K))) ≤
      Module.finrank K (LinearMap.ker (phiCj K j)) := by
  have hmaps : ∀ w ∈ LinearMap.ker (phi K (Ncyc j) (opK K)),
      (Lqj K j : (Fin 110 → MonoidAlgebra K (F ⧸ Ncyc j)) →ₗ[K]
        (Fin 110 → RN K (3 ^ j))) w ∈ LinearMap.ker (phiCj K j) := by
    intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    change phiCj K j (Lqj K j w) = 0
    rw [phiCj_Lqj, hw, map_zero]
  apply LinearMap.finrank_le_finrank_of_injective
    (f := (Lqj K j : (Fin 110 → MonoidAlgebra K (F ⧸ Ncyc j)) →ₗ[K]
      (Fin 110 → RN K (3 ^ j))).restrict hmaps)
  intro a b hab
  apply Subtype.ext
  exact (Lqj K j).injective (congrArg Subtype.val hab)

/-- **The kernel stays 42**: on the cyclic `3^j` cover the only kernel vectors are pulled back. -/
theorem finrank_ker_Ncyc_le (j : ℕ) :
    Module.finrank K (LinearMap.ker (phi K (Ncyc j) (opK K))) ≤ 42 :=
  (finrank_ker_phi_le_j K j).trans ((finrank_ker_phiCj_le K j).trans (finrank_ker_B0_K K))

theorem rk_Ncyc (j : ℕ) : (110 : ℝ) - 42 / 3 ^ j ≤ rk K (Ncyc j) (opK K) := by
  rw [rk_eq_sub, index_Ncyc]
  have hk : (Module.finrank K (LinearMap.ker (phi K (Ncyc j) (opK K))) : ℝ) ≤ 42 := by
    exact_mod_cast finrank_ker_Ncyc_le K j
  push_cast
  gcongr

end Field

end Luck.Op

import LuckApproximation.Sanity
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Semantic checks of `LuckApproximation.Statement`

Checks of what the definitions mean, written independently of their docstrings. Standard axioms
only.

* Definitional checks: `K` acts coefficientwise; `K[G] → K[G/N]` sends `g` to `gN`; multiplication
  in `K[G/N]` is convolution in the order `g * h`; `phi` multiplies row vectors on the right.
* `rk_zero`: `rk(0) = 0`.
* `isEmpty_chain_of_finite`, `infinite_of_chain`: only infinite groups carry chains.
* `luck_freeGroup_zero`: the conjecture holds vacuously for the trivial free group, so `r = 0`
  cannot witness `MainTheoremTarget`. (For `r = 1` the group is `ℤ`, amenable, where parts (1)
  and (2) are a theorem.)
* `rk_one_sub_single`: `rk_{G/N}(1 − g) = 1 − 1/ord(gN)` for the `1 × 1` matrix `(1 − g)`, and
  `intChain_tendsto`: along `2ⁱℤ` this is `1 − 2⁻ⁱ → 1`, a non-trivial instance of convergence.
* `chain_ssubset`, `iInf_eq_bot_iff`, `rkSeq_congr`: chains strictly shrink as sets; `⨅ = ⊥` is
  trivial intersection; `rkSeq` depends only on the subgroups.
-/

open Luck Filter Topology

namespace Luck.Checks

section Defeq
variable (K : Type) [Field K] {G : Type} [Group G] (N : Subgroup G) [N.Normal]

/-- The `K`-action on `K[G/N]^n` is coefficientwise scalar multiplication. -/
example (n : ℕ) (c : K) (x : Fin n → MonoidAlgebra K (G ⧸ N)) (i : Fin n) (g : G ⧸ N) :
    ((c • x) i).coeff g = c * (x i).coeff g := rfl

/-- The quotient ring map sends `g` to `gN`. -/
example (g : G) (a : K) :
    MonoidAlgebra.mapDomainRingHom K (QuotientGroup.mk' N) (MonoidAlgebra.single g a)
      = MonoidAlgebra.single (QuotientGroup.mk g : G ⧸ N) a := by
  simp [MonoidAlgebra.mapDomain_single]

/-- Multiplication in `K[H]` is convolution, `g * h` in that order. -/
example (g h : G ⧸ N) (a b : K) :
    MonoidAlgebra.single g a * MonoidAlgebra.single h b = MonoidAlgebra.single (g * h) (a * b) :=
  MonoidAlgebra.single_mul_single _ _ _ _

/-- `phi` is right multiplication: for a `1 × 1` matrix `(a)`, `phi (x) = (x * a)`. -/
example (a : MonoidAlgebra K G) (x : Fin 1 → MonoidAlgebra K (G ⧸ N)) :
    phi K N (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => a) x 0
      = x 0 * MonoidAlgebra.mapDomainRingHom K (QuotientGroup.mk' N) a := by
  simp [phi_apply]

end Defeq

section Rk
variable (K : Type) [Field K] {G : Type} [Group G] (N : Subgroup G) [N.Normal]

theorem rk_zero [N.FiniteIndex] (n m : ℕ) :
    rk K N (0 : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) = 0 := by
  have h0 : phi K N (0 : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) = 0 := by
    ext x j
    simp [phi_apply]
  unfold rk
  rw [h0, LinearMap.range_zero, finrank_bot]
  simp

end Rk

/-- A finite group has no chains (strictly descending sequences of subgroups do not exist). -/
theorem isEmpty_chain_of_finite (G : Type) [Group G] [Finite G] : IsEmpty (Chain G) := by
  constructor
  intro c
  have : Finite (Subgroup G) := by
    have : Finite (Set G) := Set.instFinite
    exact Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  exact not_injective_infinite_finite c.N c.strictAnti.injective

/-- `r = 0` is not a silly witness for `MainTheoremTarget`: the conjecture holds vacuously. -/
theorem luck_freeGroup_zero (K : Type) [Field K] : LuckApproximation K (FreeGroup (Fin 0)) := by
  have : Finite (FreeGroup (Fin 0)) := by
    have : Subsingleton (FreeGroup (Fin 0)) := inferInstance
    exact Finite.of_subsingleton
  have := isEmpty_chain_of_finite (FreeGroup (Fin 0))
  exact ⟨fun _ _ _ c => isEmptyElim c, fun _ _ _ c => isEmptyElim c⟩



/-- Proof irrelevance: `rkSeq` does not depend on which normality or finite-index proof is used. -/
example (K : Type) [Field K] {G : Type} [Group G] (c : Chain G) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) (i : ℕ) (h : (c.N i).Normal)
    (hf : (c.N i).FiniteIndex) :
    c.rkSeq K A i = @rk K _ G _ (c.N i) h hf n m A := rfl

section OneMinus
variable (K : Type) [Field K] {Q : Type} [Group Q] [Finite Q] (q : Q)

/-- `u ↦ Σ_h u(h⟨q⟩) h`: elements of `K[Q]` whose coefficients are constant on left cosets
`h⟨q⟩`. -/
noncomputable def cosetFun : (Q ⧸ Subgroup.zpowers q → K) →ₗ[K] MonoidAlgebra K Q :=
  (MonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap ∘ₗ
    (Finsupp.linearEquivFunOnFinite K K Q).symm.toLinearMap ∘ₗ
    LinearMap.funLeft K K (QuotientGroup.mk : Q → Q ⧸ Subgroup.zpowers q)

lemma coeff_cosetFun (u : Q ⧸ Subgroup.zpowers q → K) (h : Q) :
    (cosetFun K q u).coeff h = u (h : Q ⧸ Subgroup.zpowers q) := by
  simp [cosetFun, LinearMap.funLeft]

lemma cosetFun_injective : Function.Injective (cosetFun K q) := by
  intro u v huv
  funext c
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective c
  have := congrArg (fun x => MonoidAlgebra.coeff x h) huv
  simpa [coeff_cosetFun] using this

omit [Finite Q] in
lemma mul_one_sub_eq_zero_iff (x : MonoidAlgebra K Q) :
    x * (1 - MonoidAlgebra.single q 1) = 0 ↔ ∀ h, x.coeff (h * q⁻¹) = x.coeff h := by
  rw [mul_sub, mul_one, sub_eq_zero]
  constructor
  · intro hx h
    have := congrArg (fun y => MonoidAlgebra.coeff y h) hx
    simp only [MonoidAlgebra.coeff_mul_single_apply, mul_one] at this
    exact this.symm
  · intro hx
    ext h
    simp [MonoidAlgebra.coeff_mul_single_apply, hx]

omit [Field K] [Finite Q] in
lemma invariant_zpow (v : Q → K) (hv : ∀ h, v (h * q⁻¹) = v h) (k : ℤ) (h : Q) :
    v (h * q ^ k) = v h := by
  induction k using Int.induction_on generalizing h with
  | zero => simp
  | succ k ih =>
    have := hv (h * q ^ (k : ℤ) * q)
    rw [mul_inv_cancel_right] at this
    rw [zpow_add_one, ← mul_assoc, ← this, ih]
  | pred k ih =>
    have := hv (h * q ^ (-(k : ℤ)))
    rw [zpow_sub_one, ← mul_assoc, this, ih]

lemma ker_eq_range :
    LinearMap.ker (LinearMap.mulRight K (1 - MonoidAlgebra.single q (1 : K))) =
      LinearMap.range (cosetFun K q) := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mulRight_apply, mul_one_sub_eq_zero_iff, LinearMap.mem_range]
  constructor
  · intro hx
    refine ⟨fun c => x.coeff c.out, ?_⟩
    ext h
    rw [coeff_cosetFun]
    have hrel : ((QuotientGroup.mk h : Q ⧸ Subgroup.zpowers q).out : Q ⧸ Subgroup.zpowers q)
        = QuotientGroup.mk h := QuotientGroup.out_eq' _
    rw [QuotientGroup.eq] at hrel
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hrel
    have := invariant_zpow K q (⇑x.coeff) hx k (QuotientGroup.mk h : Q ⧸ Subgroup.zpowers q).out
    rw [hk, mul_inv_cancel_left] at this
    exact this.symm
  · rintro ⟨u, rfl⟩ h
    rw [coeff_cosetFun, coeff_cosetFun]
    congr 1
    rw [QuotientGroup.eq]
    simp [mul_assoc]

lemma finrank_ker_mulRight :
    Module.finrank K (LinearMap.ker (LinearMap.mulRight K (1 - MonoidAlgebra.single q (1 : K)))) =
      (Subgroup.zpowers q).index := by
  rw [ker_eq_range, LinearMap.finrank_range_of_inj (cosetFun_injective K q)]
  have : Fintype (Q ⧸ Subgroup.zpowers q) := Fintype.ofFinite _
  rw [Module.finrank_fintype_fun_eq_card, Subgroup.index, Nat.card_eq_fintype_card]

end OneMinus

/-- **`rk_{G/N}(1 - g) = 1 - 1/ord(gN)`** for the `1 × 1` matrix `(1 - g)`. -/
theorem rk_one_sub_single (K : Type) [Field K] {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    [N.FiniteIndex] (g : G) :
    rk K N (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (1 - MonoidAlgebra.single g (1 : K))) =
      1 - 1 / (orderOf (g : G ⧸ N) : ℝ) := by
  have hfin : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  set q : G ⧸ N := (g : G ⧸ N) with hq
  set A : Matrix (Fin 1) (Fin 1) (MonoidAlgebra K G) :=
    Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (1 - MonoidAlgebra.single g (1 : K)) with hA
  have hphi : ∀ x, phi K N A x = fun _ => x 0 * (1 - MonoidAlgebra.single q 1) := by
    intro x
    funext j
    simp only [phi_apply, hA, hq, Matrix.of_apply, Fin.sum_univ_one, map_sub, map_one,
      MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, QuotientGroup.mk'_apply]
  have hker : Module.finrank K (LinearMap.ker (phi K N A)) = (Subgroup.zpowers q).index := by
    rw [← finrank_ker_mulRight K q]
    let e := LinearEquiv.funUnique (Fin 1) K (MonoidAlgebra K (G ⧸ N))
    have hc : LinearMap.ker (phi K N A) =
        (LinearMap.ker (LinearMap.mulRight K (1 - MonoidAlgebra.single q (1 : K)))).comap
          e.toLinearMap := by
      ext x
      simp only [LinearMap.mem_ker, Submodule.mem_comap, LinearMap.mulRight_apply, hphi]
      constructor
      · intro h
        exact congrFun h 0
      · intro h
        funext j
        simpa [e] using h
    rw [hc, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have hidx : ((Subgroup.zpowers q).index : ℝ) * (orderOf q : ℝ) = (N.index : ℝ) := by
    have := (Subgroup.zpowers q).index_mul_card
    rw [Nat.card_zpowers] at this
    exact_mod_cast this
  have hN : (N.index : ℝ) ≠ 0 := by exact_mod_cast Subgroup.FiniteIndex.index_ne_zero
  have hord : (orderOf q : ℝ) ≠ 0 := by exact_mod_cast (orderOf_pos q).ne'
  have hH : ((Subgroup.zpowers q).index : ℝ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite
  rw [rk_eq_sub, hker]
  push_cast
  rw [← hidx]
  field_simp

/-- Along the chain `2ⁱℤ`, the rank of `1 - t` is `1 - 2⁻ⁱ`. -/
theorem intChain_rkSeq (K : Type) [Field K] (i : ℕ) :
    intChain.rkSeq K (Matrix.of fun (_ : Fin 1) (_ : Fin 1) =>
      (1 - MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : K))) i =
      1 - 1 / (2 : ℝ) ^ i := by
  have := intChain.normal i
  have := intChain.finiteIndex i
  have hidx : (intChain.N i).index = 2 ^ i := by
    change (AddSubgroup.toSubgroup (AddSubgroup.zmultiples ((2 : ℤ) ^ i))).index = 2 ^ i
    rw [AddSubgroup.index_toSubgroup, Int.index_zmultiples, Int.natAbs_pow]
    rfl
  have hord : orderOf ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) :
      Multiplicative ℤ ⧸ intChain.N i) = 2 ^ i := by
    rw [orderOf_eq_card_of_forall_mem_zpowers, ← Subgroup.index, hidx]
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨Multiplicative.toAdd y, ?_⟩
    simp only
    rw [← QuotientGroup.mk_zpow]
    congr 1
    rw [← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
  unfold Chain.rkSeq
  rw [rk_one_sub_single, hord]
  push_cast
  ring

theorem intChain_tendsto (K : Type) [Field K] :
    Tendsto (intChain.rkSeq K (Matrix.of fun (_ : Fin 1) (_ : Fin 1) =>
      (1 - MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : K)))) atTop (𝓝 1) := by
  have h : intChain.rkSeq K (Matrix.of fun (_ : Fin 1) (_ : Fin 1) =>
      (1 - MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : K))) =
      fun i => 1 - (1 / 2 : ℝ) ^ i := by
    funext i
    rw [intChain_rkSeq, one_div_pow]
  rw [h]
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_sub (1 : ℝ)
  simpa using this


section Chains
variable {G : Type} [Group G]

/-- `StrictAnti` in the subgroup lattice is strict inclusion of carriers, in the descending
direction. -/
theorem chain_ssubset (c : Chain G) {i j : ℕ} (h : i < j) : (c.N j : Set G) ⊂ (c.N i : Set G) :=
  SetLike.coe_ssubset_coe.mpr (c.strictAnti h)

/-- `⨅ i, N i = ⊥` is exactly "trivial intersection". -/
theorem iInf_eq_bot_iff (N : ℕ → Subgroup G) :
    (⨅ i, N i = ⊥) ↔ ∀ g : G, (∀ i, g ∈ N i) → g = 1 := by
  rw [eq_bot_iff]
  constructor
  · intro h g hg
    exact (Subgroup.mem_bot).mp (h (Subgroup.mem_iInf.mpr hg))
  · intro h g hg
    exact (Subgroup.mem_bot).mpr (h g (Subgroup.mem_iInf.mp hg))

/-- Only infinite groups carry chains. -/
theorem infinite_of_chain (c : Chain G) : Infinite G := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have : Finite (Subgroup G) := by
    have : Finite (Set G) := Set.instFinite
    exact Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  exact not_injective_infinite_finite c.N c.strictAnti.injective

/-- `rkSeq` depends on a chain only through its subgroups (the `Prop` fields are irrelevant). -/
theorem rkSeq_congr (K : Type) [Field K] {c c' : Chain G} (h : c.N = c'.N) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) : c.rkSeq K A = c'.rkSeq K A := by
  obtain ⟨N, _, _, _, _⟩ := c
  obtain ⟨N', _, _, _, _⟩ := c'
  cases h
  rfl

end Chains

end Luck.Checks

import LuckApproximation.Sanity
import Mathlib.Algebra.Order.Star.Real
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.PicardGroup

/-!
# Monotonicity of normalised ranks along p-chains

Bergeron–Linnell–Lück–Sauer (2014), Lemma 4.1, for the cokernel of `A`, with the step-by-step argument of
Kionke (2017), Lemma 2.6 and Theorem 2.5: over a field of characteristic `p`, if `N' ≤ N` are normal subgroups of finite index and `G/N'` is a
`p`-group, then `rk_{G/N}(A) ≤ rk_{G/N'}(A)` (`Luck.rk_le_rk_of_isPGroup`).

## Proof

* **Reduction to cyclic steps** (`rk_le_rk_of_isPGroup`), by strong induction on `|G : N'|`. If
  `N' < N`, the image of `N` in the `p`-group `G/N'` is a nontrivial normal subgroup, so it meets
  the centre nontrivially (`Group.IsNilpotent.inf_center_ne_bot_of_normal`), and by Cauchy it
  contains a central `ζ` of order `p`. The preimage `N₁` of `⟨ζ⟩` is normal, `N' ≤ N₁ ≤ N`,
  `|G : N'| = p |G : N₁|` and `G/N₁` is a `p`-group; the induction hypothesis gives
  `rk_{G/N} ≤ rk_{G/N₁}`, and the step below gives `rk_{G/N₁} ≤ rk_{G/N'}`.
* **One step** (`rk_le_rk_of_cyclic_step`): `N' ≤ N₁`, every element of `N₁/N'` is a power of
  `ζ`, `ζ ^ p = 1` and `|G : N'| = p |G : N₁|`. Put `Q' = G/N'`, `Q = G/N₁`,
  `π : K[Q'] → K[Q]` and `s = ζ - 1 ∈ K[Q']`. Then `s ^ p = ζ ^ p - 1 = 0` in characteristic `p`,
  and `ker π ⊆ s K[Q']` (`exists_mul_of_mapDomainRingHom_eq_zero`, via a set-theoretic section of
  `Q' → Q`).
* **Linear algebra** (`finrank_range_vecMulLin_map_le`, `finrank_filtration_le`). Let
  `V' = K[Q']^m`, `R' = Im φ_A^{Q'} ⊆ V'` and `T = s · (-)` on `V'`. `R'` is `T`-stable and
  `T ^ p = 0`, so the chain `R' + T^i V'` (`i = 0, …, p`) runs from `V'` down to `R'` and each
  layer has dimension at most `dim V' / (R' + T V')`. Since `ker π ⊆ T V'` and `π(R') = Im φ_A^Q`,
  that codimension is at most `m |Q| - rank_Q`. Hence `m |Q'| - rank_{Q'} ≤ p (m |Q| - rank_Q)`,
  i.e. `p · rank_Q ≤ rank_{Q'}`, which is the claim because `|Q'| = p |Q|`.

Instead of the coinvariant formulation `dim M ≤ |H| dim M_H` for the whole `p`-group
`H = N/N'`, the proof peels off one central subgroup of order `p` at a time, so no quotient of `H`
ever has to act on a quotient space.
-/

namespace Luck

open Module

/-! ### Linear algebra -/

/-- A nilpotent filtration bound: if `R` is `T`-stable and `T ^ p = 0`, then
`dim V - dim R ≤ p · (dim V - dim (R + T V))`, stated without subtraction. -/
theorem finrank_filtration_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : V →ₗ[K] V) (R : Submodule K V) (hR : ∀ x ∈ R, T x ∈ R)
    (p : ℕ) (hT : T ^ p = 0) :
    finrank K V + p * finrank K ↥(R ⊔ LinearMap.range T) ≤ p * finrank K V + finrank K R := by
  set U : ℕ → Submodule K V := fun i => R ⊔ LinearMap.range (T ^ i) with hU
  have hRi : ∀ i, ∀ x ∈ R, (T ^ i) x ∈ R := by
    intro i
    induction i with
    | zero => intro x hx; simpa using hx
    | succ i ih =>
      intro x hx
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (hR x hx)
  -- each layer `U i / U (i+1)` is an image of `V / U 1` under `T ^ i`
  have hlayer : ∀ i, finrank K (U i) + finrank K (U 1) ≤ finrank K V + finrank K (U (i + 1)) := by
    intro i
    obtain ⟨C, hC⟩ := (U 1).exists_isCompl
    have hsum := Submodule.finrank_add_eq_of_isCompl hC
    have hle : U i ≤ U (i + 1) ⊔ C.map (T ^ i) := by
      apply sup_le
      · exact le_sup_left.trans le_sup_left
      · rintro _ ⟨x, rfl⟩
        have hx : x ∈ U 1 ⊔ C := by rw [hC.sup_eq_top]; trivial
        obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
        rw [map_add]
        apply Submodule.add_mem_sup
        · obtain ⟨r, hr, t, ht, rfl⟩ := Submodule.mem_sup.mp hu
          rw [map_add]
          apply Submodule.add_mem_sup (hRi i r hr)
          obtain ⟨y, rfl⟩ := ht
          exact LinearMap.mem_range.mpr ⟨y, by rw [← Module.End.mul_apply, ← pow_add]⟩
        · exact Submodule.mem_map_of_mem hc
    have h1 := Submodule.finrank_mono hle
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (U (i + 1)) (C.map (T ^ i))
    have h3 := Submodule.finrank_map_le (T ^ i) C
    omega
  have hmain : ∀ i, finrank K V + i * finrank K (U 1) ≤ i * finrank K V + finrank K (U i) := by
    intro i
    induction i with
    | zero =>
      have : U 0 = ⊤ := by
        simp only [hU, pow_zero]
        rw [Module.End.one_eq_id, LinearMap.range_id, sup_top_eq]
      rw [this, finrank_top]; omega
    | succ i ih =>
      have := hlayer i
      rw [add_mul, add_mul, one_mul, one_mul]
      omega
  have hU1 : U 1 = R ⊔ LinearMap.range T := by simp [hU]
  have hUp : U p = R := by simp [hU, hT]
  have := hmain p
  rw [hU1, hUp] at this
  exact this

/-- `x ↦ x B` (row vector times matrix) as a `K`-linear map. By definition,
`phi K N A = vecMulLin K (quotientMatrix K N A)`. -/
def vecMulLin (K : Type*) [Field K] {S : Type*} [Ring S] [Module K S] [IsScalarTower K S S]
    {n m : ℕ} (B : Matrix (Fin n) (Fin m) S) : (Fin n → S) →ₗ[K] (Fin m → S) where
  toFun x := Matrix.vecMul x B
  map_add' x y := Matrix.add_vecMul _ x y
  map_smul' c x := Matrix.smul_vecMul c x _

/-- The key estimate for one step, for an abstract surjective `K`-linear ring map `π : R' → R`
whose kernel consists of left multiples of an element `s` with `s ^ p = 0`:
`dim R'^m + p · rank (B.map π) ≤ p · dim R^m + rank B`. -/
theorem finrank_range_vecMulLin_map_le {K : Type*} [Field K] {R' R : Type*} [Ring R'] [Ring R]
    [Module K R'] [Module K R] [IsScalarTower K R' R'] [IsScalarTower K R R]
    [SMulCommClass K R' R'] [FiniteDimensional K R'] [FiniteDimensional K R]
    (π : R' →+* R) (hπlin : ∀ (c : K) (x : R'), π (c • x) = c • π x)
    (hπ : Function.Surjective π) (s : R') (p : ℕ) (hs : s ^ p = 0)
    (hker : ∀ x, π x = 0 → ∃ y, x = s * y) {n m : ℕ} (B : Matrix (Fin n) (Fin m) R') :
    finrank K (Fin m → R') + p * finrank K (LinearMap.range (vecMulLin K (B.map π))) ≤
      p * finrank K (Fin m → R) + finrank K (LinearMap.range (vecMulLin K B)) := by
  let πL : R' →ₗ[K] R := { toFun := π, map_add' := π.map_add, map_smul' := hπlin }
  let Pm : (Fin m → R') →ₗ[K] (Fin m → R) := πL.compLeft (Fin m)
  let Pn : (Fin n → R') →ₗ[K] (Fin n → R) := πL.compLeft (Fin n)
  -- left multiplication by `s`, coordinatewise
  let T : (Fin m → R') →ₗ[K] (Fin m → R') :=
    { toFun := fun x j => s * x j
      map_add' := fun x y => funext fun j => mul_add s (x j) (y j)
      map_smul' := fun c x => funext fun j => mul_smul_comm c s (x j) }
  have hTpow : ∀ i (x : Fin m → R'), (T ^ i) x = fun j => s ^ i * x j := by
    intro i
    induction i with
    | zero => intro x; funext j; simp
    | succ i ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, ih]
      funext j
      simp only [T, LinearMap.coe_mk, AddHom.coe_mk, pow_succ', mul_assoc]
  have hT : T ^ p = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [hTpow]
    funext j
    simp [hs]
  set φ' := vecMulLin K B with hφ'
  set φ := vecMulLin K (B.map π) with hφ
  -- `Im φ'` is stable under `T`
  have hstab : ∀ x ∈ LinearMap.range φ', T x ∈ LinearMap.range φ' := by
    rintro _ ⟨y, rfl⟩
    refine ⟨fun i => s * y i, ?_⟩
    funext j
    simp only [hφ', vecMulLin, T, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMul, dotProduct,
      Finset.mul_sum, mul_assoc]
  -- `ker π ⊆ s R'`, coordinatewise
  have hkerT : LinearMap.ker Pm ≤ LinearMap.range T := by
    intro x hx
    have hx' : ∀ j, π (x j) = 0 := fun j => congrFun hx j
    choose y hy using fun j => hker (x j) (hx' j)
    exact ⟨y, funext fun j => (hy j).symm⟩
  have hPn : Function.Surjective Pn := fun y =>
    ⟨fun i => Function.surjInv hπ (y i), funext fun i => Function.surjInv_eq hπ (y i)⟩
  have hPm : Function.Surjective Pm := fun y =>
    ⟨fun i => Function.surjInv hπ (y i), funext fun i => Function.surjInv_eq hπ (y i)⟩
  have hcomm : Pm ∘ₗ φ' = φ ∘ₗ Pn := by
    refine LinearMap.ext fun x => funext fun j => ?_
    exact RingHom.map_vecMul π B x j
  have hrange : (LinearMap.range φ').map Pm = LinearMap.range φ := by
    rw [← LinearMap.range_comp, hcomm,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hPn)]
  -- `codim (Im φ' + ker π) = dim R^m - dim π(Im φ')`
  have hid : finrank K (Fin m → R') + finrank K ((LinearMap.range φ').map Pm) =
      finrank K (Fin m → R) + finrank K ↥(LinearMap.range φ' ⊔ LinearMap.ker Pm) := by
    set W := (LinearMap.range φ').map Pm
    let g := W.mkQ ∘ₗ Pm
    have hg : LinearMap.range g = ⊤ := LinearMap.range_eq_top.mpr (W.mkQ_surjective.comp hPm)
    have hkg : LinearMap.ker g = LinearMap.range φ' ⊔ LinearMap.ker Pm := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_map_eq]
    have h1 := LinearMap.finrank_range_add_finrank_ker g
    rw [hg, hkg, finrank_top] at h1
    have h2 := W.finrank_quotient_add_finrank
    omega
  have hfil := finrank_filtration_le T (LinearMap.range φ') hstab p hT
  have hmono : finrank K ↥(LinearMap.range φ' ⊔ LinearMap.ker Pm) ≤
      finrank K ↥(LinearMap.range φ' ⊔ LinearMap.range T) :=
    Submodule.finrank_mono (sup_le_sup_left hkerT _)
  rw [← hrange]
  have hmul := Nat.mul_le_mul_left p hmono
  have hid' := congrArg (p * ·) hid
  simp only [mul_add] at hid'
  omega

/-! ### Group algebras -/

/-- If `f : Q' →* Q` is surjective and every element of its kernel is a power of `ζ`, then every
element of the kernel of `K[Q'] → K[Q]` is a left multiple of `ζ - 1`. -/
theorem exists_mul_of_mapDomainRingHom_eq_zero {K : Type*} [Field K] {Q' Q : Type*} [Group Q']
    [Group Q] (f : Q' →* Q) (hf : Function.Surjective f) (ζ : Q')
    (hker : ∀ q, f q = 1 → ∃ j : ℕ, q = ζ ^ j) (x : MonoidAlgebra K Q')
    (hx : MonoidAlgebra.mapDomainRingHom K f x = 0) :
    ∃ y, x = (MonoidAlgebra.single ζ (1 : K) - 1) * y := by
  classical
  set g := Function.surjInv hf with hg
  set s : MonoidAlgebra K Q' := MonoidAlgebra.single ζ (1 : K) - 1 with hs
  -- `x - σ(π x) ∈ s K[Q']` for the section `σ = mapDomain g` of `π = mapDomain f`
  have key : ∀ x : MonoidAlgebra K Q',
      ∃ y, x - MonoidAlgebra.mapDomain g (MonoidAlgebra.mapDomain f x) = s * y := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, ?_⟩
      rw [MonoidAlgebra.mapDomain_add, MonoidAlgebra.mapDomain_add, mul_add, ← ha, ← hb]
      abel
    | single q c =>
      rw [MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single]
      have hq₀ : f (g (f q)) = f q := Function.surjInv_eq hf _
      obtain ⟨j, hj⟩ := hker (q * (g (f q))⁻¹) (by rw [map_mul, map_inv, hq₀, mul_inv_cancel])
      have hq : q = ζ ^ j * g (f q) := by rw [← hj, inv_mul_cancel_right]
      refine ⟨(∑ i ∈ Finset.range j, MonoidAlgebra.single ζ (1 : K) ^ i) *
        MonoidAlgebra.single (g (f q)) c, ?_⟩
      rw [← mul_assoc, hs, mul_geom_sum, MonoidAlgebra.single_pow, one_pow, sub_mul, one_mul,
        MonoidAlgebra.single_mul_single, one_mul, ← hq]
  obtain ⟨y, hy⟩ := key x
  refine ⟨y, ?_⟩
  have h0 : MonoidAlgebra.mapDomain f x = 0 := hx
  rw [h0, MonoidAlgebra.mapDomain_zero, sub_zero] at hy
  exact hy

/-! ### One cyclic step -/

/-- One step: `N' ≤ N₁`, every element of `N₁/N'` is a power of `ζ`, `ζ ^ p = 1`, and
`|G : N'| = p |G : N₁|`. -/
theorem rk_le_rk_of_cyclic_step {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {G : Type*} [Group G] (N₁ N' : Subgroup G) [N₁.Normal] [N'.Normal] [N₁.FiniteIndex]
    [N'.FiniteIndex] (hle : N' ≤ N₁) (ζ : G ⧸ N') (hζ : ζ ^ p = 1)
    (hker : ∀ g ∈ N₁, ∃ j : ℕ, (g : G ⧸ N') = ζ ^ j) (hidx : N'.index = p * N₁.index)
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) :
    rk K N₁ A ≤ rk K N' A := by
  classical
  have := finiteDimensional_quotient K N'
  have := finiteDimensional_quotient K N₁
  let f : G ⧸ N' →* G ⧸ N₁ := QuotientGroup.map N' N₁ (MonoidHom.id G) (by simpa using hle)
  have hfmk : ∀ g : G, f (g : G ⧸ N') = (g : G ⧸ N₁) := fun g => rfl
  have hf : Function.Surjective f := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H g => exact ⟨(g : G ⧸ N'), hfmk g⟩
  have hfk : ∀ q : G ⧸ N', f q = 1 → ∃ j : ℕ, q = ζ ^ j := by
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [hfmk] at hq
      exact hker g ((QuotientGroup.eq_one_iff g).mp hq)
  set π := MonoidAlgebra.mapDomainRingHom K f with hπdef
  have hπlin : ∀ (c : K) (x : MonoidAlgebra K (G ⧸ N')), π (c • x) = c • π x :=
    fun c x => MonoidAlgebra.mapDomain_smul _ _ _
  have hπ : Function.Surjective π := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero π⟩
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add π a b⟩
    | single q c =>
      obtain ⟨q', rfl⟩ := hf q
      exact ⟨MonoidAlgebra.single q' c, MonoidAlgebra.mapDomain_single⟩
  set s : MonoidAlgebra K (G ⧸ N') := MonoidAlgebra.single ζ (1 : K) - 1 with hsdef
  have hs : s ^ p = 0 := by
    have : CharP (MonoidAlgebra K (G ⧸ N')) p := charP_of_injective_algebraMap' K p
    rw [hsdef, sub_pow_char_of_commute p (Commute.one_right _), MonoidAlgebra.single_pow, one_pow,
      one_pow, hζ, ← MonoidAlgebra.one_def, sub_self]
  have hπker : ∀ x, π x = 0 → ∃ y, x = s * y :=
    exists_mul_of_mapDomainRingHom_eq_zero f hf ζ hfk
  have hQ : quotientMatrix K N₁ A = (quotientMatrix K N' A).map π := by
    ext i j
    simp only [quotientMatrix, Matrix.map_apply]
    rw [← RingHom.comp_apply, hπdef, ← MonoidAlgebra.mapDomainRingHom_comp]
    congr 2
  have key := finrank_range_vecMulLin_map_le π hπlin hπ s p hs hπker (quotientMatrix K N' A)
  rw [← hQ] at key
  have e1 : vecMulLin K (quotientMatrix K N₁ A) = phi K N₁ A := rfl
  have e2 : vecMulLin K (quotientMatrix K N' A) = phi K N' A := rfl
  rw [e1, e2, finrank_domain, finrank_domain, hidx] at key
  have hb : p * finrank K (LinearMap.range (phi K N₁ A)) ≤
      finrank K (LinearMap.range (phi K N' A)) := by
    have : m * (p * N₁.index) = p * (m * N₁.index) := by ring
    omega
  unfold rk
  rw [hidx]
  have hi : (0 : ℝ) < N₁.index := by
    exact_mod_cast Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [div_le_div_iff₀ hi (by push_cast; positivity)]
  have hb' : (p : ℝ) * finrank K (LinearMap.range (phi K N₁ A)) ≤
      finrank K (LinearMap.range (phi K N' A)) := by exact_mod_cast hb
  push_cast
  nlinarith

/-! ### The theorem -/

theorem rk_le_rk_of_isPGroup {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {G : Type*} [Group G] (N N' : Subgroup G) [N.Normal] [N'.Normal] [N.FiniteIndex]
    [N'.FiniteIndex] (hle : N' ≤ N) (hp : IsPGroup p (G ⧸ N')) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) :
    rk K N A ≤ rk K N' A := by
  classical
  -- strong induction on `|G : N'|`
  suffices H : ∀ k : ℕ, ∀ (N' : Subgroup G) [N'.Normal] [N'.FiniteIndex], N'.index = k →
      N' ≤ N → IsPGroup p (G ⧸ N') → rk K N A ≤ rk K N' A from H _ N' rfl hle hp
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro N' _ _ hk hle hp
  by_cases hNN : N = N'
  · subst hNN
    exact le_rfl
  have hfin : Finite (G ⧸ N') := Subgroup.finite_quotient_of_finiteIndex
  have hnil : Group.IsNilpotent (G ⧸ N') := hp.isNilpotent
  -- the image `H = N/N'` is a nontrivial normal subgroup of the `p`-group `G/N'`
  set H : Subgroup (G ⧸ N') := N.map (QuotientGroup.mk' N') with hHdef
  have hHn : H.Normal := Subgroup.Normal.map ‹N.Normal› _ (QuotientGroup.mk'_surjective N')
  have hHbot : H ≠ ⊥ := by
    intro hbot
    apply hNN
    refine le_antisymm (fun g hg => ?_) hle
    have hgH : QuotientGroup.mk' N' g ∈ H := Subgroup.mem_map_of_mem _ hg
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hgH
    exact hgH
  -- a central element `ζ ∈ H` of order `p`
  have hS := Group.IsNilpotent.inf_center_ne_bot_of_normal hHbot
  have hSp : IsPGroup p ↥(H ⊓ Subgroup.center (G ⧸ N')) := hp.to_subgroup _
  have hSdvd : p ∣ Nat.card ↥(H ⊓ Subgroup.center (G ⧸ N')) := by
    rcases hSp.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hS
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hSdvd
  set ζ : G ⧸ N' := (x : G ⧸ N') with hζdef
  have hζord : orderOf ζ = p := by rw [hζdef, Subgroup.orderOf_coe]; exact hx
  have hζH : ζ ∈ H := (Subgroup.mem_inf.mp x.2).1
  have hζZ : ζ ∈ Subgroup.center (G ⧸ N') := (Subgroup.mem_inf.mp x.2).2
  have hCZ : Subgroup.zpowers ζ ≤ Subgroup.center (G ⧸ N') := Subgroup.zpowers_le.mpr hζZ
  have hCn : (Subgroup.zpowers ζ).Normal := Subgroup.normal_of_le_center hCZ
  -- its preimage `N₁`: `N' ≤ N₁ ≤ N`, `|G : N'| = p |G : N₁|`
  set N₁ : Subgroup G := (Subgroup.zpowers ζ).comap (QuotientGroup.mk' N') with hN₁def
  have hN₁n : N₁.Normal := hCn.comap _
  have hle₁ : N' ≤ N₁ := by
    intro g hg
    show QuotientGroup.mk' N' g ∈ Subgroup.zpowers ζ
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).mpr hg]
    exact (Subgroup.zpowers ζ).one_mem
  have hN₁f : N₁.FiniteIndex := Subgroup.finiteIndex_of_le hle₁
  have hN₁N : N₁ ≤ N := by
    intro g hg
    have hg' : QuotientGroup.mk' N' g ∈ H := (Subgroup.zpowers_le.mpr hζH) hg
    obtain ⟨g', hg'N, hgg'⟩ := Subgroup.mem_map.mp hg'
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hgg'
    have := N.mul_mem hg'N (hle hgg')
    simpa using this
  have hidx : N'.index = p * N₁.index := by
    have h1 : N₁.index = (Subgroup.zpowers ζ).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N')
    have h2 := (Subgroup.zpowers ζ).index_mul_card
    rw [Nat.card_zpowers, hζord] at h2
    rw [h1, Subgroup.index_eq_card, ← h2, mul_comm]
  have hp₁ : IsPGroup p (G ⧸ N₁) := by
    refine hp.of_surjective (QuotientGroup.map N' N₁ (MonoidHom.id G) (by simpa using hle₁)) ?_
    intro y
    induction y using QuotientGroup.induction_on with
    | H g => exact ⟨(g : G ⧸ N'), rfl⟩
  have hlt : N₁.index < k := by
    rw [← hk, hidx]
    have h1 : 0 < N₁.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    have h2 : 1 < p := (Fact.out : p.Prime).one_lt
    nlinarith
  have IH := ih N₁.index hlt N₁ rfl hN₁N hp₁
  have hker : ∀ g ∈ N₁, ∃ j : ℕ, (g : G ⧸ N') = ζ ^ j := by
    intro g hg
    have hg' : QuotientGroup.mk' N' g ∈ Submonoid.powers ζ :=
      mem_powers_iff_mem_zpowers.mpr hg
    obtain ⟨j, hj⟩ := hg'
    exact ⟨j, hj.symm⟩
  have hζp : ζ ^ p = 1 := by rw [← hζord]; exact pow_orderOf_eq_one ζ
  exact IH.trans (rk_le_rk_of_cyclic_step p N₁ N' hle₁ ζ hζp hker hidx A)

/-- **Part (1) along `p`-chains**: in characteristic `p`, along every chain with `p`-group quotients the ranks
are non-decreasing (`rk_le_rk_of_isPGroup`) and at most `n`, so they converge. -/
theorem exists_tendsto_of_isPGroup {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {G : Type*} [Group G] (c : Chain G) (hp : ∀ i, haveI := c.normal i; IsPGroup p (G ⧸ c.N i))
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) :
    ∃ l, Filter.Tendsto (c.rkSeq K A) Filter.atTop (nhds l) := by
  have hmono : Monotone (c.rkSeq K A) := by
    refine monotone_nat_of_le_succ fun i => ?_
    have := c.normal i
    have := c.normal (i + 1)
    have := c.finiteIndex i
    have := c.finiteIndex (i + 1)
    exact rk_le_rk_of_isPGroup p (c.N i) (c.N (i + 1)) (c.strictAnti.antitone (Nat.le_succ i))
      (hp (i + 1)) A
  have hbdd : BddAbove (Set.range (c.rkSeq K A)) := by
    refine ⟨n, ?_⟩
    rintro _ ⟨i, rfl⟩
    have := c.normal i
    have := c.finiteIndex i
    exact rk_le K (c.N i) A
  exact ⟨_, tendsto_atTop_ciSup hmono hbdd⟩

end Luck

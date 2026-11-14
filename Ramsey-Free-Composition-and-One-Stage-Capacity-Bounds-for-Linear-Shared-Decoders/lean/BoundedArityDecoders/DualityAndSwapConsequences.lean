import BoundedArityDecoders.OperatorDualityProofs
import BoundedArityDecoders.SwapCodeAnswersProofs
import SharedDecoders.CapacityTP
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Operator Duality Consequences, Mask-Floor Realization, & Multi-Scale Swap Corollaries

Kernel-verified theorems extending `OperatorDualityProofs` and `SwapCodeAnswersProofs`:

1. **Explicit `TensorProduct` Anti-Diagonal Untwisting & Mask-Floor Realization**:
   * `antiDiagTensorEquiv`: explicit `LinearEquiv` `((ZMod d → F) ⊗[F] (ZMod d → A)) ≃ₗ[F] State d A`
     mapping pure tensors `u ⊗ₜ v` to `fun c j => u c • v (j + c)`.
   * `coordShiftLinear` & `antiDiagTensorEquiv_intertwines_rot`: column rotation `rotLinear F t`
     intertwines with `LinearMap.lTensor (ZMod d → F) (coordShiftLinear F d A t)` (`I_d ⊗ σ^t`).
   * `leftComponentSubmodule`, `shiftSetCovarianceSubmodule`, & `shiftSetCovariance_tensor_finrank`:
     `antiDiagTensorEquiv` maps `U_E ⊗ ⊤` onto `H_E(p)` with exact dimension
     `finrank F H_E(p) = finrank F U_E * (d * finrank F A)`.
   * `maskFloor_GenericSubspaceRealization`: explains why positive-term Grassmann/mask bounds stall
     once `C_s = rotLinear F (-s) C_0` is dropped, together with an explicit alternating-mask
     separation on even `d = 2 * m` (`m ≥ 2`).

2. **General `(d, R)` Bounded-OSR Pipeline Pass Lower Bound**:
   * `isRowOrColUniform_rankLe_one` & `boundedOSRPipelinePassLowerBound`: any pipeline with
     `t = heavyIndices.card` passes of Operator Schmidt Rank `≤ R` and arbitrarily many passes of
     Operator Schmidt Rank `≤ 1` realizing `gridSwapLinear F d b` satisfies `d^2 ≤ R^t` and
     (for `2 ≤ R`) `2 * Real.log d / Real.log R ≤ t`.

3. **Discrete Shannon Mutual Information `= 0` & Row-Diagonal Gauge Invariance**:
   * `uniformShannonMI`, `uniformShannonMI_eq_zero_of_indep`, &
     `skewOneTimePad_ShannonMutualInfoZero`: under uniform `X ∈ State d (Fin b → Bool)`, every cell
     `W_{r, c}` of `W = Xᵀ ⊕ X` has zero discrete Shannon mutual information with every source
     column `X_{:, c'}`.
   * `rowDiagonal_SourceArityGaugeInvariance`: output-row source arity is invariant under two-sided
     multiplication by `IsRowDiagonalOp` gauges `D₁ ∘ K ∘ D₀`, in contrast to Operator Schmidt Rank
     where `rowShearLinear = rowShearLinear ∘ id` jumps from `rk_⊗(id) ≤ 1` to exact `rk_⊗ = d`.

4. **Unified Three-Term Swap-Code Corollary (`Remark 5.6` of Paper 17)**:
   * `bonus1_UnifiedThreeTermExceedsPairingBound`: explicit `7 * 8 / 2 < 29`, `4 * 5 / 2 < 11`, and
     unified 3-term swap-code corollary exceeding the pairing value `d * (d + 1) / 2` over every
     field `F` for `d ∈ {3, 4, 6, 7, 9, 12}` (extending Paper 17 `Remark 5.6`'s `d = 3, 4` examples
     to `d = 6, 7, 9, 12` and all fields at `d = 4`, while `d = 5` and other `d ≥ 8` remain open).

5. **Bonus 2 Asymptotic `1/2 d^2 + o(d^2)` Consequences & Walsh Dichotomy**:
   * `bonus2_SublinearProfileAndTendstoHalf`: `(ε, δ)` sublinear profile bound and `Filter.Tendsto`
     `1/2 d^2 + o(d^2)` sequence bound from `bonus2_MultiscaleIntervalBothSides`.
   * `walshBitSet`, `cyclicBoundaryCount`, `walshBitSet_cyclicBoundaryCount`,
     `walshBitSet_joint_separates_points`, `walshDigitMaskRotSpan_finrank_le`, &
     `bonus2_WalshDichotomyStructuralProperties`.
-/

namespace BoundedArityDecoders

open SharedDecoders Module
open scoped BigOperators TensorProduct

/-! ### 1. Explicit `TensorProduct` Anti-Diagonal Untwisting & Mask-Floor Realization -/

section AntiDiagTensor

/-- Coordinate linear isomorphism `((ι → F) ⊗[F] M) ≃ₗ[F] (ι → M)` over a finite index type `ι`,
mapping pure tensors `u ⊗ₜ m` to `fun c => u c • m`. -/
def piLeftTensorEquiv (F : Type*) [Field F] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (M : Type*) [AddCommGroup M] [Module F M] :
    ((ι → F) ⊗[F] M) ≃ₗ[F] (ι → M) :=
  let fwdBilin : (ι → F) →ₗ[F] M →ₗ[F] (ι → M) :=
    { toFun := fun u =>
        { toFun := fun m c => u c • m
          map_add' := fun m₁ m₂ => funext fun c => smul_add (u c) m₁ m₂
          map_smul' := fun a m => funext fun c => smul_comm (u c) a m }
      map_add' := fun u₁ u₂ =>
        LinearMap.ext fun m => funext fun c => add_smul (u₁ c) (u₂ c) m
      map_smul' := fun a u =>
        LinearMap.ext fun m => funext fun c => mul_smul a (u c) m }
  let fwd : ((ι → F) ⊗[F] M) →ₗ[F] (ι → M) := TensorProduct.lift fwdBilin
  let invLin : (ι → M) →ₗ[F] ((ι → F) ⊗[F] M) :=
    ∑ c : ι,
      (TensorProduct.mk F (ι → F) M (Pi.single (M := fun _ : ι => F) c 1)).comp
        (LinearMap.proj (R := F) (φ := fun _ : ι => M) c)
  LinearEquiv.ofLinearMap fwd invLin
    (by
      apply LinearMap.ext
      intro f
      funext c'
      simp only [LinearMap.comp_apply, LinearMap.id_apply, invLin, LinearMap.sum_apply,
        LinearMap.proj_apply, TensorProduct.mk_apply, map_sum, Finset.sum_apply]
      change (∑ c : ι, (Pi.single (M := fun _ : ι => F) c 1 c') • f c) = f c'
      rw [Finset.sum_eq_single c']
      · simp
      · intro c _ hc
        simp [Pi.single_eq_of_ne hc.symm]
      · intro h
        exact absurd (Finset.mem_univ c') h)
    (by
      refine TensorProduct.ext' fun u m => ?_
      simp only [LinearMap.comp_apply, LinearMap.id_apply, invLin, LinearMap.sum_apply,
        LinearMap.proj_apply, TensorProduct.mk_apply]
      have hf : ∀ c : ι, fwd (u ⊗ₜ[F] m) c = u c • m := fun _ => rfl
      simp only [hf]
      have hsum :
          (∑ c : ι, (Pi.single (M := fun _ : ι => F) c 1) ⊗ₜ[F] (u c • m)) =
            (∑ c : ι, u c • Pi.single (M := fun _ : ι => F) c 1) ⊗ₜ[F] m := by
        rw [TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      have hu : (∑ c : ι, u c • Pi.single (M := fun _ : ι => F) c 1) = u := by
        funext c'
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single c']
        · simp
        · intro c _ hc
          simp [Pi.single_eq_of_ne hc.symm]
        · intro h
          exact absurd (Finset.mem_univ c') h
      rw [hsum, hu])

/-- Linear equivalence version of `fromAntiDiagLinear` and `antiDiagLinear` on `State d A`. -/
def fromAntiDiagLinearEquiv (F : Type*) [Field F] (d : ℕ) (A : Type*)
    [AddCommGroup A] [Module F A] :
    State d A ≃ₗ[F] State d A where
  toLinearMap := fromAntiDiagLinear F d A
  invFun := antiDiagLinear F d A
  left_inv Z := by
    funext c a
    simp [sub_add_cancel]
  right_inv X := by
    funext c j
    simp [add_sub_cancel_right]

/-- **Explicit Anti-Diagonal `TensorProduct` Isomorphism.**
Linear isomorphism `((ZMod d → F) ⊗[F] (ZMod d → A)) ≃ₗ[F] State d A` (`[NeZero d]`) sending every
pure tensor `u ⊗ₜ v` to `fromAntiDiagLinear F d A (fun c a => u c • v a) = fun c j => u c • v (j + c)`. -/
def antiDiagTensorEquiv (F : Type*) [Field F] (d : ℕ) [NeZero d] (A : Type*)
    [AddCommGroup A] [Module F A] :
    ((ZMod d → F) ⊗[F] (ZMod d → A)) ≃ₗ[F] State d A :=
  (piLeftTensorEquiv F (ZMod d) (ZMod d → A)).trans (fromAntiDiagLinearEquiv F d A)

@[simp]
theorem antiDiagTensorEquiv_tmul (F : Type*) [Field F] (d : ℕ) [NeZero d] (A : Type*)
    [AddCommGroup A] [Module F A] (u : ZMod d → F) (v : ZMod d → A) :
    antiDiagTensorEquiv F d A (u ⊗ₜ[F] v) =
      fromAntiDiagLinear F d A (fun c a => u c • v a) :=
  rfl

@[simp]
theorem antiDiagTensorEquiv_tmul_apply (F : Type*) [Field F] (d : ℕ) [NeZero d] (A : Type*)
    [AddCommGroup A] [Module F A] (u : ZMod d → F) (v : ZMod d → A) (c j : ZMod d) :
    antiDiagTensorEquiv F d A (u ⊗ₜ[F] v) c j = u c • v (j + c) :=
  rfl

/-- Left-shift operator `σ^t` on anti-diagonal profiles `ZMod d → A`:
`(coordShiftLinear F d A t v) a = v (a + t)`. -/
def coordShiftLinear (F : Type*) [Semiring F] (d : ℕ) (A : Type*)
    [AddCommMonoid A] [Module F A] (t : ZMod d) :
    (ZMod d → A) →ₗ[F] (ZMod d → A) :=
  LinearMap.pi fun a => LinearMap.proj (R := F) (φ := fun _ : ZMod d => A) (a + t)

@[simp]
theorem coordShiftLinear_apply (F : Type*) [Semiring F] (d : ℕ) (A : Type*)
    [AddCommMonoid A] [Module F A] (t : ZMod d) (v : ZMod d → A) (a : ZMod d) :
    coordShiftLinear F d A t v a = v (a + t) :=
  rfl

/-- **Right-Factor Shift Intertwining.**
Under `antiDiagTensorEquiv`, column rotation `rotLinear F t` on `State d A` intertwines with the
pure right-factor shift `LinearMap.lTensor (ZMod d → F) (coordShiftLinear F d A t)` (`I_d ⊗ σ^t`
on `(ZMod d → F) ⊗[F] (ZMod d → A)`). -/
theorem antiDiagTensorEquiv_intertwines_rot (F : Type*) [Field F] (d : ℕ) [NeZero d] (A : Type*)
    [AddCommGroup A] [Module F A] (t : ZMod d) :
    (antiDiagTensorEquiv F d A).toLinearMap.comp
        (LinearMap.lTensor (ZMod d → F) (coordShiftLinear F d A t)) =
      (rotLinear F t).comp (antiDiagTensorEquiv F d A).toLinearMap ∧
    (antiDiagTensorEquiv F d A).symm.toLinearMap.comp (rotLinear F t) =
      (LinearMap.lTensor (ZMod d → F) (coordShiftLinear F d A t)).comp
        (antiDiagTensorEquiv F d A).symm.toLinearMap := by
  have hfwd :
      (antiDiagTensorEquiv F d A).toLinearMap.comp
          (LinearMap.lTensor (ZMod d → F) (coordShiftLinear F d A t)) =
        (rotLinear F t).comp (antiDiagTensorEquiv F d A).toLinearMap := by
    refine TensorProduct.ext' fun u v => ?_
    funext c j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul,
      antiDiagTensorEquiv_tmul_apply, coordShiftLinear_apply, rotLinear_apply, rot_apply]
    rw [add_right_comm]
  refine ⟨hfwd, ?_⟩
  apply LinearMap.ext
  intro X
  apply (antiDiagTensorEquiv F d A).injective
  have h := congrArg (fun L => L ((antiDiagTensorEquiv F d A).symm X)) hfwd.symm
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using h

/-- Left-factor component subspace `U_E(p) ≤ (ZMod d → F)` consisting of vectors constant on the
connected components `Relation.EqvGen (SwapRigidity.Link p E)` of the shift-link graph. -/
def leftComponentSubmodule (F : Type*) [Field F] {d : ℕ} {κ : Type*}
    (p : ZMod d → κ) (E : Finset (ZMod d)) : Submodule F (ZMod d → F) where
  carrier := {u | ∀ c c' : ZMod d, Relation.EqvGen (SwapRigidity.Link p E) c c' → u c = u c'}
  add_mem' := fun {u v} hu hv c c' hrel => by simp [hu c c' hrel, hv c c' hrel]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun a {u} hu c c' hrel => by simp [hu c c' hrel]

/-- Shift-set covariance subspace `H_E(p) ≤ State d A` consisting of states satisfying
`InShiftSetCovariance p E`. -/
def shiftSetCovarianceSubmodule (F : Type*) [Field F] {d : ℕ} {κ : Type*}
    (p : ZMod d → κ) (E : Finset (ZMod d)) (A : Type*) [AddCommGroup A] [Module F A] :
    Submodule F (State d A) where
  carrier := {X | InShiftSetCovariance p E X}
  add_mem' := fun {X Y} hX hY c c' δ δ' hδ hδ' hp hsum j => by
    simp [hX c c' δ δ' hδ hδ' hp hsum j, hY c c' δ δ' hδ hδ' hp hsum j]
  zero_mem' := fun _ _ _ _ _ _ _ _ _ => rfl
  smul_mem' := fun a {X} hX c c' δ δ' hδ hδ' hp hsum j => by
    simp [hX c c' δ δ' hδ hδ' hp hsum j]

private noncomputable def linkRep {d : ℕ} {κ : Type*}
    (p : ZMod d → κ) (E : Finset (ZMod d)) (c : ZMod d) : ZMod d :=
  let S : Set (ZMod d) := {x | Relation.EqvGen (SwapRigidity.Link p E) c x}
  have hne : S.Nonempty := ⟨c, Relation.EqvGen.refl c⟩
  Classical.choose hne

private lemma linkRep_rel {d : ℕ} {κ : Type*}
    (p : ZMod d → κ) (E : Finset (ZMod d)) (c : ZMod d) :
    Relation.EqvGen (SwapRigidity.Link p E) c (linkRep p E c) := by
  let S : Set (ZMod d) := {x | Relation.EqvGen (SwapRigidity.Link p E) c x}
  have hne : S.Nonempty := ⟨c, Relation.EqvGen.refl c⟩
  exact Classical.choose_spec hne

private lemma linkRep_eq_iff {d : ℕ} {κ : Type*}
    (p : ZMod d → κ) (E : Finset (ZMod d)) (c c' : ZMod d) :
    linkRep p E c = linkRep p E c' ↔ Relation.EqvGen (SwapRigidity.Link p E) c c' := by
  constructor
  · intro hEq
    have h1 := linkRep_rel p E c
    have h2 := linkRep_rel p E c'
    rw [← hEq] at h2
    exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.symm _ _ h2)
  · intro hrel
    have hSet : {x : ZMod d | Relation.EqvGen (SwapRigidity.Link p E) c x} =
        {x : ZMod d | Relation.EqvGen (SwapRigidity.Link p E) c' x} := by
      ext x
      constructor
      · exact fun hcx => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hrel) hcx
      · exact fun hc'x => Relation.EqvGen.trans _ _ _ hrel hc'x
    dsimp only [linkRep]
    congr 1

private lemma linkRep_idem {d : ℕ} {κ : Type*}
    (p : ZMod d → κ) (E : Finset (ZMod d)) (c : ZMod d) :
    linkRep p E (linkRep p E c) = linkRep p E c :=
  ((linkRep_eq_iff p E (linkRep p E c) c).mpr
    (Relation.EqvGen.symm _ _ (linkRep_rel p E c)))

private noncomputable def linkRepFinset {d : ℕ} [NeZero d] {κ : Type*}
    (p : ZMod d → κ) (E : Finset (ZMod d)) : Finset (ZMod d) :=
  letI := Classical.decEq (ZMod d)
  Finset.univ.image (linkRep p E)

private lemma mem_linkRepFinset_iff {d : ℕ} [NeZero d] {κ : Type*}
    (p : ZMod d → κ) (E : Finset (ZMod d)) (r : ZMod d) :
    r ∈ linkRepFinset p E ↔ linkRep p E r = r := by
  classical
  simp only [linkRepFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩
    exact linkRep_idem p E c
  · intro hr
    exact ⟨r, hr⟩

private lemma linkRep_mem_linkRepFinset {d : ℕ} [NeZero d] {κ : Type*}
    (p : ZMod d → κ) (E : Finset (ZMod d)) (c : ZMod d) :
    linkRep p E c ∈ linkRepFinset p E :=
  (mem_linkRepFinset_iff p E _).mpr (linkRep_idem p E c)

private lemma finrank_leftComponentSubmodule (F : Type*) [Field F] {d : ℕ} [NeZero d]
    {κ : Type*} (p : ZMod d → κ) (E : Finset (ZMod d)) :
    finrank F (leftComponentSubmodule F p E) = (linkRepFinset p E).card := by
  classical
  let Reps := linkRepFinset p E
  let e : leftComponentSubmodule F p E ≃ₗ[F] (Reps → F) :=
    { toFun := fun u r => u.1 r.1
      invFun := fun w =>
        ⟨fun c => w ⟨linkRep p E c, linkRep_mem_linkRepFinset p E c⟩,
         fun c c' hrel => by
           have hEq : linkRep p E c = linkRep p E c' := (linkRep_eq_iff p E c c').mpr hrel
           simp_rw [hEq]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun u => Subtype.ext (funext fun c =>
        (u.2 c (linkRep p E c) (linkRep_rel p E c)).symm)
      right_inv := fun w => funext fun r => by
        have hr : linkRep p E r.1 = r.1 := (mem_linkRepFinset_iff p E r.1).mp r.2
        have hsub : (⟨linkRep p E r.1, linkRep_mem_linkRepFinset p E r.1⟩ : Reps) = r :=
          Subtype.ext hr
        exact congrArg w hsub }
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

/-- Left-factor subspace of `ZMod d → F` whose coordinates agree with `linkRep p E c` outside a
chosen subset `S` of non-representative rows. -/
private def partialLeftSubmodule (F : Type*) [Field F] {d : ℕ} {κ : Type*}
    (p : ZMod d → κ) (E : Finset (ZMod d)) (S : Finset (ZMod d)) :
    Submodule F (ZMod d → F) where
  carrier := {u | ∀ c : ZMod d, c ∉ S → u c = u (linkRep p E c)}
  add_mem' := fun {u v} hu hv c hc => by simp [hu c hc, hv c hc]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun r {u} hu c hc => by simp [hu c hc]

/-- Subspace of `State d A` whose anti-diagonal profile agrees with `linkRep p E c` outside a
chosen subset `S ⊆ Finset.univ \ linkRepFinset p E` of non-representative rows. -/
private def partialLeftExtensionSubmodule (F : Type*) [Field F] {d : ℕ} {κ : Type*}
    (p : ZMod d → κ) (E : Finset (ZMod d)) (A : Type*) [AddCommGroup A] [Module F A]
    (S : Finset (ZMod d)) : Submodule F (State d A) where
  carrier := {X | ∀ c : ZMod d, c ∉ S → ∀ a : ZMod d,
    antiDiagLinear F d A X c a = antiDiagLinear F d A X (linkRep p E c) a}
  add_mem' := fun {X Y} hX hY c hc a => by
    simp only [map_add, Pi.add_apply]
    rw [hX c hc a, hY c hc a]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun r {X} hX c hc a => by
    simp only [map_smul, Pi.smul_apply]
    rw [hX c hc a]

private lemma map_partialLeftSubmodule_eq (F : Type*) [Field F] {d : ℕ} [NeZero d]
    {κ : Type*} (p : ZMod d → κ) (E : Finset (ZMod d))
    (A : Type*) [AddCommGroup A] [Module F A]
    (S : Finset (ZMod d)) (hDisj : Disjoint (linkRepFinset p E) S) :
    Submodule.map (antiDiagTensorEquiv F d A).toLinearMap
        (Submodule.map₂ (TensorProduct.mk F (ZMod d → F) (ZMod d → A))
          (partialLeftSubmodule F p E S) ⊤) =
      partialLeftExtensionSubmodule F p E A S := by
  classical
  have hRepNotS : ∀ r ∈ linkRepFinset p E, r ∉ S := Finset.disjoint_left.mp hDisj
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, Submodule.map₂_le]
    intro u hu v _hv c hc a
    have hZ : antiDiagLinear F d A (fromAntiDiagLinear F d A (fun c a => u c • v a)) =
        (fun c a => u c • v a) :=
      (fromAntiDiagLinearEquiv F d A).left_inv _
    change antiDiagLinear F d A (fromAntiDiagLinear F d A (fun c a => u c • v a)) c a =
      antiDiagLinear F d A (fromAntiDiagLinear F d A (fun c a => u c • v a)) (linkRep p E c) a
    rw [hZ]
    dsimp only
    rw [hu c hc]
  · intro X hX
    rw [Submodule.mem_map]
    let Z := antiDiagLinear F d A X
    let Reps := linkRepFinset p E
    let indR (r : ZMod d) : ZMod d → F := fun c =>
      if c ∉ S ∧ linkRep p E c = r then 1 else 0
    let indS (x : ZMod d) : ZMod d → F := fun c =>
      if c = x then 1 else 0
    have hindR_mem : ∀ r : ZMod d, indR r ∈ partialLeftSubmodule F p E S := by
      intro r c hc
      have hrep_notS : linkRep p E c ∉ S := hRepNotS _ (linkRep_mem_linkRepFinset p E c)
      have hidem : linkRep p E (linkRep p E c) = linkRep p E c := linkRep_idem p E c
      simp [indR, hc, hrep_notS, hidem]
    have hindS_mem : ∀ x ∈ S, indS x ∈ partialLeftSubmodule F p E S := by
      intro x hxS c hc
      have hcx : c ≠ x := fun h => hc (h ▸ hxS)
      have hrepx : linkRep p E c ≠ x := fun h =>
        hRepNotS _ (linkRep_mem_linkRepFinset p E c) (h ▸ hxS)
      simp [indS, hcx, hrepx]
    let t : (ZMod d → F) ⊗[F] (ZMod d → A) :=
      (∑ r ∈ Reps, (indR r) ⊗ₜ[F] (Z r)) + (∑ x ∈ S, (indS x) ⊗ₜ[F] (Z x))
    refine ⟨t, ?_, ?_⟩
    · refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.sum_mem _ fun r _ =>
          Submodule.apply_mem_map₂ _ (hindR_mem r) Submodule.mem_top
      · exact Submodule.sum_mem _ fun x hx =>
          Submodule.apply_mem_map₂ _ (hindS_mem x hx) Submodule.mem_top
    · funext c j
      have hX_id : fromAntiDiagLinear F d A Z = X :=
        (fromAntiDiagLinearEquiv F d A).right_inv X
      simp only [t, LinearEquiv.coe_coe, map_add, map_sum, Pi.add_apply, Finset.sum_apply,
        antiDiagTensorEquiv_tmul_apply]
      by_cases hc : c ∈ S
      · have hR0 : (∑ r ∈ Reps, indR r c • Z r (j + c)) = 0 :=
          Finset.sum_eq_zero fun r _ => by simp [indR, hc]
        rw [hR0, zero_add, Finset.sum_eq_single c]
        · simp only [indS, ite_true, one_smul]
          exact congrFun (congrFun hX_id c) j
        · intro x _ hx
          simp [indS, hx.symm]
        · intro hnot
          exact absurd hc hnot
      · have hS0 : (∑ x ∈ S, indS x c • Z x (j + c)) = 0 :=
          Finset.sum_eq_zero fun x hx => by
            have hne : c ≠ x := fun h => hc (h ▸ hx)
            simp [indS, hne]
        rw [hS0, add_zero, Finset.sum_eq_single (linkRep p E c)]
        · have h1 : indR (linkRep p E c) c = 1 := by simp [indR, hc]
          rw [h1, one_smul]
          have hZc : Z (linkRep p E c) (j + c) = Z c (j + c) := (hX c hc (j + c)).symm
          rw [hZc]
          exact congrFun (congrFun hX_id c) j
        · intro r _ hr
          have h0 : indR r c = 0 := by simp [indR, hr.symm]
          rw [h0, zero_smul]
        · intro hnot
          exact absurd (linkRep_mem_linkRepFinset p E c) hnot

private lemma finrank_partialLeftExtensionSubmodule (F : Type*) [Field F] {d : ℕ} [NeZero d]
    {κ : Type*} (p : ZMod d → κ) (E : Finset (ZMod d))
    (A : Type*) [AddCommGroup A] [Module F A] [FiniteDimensional F A]
    (S : Finset (ZMod d)) (hDisj : Disjoint (linkRepFinset p E) S) :
    finrank F (partialLeftExtensionSubmodule F p E A S) =
      ((linkRepFinset p E).card + S.card) * (d * finrank F A) := by
  classical
  let Reps := linkRepFinset p E
  let Idx := Reps ∪ S
  have hRepNotS : ∀ r ∈ Reps, r ∉ S := Finset.disjoint_left.mp hDisj
  let e : partialLeftExtensionSubmodule F p E A S ≃ₗ[F] (Idx → ZMod d → A) :=
    { toFun := fun X r => antiDiagLinear F d A X.1 r.1
      invFun := fun g =>
        ⟨fromAntiDiagLinear F d A (fun c =>
            if hc : c ∈ S then g ⟨c, Finset.mem_union_right _ hc⟩
            else g ⟨linkRep p E c, Finset.mem_union_left _ (linkRep_mem_linkRepFinset p E c)⟩),
         by
           intro c hc a
           have hZ : ∀ Z : State d A, antiDiagLinear F d A (fromAntiDiagLinear F d A Z) = Z :=
             (fromAntiDiagLinearEquiv F d A).left_inv
           rw [hZ]
           have hrep_notS : linkRep p E c ∉ S := hRepNotS _ (linkRep_mem_linkRepFinset p E c)
           have hidem : linkRep p E (linkRep p E c) = linkRep p E c := linkRep_idem p E c
           have hsub :
               (⟨linkRep p E (linkRep p E c),
                 Finset.mem_union_left _ (linkRep_mem_linkRepFinset p E (linkRep p E c))⟩ : Idx) =
               ⟨linkRep p E c,
                 Finset.mem_union_left _ (linkRep_mem_linkRepFinset p E c)⟩ :=
             Subtype.ext hidem
           simp only [hc, hrep_notS, dite_false, hsub]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun X => by
        apply Subtype.ext
        have hX_id : fromAntiDiagLinear F d A (antiDiagLinear F d A X.1) = X.1 :=
          (fromAntiDiagLinearEquiv F d A).right_inv X.1
        have hEqZ : (fun c : ZMod d =>
            if hc : c ∈ S then antiDiagLinear F d A X.1 c
            else antiDiagLinear F d A X.1 (linkRep p E c)) = antiDiagLinear F d A X.1 := by
          funext c a
          by_cases hc : c ∈ S
          · simp [hc]
          · simp [hc, (X.2 c hc a).symm]
        exact (congrArg (fromAntiDiagLinear F d A) hEqZ).trans hX_id
      right_inv := fun g => by
        funext x a
        have hZ : ∀ Z : State d A, antiDiagLinear F d A (fromAntiDiagLinear F d A Z) = Z :=
          (fromAntiDiagLinearEquiv F d A).left_inv
        change (antiDiagLinear F d A (fromAntiDiagLinear F d A _)) x.1 a = g x a
        rw [hZ]
        by_cases hx : x.1 ∈ S
        · simp [hx]
        · have hxR : x.1 ∈ Reps := by
            rcases Finset.mem_union.mp x.2 with h1 | h2
            · exact h1
            · exact absurd h2 hx
          have hidem : linkRep p E x.1 = x.1 := (mem_linkRepFinset_iff p E x.1).mp hxR
          have hsub :
              (⟨linkRep p E x.1,
                Finset.mem_union_left _ (linkRep_mem_linkRepFinset p E x.1)⟩ : Idx) = x :=
            Subtype.ext hidem
          simp only [hx, dite_false, hsub] }
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  have hinner : finrank F (ZMod d → A) = d * finrank F A := by
    rw [Module.finrank_pi_fintype]
    simp [ZMod.card]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, hinner]
  rw [Finset.card_union_of_disjoint hDisj]

/-- **Tensor Decomposition & Dimension Formula for Shift-Set Covariance.**
1. `antiDiagTensorEquiv` maps `U_E(p) ⊗ ⊤` (`Submodule.map₂ (TensorProduct.mk ...) U_E ⊤`) onto
   `shiftSetCovarianceSubmodule F p E A`.
2. `finrank F (shiftSetCovarianceSubmodule F p E A) = finrank F (leftComponentSubmodule F p E) * (d * finrank F A)`. -/
theorem shiftSetCovariance_tensor_finrank (F : Type*) [Field F] {d : ℕ} [NeZero d]
    {κ : Type*} (p : ZMod d → κ) (E : Finset (ZMod d))
    (A : Type*) [AddCommGroup A] [Module F A] [FiniteDimensional F A] :
    Submodule.map (antiDiagTensorEquiv F d A).toLinearMap
        (Submodule.map₂ (TensorProduct.mk F (ZMod d → F) (ZMod d → A))
          (leftComponentSubmodule F p E) ⊤) =
      shiftSetCovarianceSubmodule F p E A ∧
    finrank F (shiftSetCovarianceSubmodule F p E A) =
      finrank F (leftComponentSubmodule F p E) * (d * finrank F A) := by
  classical
  obtain ⟨_, _, _, hCovIff⟩ := antiDiagonalTensorSeparation F d κ A
  constructor
  · apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap, Submodule.map₂_le]
      intro u hu v _hv
      change InShiftSetCovariance p E (antiDiagTensorEquiv F d A (u ⊗ₜ[F] v))
      rw [hCovIff]
      intro c c' a hrel
      have hZ : antiDiagLinear F d A (fromAntiDiagLinear F d A (fun c a => u c • v a)) =
          (fun c a => u c • v a) :=
        (fromAntiDiagLinearEquiv F d A).left_inv _
      change antiDiagLinear F d A (fromAntiDiagLinear F d A (fun c a => u c • v a)) c a =
        antiDiagLinear F d A (fromAntiDiagLinear F d A (fun c a => u c • v a)) c' a
      rw [hZ]
      dsimp only
      rw [hu c c' hrel]
    · intro X hX
      rw [Submodule.mem_map]
      let Z := antiDiagLinear F d A X
      have hZ_const : ∀ c c' a : ZMod d,
          Relation.EqvGen (SwapRigidity.Link p E) c c' → Z c a = Z c' a :=
        (hCovIff p E X).mp hX
      let Reps := linkRepFinset p E
      let ind (r : ZMod d) : ZMod d → F := fun c => if linkRep p E c = r then 1 else 0
      have hind_mem : ∀ r : ZMod d, ind r ∈ leftComponentSubmodule F p E := by
        intro r c c' hrel
        have hEq : linkRep p E c = linkRep p E c' := (linkRep_eq_iff p E c c').mpr hrel
        simp [ind, hEq]
      let t : (ZMod d → F) ⊗[F] (ZMod d → A) := ∑ r ∈ Reps, (ind r) ⊗ₜ[F] (Z r)
      refine ⟨t, ?_, ?_⟩
      · refine Submodule.sum_mem _ fun r _ => ?_
        exact Submodule.apply_mem_map₂ _ (hind_mem r) Submodule.mem_top
      · funext c j
        simp only [t, LinearEquiv.coe_coe, map_sum, Finset.sum_apply,
          antiDiagTensorEquiv_tmul_apply]
        rw [Finset.sum_eq_single (linkRep p E c)]
        · have h1 : ind (linkRep p E c) c = 1 := by simp [ind]
          rw [h1, one_smul]
          have hrel := linkRep_rel p E c
          have hZc := (hZ_const c (linkRep p E c) (j + c) hrel).symm
          rw [hZc]
          have hX_id : fromAntiDiagLinear F d A Z = X :=
            (fromAntiDiagLinearEquiv F d A).right_inv X
          exact congrFun (congrFun hX_id c) j
        · intro r _ hr
          have h0 : ind r c = 0 := ite_eq_right hr.symm
          rw [h0, zero_smul]
        · intro hnot
          exact absurd (linkRep_mem_linkRepFinset p E c) hnot
  · have hEqSub : shiftSetCovarianceSubmodule F p E A =
        partialLeftExtensionSubmodule F p E A ∅ := by
      ext X
      change InShiftSetCovariance p E X ↔ _
      rw [hCovIff]
      constructor
      · intro h c _ a
        exact h c (linkRep p E c) a (linkRep_rel p E c)
      · intro h c c' a hrel
        have hEq : linkRep p E c = linkRep p E c' := (linkRep_eq_iff p E c c').mpr hrel
        calc antiDiagLinear F d A X c a
            = antiDiagLinear F d A X (linkRep p E c) a := h c (Finset.notMem_empty c) a
          _ = antiDiagLinear F d A X (linkRep p E c') a := by rw [hEq]
          _ = antiDiagLinear F d A X c' a := (h c' (Finset.notMem_empty c') a).symm
    rw [hEqSub, finrank_partialLeftExtensionSubmodule F p E A ∅ (Finset.disjoint_empty_right _),
        Finset.card_empty, add_zero, finrank_leftComponentSubmodule]

/-- **Formal Explanation of Grassmann / Mask-Method Floors.**
1. **Grassmann 2-set bound**: For any partition `p : ZMod d → κ`, shift `s : ZMod d`, and subspaces
   `C_0, C_s ≤ State d A` with `finrank F C_0 = finrank F C_s` and
   `C_0 ⊓ C_s ≤ shiftSetCovarianceSubmodule F p {0, s} A`, modularity alone yields
   `2 * finrank F C_0 ≤ d^2 * finrank F A + finrank F (shiftSetCovarianceSubmodule F p {0, s} A)`.
2. **Sharpness once right-factor shift equivariance is dropped**: Conversely, splitting a
   complement of `U_{0, s}` on the left tensor factor into two disjoint halves of size
   `⌊(d - dim U_{0, s}) / 2⌋` produces subspaces `C_0, C_s ≤ State d A` (each of the tensor form
   `V_i ⊗ ⊤` under `antiDiagTensorEquiv`) with `C_0 ⊓ C_s = shiftSetCovarianceSubmodule F p {0, s} A`,
   `finrank F C_0 = finrank F C_s`, and
   `d^2 * finrank F A + finrank F (shiftSetCovarianceSubmodule F p {0, s} A) ≤ 2 * finrank F C_0 + d * finrank F A`.
3. **Explicit 2-class alternating-mask separation (`d = 2 * m`, `m ≥ 2`)**: With
   `p c := decide (c.val % 2 = 1)` on `ZMod (2 * m)` (`2 ≤ m`), every true shared code
   `IsSharedCode F p C` satisfies `2 * finrank F C ≤ ((2 * m)^2 + 2 * (2 * m)) * finrank F A`
   (rate `≤ 1/2 + 1/d`, enforced by shift `s = 2` where `finrank U_{0, 2} = 2`), whereas at shift
   `s = 1`, `p c ≠ p (c + 1)` everywhere so `leftComponentSubmodule F p {0, 1} = ⊤` and
   `shiftSetCovarianceSubmodule F p {0, 1} A = ⊤` (allowing `C_0 = C_1 = ⊤` of full rate `1`). -/
theorem maskFloor_GenericSubspaceRealization :
    (∀ (F : Type*) [Field F] (d : ℕ) [NeZero d] (κ A : Type*)
      [AddCommGroup A] [Module F A] [FiniteDimensional F A]
      (p : ZMod d → κ) (s : ZMod d),
      (∀ C₀ Cₛ : Submodule F (State d A),
        finrank F C₀ = finrank F Cₛ →
        C₀ ⊓ Cₛ ≤ shiftSetCovarianceSubmodule F p {0, s} A →
        2 * finrank F C₀ ≤
          d ^ 2 * finrank F A + finrank F (shiftSetCovarianceSubmodule F p {0, s} A)) ∧
      (∃ (V₀ Vₛ : Submodule F (ZMod d → F)) (C₀ Cₛ : Submodule F (State d A)),
        C₀ = Submodule.map (antiDiagTensorEquiv F d A).toLinearMap
          (Submodule.map₂ (TensorProduct.mk F (ZMod d → F) (ZMod d → A)) V₀ ⊤) ∧
        Cₛ = Submodule.map (antiDiagTensorEquiv F d A).toLinearMap
          (Submodule.map₂ (TensorProduct.mk F (ZMod d → F) (ZMod d → A)) Vₛ ⊤) ∧
        C₀ ⊓ Cₛ = shiftSetCovarianceSubmodule F p {0, s} A ∧
        finrank F C₀ = finrank F Cₛ ∧
        d ^ 2 * finrank F A + finrank F (shiftSetCovarianceSubmodule F p {0, s} A) ≤
          2 * finrank F C₀ + d * finrank F A)) ∧
    (∀ (F : Type*) [Field F] (m : ℕ) (A : Type*)
      [AddCommGroup A] [Module F A] [FiniteDimensional F A],
      2 ≤ m →
      let p : ZMod (2 * m) → Bool := fun c => decide (c.val % 2 = 1)
      (∀ C : Submodule F (State (2 * m) A),
        IsSharedCode F p C →
        2 * finrank F C ≤ ((2 * m) ^ 2 + 2 * (2 * m)) * finrank F A) ∧
      finrank F (leftComponentSubmodule F p {0, 2}) = 2 ∧
      leftComponentSubmodule F p {0, 1} = ⊤ ∧
      shiftSetCovarianceSubmodule F p {0, 1} A = ⊤) := by
  constructor
  · intro F _ d _ κ A _ _ _ p s
    constructor
    · intro C₀ Cₛ hEqRank hInfLe
      have hSupLe : finrank F (C₀ ⊔ Cₛ : Submodule F (State d A)) ≤ d ^ 2 * finrank F A := by
        calc finrank F (C₀ ⊔ Cₛ : Submodule F (State d A))
            ≤ finrank F (State d A) := Submodule.finrank_le _
          _ = d * d * finrank F A := SharedDecoders.finrank_state
          _ = d ^ 2 * finrank F A := by rw [sq]
      have hInfRankLe : finrank F (C₀ ⊓ Cₛ : Submodule F (State d A)) ≤
          finrank F (shiftSetCovarianceSubmodule F p {0, s} A) :=
        Submodule.finrank_mono hInfLe
      calc 2 * finrank F C₀
          = finrank F C₀ + finrank F Cₛ := by omega
        _ = finrank F (C₀ ⊔ Cₛ : Submodule F (State d A)) +
              finrank F (C₀ ⊓ Cₛ : Submodule F (State d A)) :=
            (Submodule.finrank_sup_add_finrank_inf_eq C₀ Cₛ).symm
        _ ≤ d ^ 2 * finrank F A + finrank F (shiftSetCovarianceSubmodule F p {0, s} A) :=
            Nat.add_le_add hSupLe hInfRankLe
    · classical
      let E : Finset (ZMod d) := {0, s}
      let Reps := linkRepFinset p E
      let NonReps : Finset (ZMod d) := Finset.univ \ Reps
      let k := NonReps.card / 2
      let eNR : Fin NonReps.card ≃ NonReps := NonReps.equivFin.symm
      let S₀ : Finset (ZMod d) :=
        (Finset.univ.filter fun i : Fin NonReps.card => i.val < k).image fun i => (eNR i).1
      let S₁ : Finset (ZMod d) :=
        (Finset.univ.filter fun i : Fin NonReps.card => k ≤ i.val ∧ i.val < 2 * k).image
          fun i => (eNR i).1
      have heNR_inj : Function.Injective (fun i : Fin NonReps.card => (eNR i).1) :=
        Subtype.val_injective.comp eNR.injective
      have hS₀_sub : S₀ ⊆ NonReps := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
        exact (eNR i).2
      have hS₁_sub : S₁ ⊆ NonReps := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
        exact (eNR i).2
      have hDisj₀ : Disjoint Reps S₀ :=
        Finset.disjoint_left.mpr fun r hr hx =>
          (Finset.mem_sdiff.mp (hS₀_sub hx)).2 hr
      have hDisj₁ : Disjoint Reps S₁ :=
        Finset.disjoint_left.mpr fun r hr hx =>
          (Finset.mem_sdiff.mp (hS₁_sub hx)).2 hr
      have hDisj₀₁ : Disjoint S₀ S₁ := by
        rw [Finset.disjoint_left]
        intro x hx₀ hx₁
        rcases Finset.mem_image.mp hx₀ with ⟨i₀, hi₀, rfl⟩
        rcases Finset.mem_image.mp hx₁ with ⟨i₁, hi₁, hEq⟩
        have hi_eq : i₀ = i₁ := heNR_inj hEq.symm
        subst hi_eq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₀ hi₁
        omega
      have h2k_le : 2 * k ≤ NonReps.card := Nat.mul_div_le NonReps.card 2
      have hcard₀ : S₀.card = k := by
        rw [Finset.card_image_of_injective _ heNR_inj, Fin.card_filter_val_lt]
        omega
      have hcard₁ : S₁.card = k := by
        rw [Finset.card_image_of_injective _ heNR_inj]
        let f : Fin k → Fin NonReps.card := fun j => ⟨k + j.val, by have := j.isLt; omega⟩
        have hf_inj : Function.Injective f := fun j₁ j₂ h =>
          Fin.ext (by have := congrArg Fin.val h; dsimp [f] at this; omega)
        have hEqFilt : (Finset.univ.filter fun i : Fin NonReps.card => k ≤ i.val ∧ i.val < 2 * k) =
            Finset.univ.image f := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · rintro ⟨hge, hlt⟩
            exact ⟨⟨i.val - k, by omega⟩, Fin.ext (by dsimp [f]; omega)⟩
          · rintro ⟨j, rfl⟩
            dsimp [f]
            have := j.isLt
            omega
        rw [hEqFilt, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
      let V₀ := partialLeftSubmodule F p E S₀
      let Vₛ := partialLeftSubmodule F p E S₁
      let C₀ := partialLeftExtensionSubmodule F p E A S₀
      let Cₛ := partialLeftExtensionSubmodule F p E A S₁
      refine ⟨V₀, Vₛ, C₀, Cₛ,
        (map_partialLeftSubmodule_eq F p E A S₀ hDisj₀).symm,
        (map_partialLeftSubmodule_eq F p E A S₁ hDisj₁).symm,
        ?_, ?_, ?_⟩
      · obtain ⟨_, _, _, hCovIff⟩ := antiDiagonalTensorSeparation F d κ A
        ext X
        simp only [Submodule.mem_inf]
        change (_ ∧ _) ↔ InShiftSetCovariance p E X
        rw [hCovIff]
        constructor
        · rintro ⟨h₀, h₁⟩ c c' a hrel
          have hAll : ∀ x : ZMod d,
              antiDiagLinear F d A X x a = antiDiagLinear F d A X (linkRep p E x) a := by
            intro x
            by_cases hx₀ : x ∈ S₀
            · exact h₁ x (Finset.disjoint_left.mp hDisj₀₁ hx₀) a
            · exact h₀ x hx₀ a
          have hRepEq : linkRep p E c = linkRep p E c' := (linkRep_eq_iff p E c c').mpr hrel
          rw [hAll c, hAll c', hRepEq]
        · intro h
          refine ⟨fun c _ a => h c (linkRep p E c) a (linkRep_rel p E c),
                  fun c _ a => h c (linkRep p E c) a (linkRep_rel p E c)⟩
      · rw [finrank_partialLeftExtensionSubmodule F p E A S₀ hDisj₀,
            finrank_partialLeftExtensionSubmodule F p E A S₁ hDisj₁,
            hcard₀, hcard₁]
      · rw [finrank_partialLeftExtensionSubmodule F p E A S₀ hDisj₀, hcard₀,
            (shiftSetCovariance_tensor_finrank F p E A).2, finrank_leftComponentSubmodule]
        have hCardPart : Reps.card + NonReps.card = d := by
          have hsdiff := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Reps)
          rw [Finset.card_univ, ZMod.card] at hsdiff
          dsimp only [NonReps]
          omega
        have h2k1 : NonReps.card ≤ 2 * k + 1 := by
          dsimp [k]
          omega
        have hLeftIneq : d + Reps.card ≤ 2 * (Reps.card + k) + 1 := by omega
        calc d ^ 2 * finrank F A + Reps.card * (d * finrank F A)
            = (d + Reps.card) * (d * finrank F A) := by ring
          _ ≤ (2 * (Reps.card + k) + 1) * (d * finrank F A) :=
              Nat.mul_le_mul_right _ hLeftIneq
          _ = 2 * ((Reps.card + k) * (d * finrank F A)) + d * finrank F A := by ring
  · intro F _ m A _ _ _ hm
    have : NeZero (2 * m) := ⟨by omega⟩
    let p : ZMod (2 * m) → Bool := fun c => decide (c.val % 2 = 1)
    have h1_val : (1 : ZMod (2 * m)).val = 1 := by
      rw [← Nat.cast_one]
      exact ZMod.val_natCast_of_lt (by omega)
    have h2_val : (2 : ZMod (2 * m)).val = 2 := by
      change ((2 : ℕ) : ZMod (2 * m)).val = 2
      exact ZMod.val_natCast_of_lt (by omega)
    have hp_add_two : ∀ x : ZMod (2 * m), p (x + 2) = p x := by
      intro x
      dsimp only [p]
      have hval : (x + 2).val = (x.val + 2) % (2 * m) := by
        rw [ZMod.val_add, h2_val]
      have hmod2 : ((x.val + 2) % (2 * m)) % 2 = x.val % 2 := by
        have hdvd : 2 ∣ 2 * m := ⟨m, rfl⟩
        rw [Nat.mod_mod_of_dvd _ hdvd]
        omega
      rw [hval, hmod2]
    have hlink_add_two : ∀ x : ZMod (2 * m),
        SwapRigidity.Link p {0, 2} x (x + 2) := fun x =>
      ⟨(hp_add_two x).symm, 2, by simp, 0, by simp, by simp⟩
    have hStep2 : ∀ k : ℕ,
        Relation.EqvGen (SwapRigidity.Link p {0, 2}) ((2 * k : ℕ) : ZMod (2 * m)) 0 ∧
        Relation.EqvGen (SwapRigidity.Link p {0, 2}) ((2 * k + 1 : ℕ) : ZMod (2 * m)) 1 := by
      intro k
      induction k with
      | zero =>
        exact ⟨by simpa using Relation.EqvGen.refl (0 : ZMod (2 * m)),
               by simpa using Relation.EqvGen.refl (1 : ZMod (2 * m))⟩
      | succ k ih =>
        constructor
        · have heq : ((2 * (k + 1) : ℕ) : ZMod (2 * m)) = ((2 * k : ℕ) : ZMod (2 * m)) + 2 := by
            push_cast; ring
          rw [heq]
          exact Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (hlink_add_two _))) ih.1
        · have heq : ((2 * (k + 1) + 1 : ℕ) : ZMod (2 * m)) =
              ((2 * k + 1 : ℕ) : ZMod (2 * m)) + 2 := by
            push_cast; ring
          rw [heq]
          exact Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (hlink_add_two _))) ih.2
    have hConn02 : ∀ c : ZMod (2 * m),
        ∃ s ∈ ({0, 1} : Finset (ZMod (2 * m))),
          Relation.EqvGen (SwapRigidity.Link p {0, 2}) c s := by
      intro c
      rcases Nat.mod_two_eq_zero_or_one c.val with hc0 | hc1
      · have hc_eq : c = ((2 * (c.val / 2) : ℕ) : ZMod (2 * m)) := by
          have hval : 2 * (c.val / 2) = c.val := by omega
          rw [hval, ZMod.natCast_zmod_val]
        rw [hc_eq]
        exact ⟨0, by simp, (hStep2 (c.val / 2)).1⟩
      · have hc_eq : c = ((2 * (c.val / 2) + 1 : ℕ) : ZMod (2 * m)) := by
          have hval : 2 * (c.val / 2) + 1 = c.val := by omega
          rw [hval, ZMod.natCast_zmod_val]
        rw [hc_eq]
        exact ⟨1, by simp, (hStep2 (c.val / 2)).2⟩
    have hEqvImpP : ∀ {E : Finset (ZMod (2 * m))} {c c' : ZMod (2 * m)},
        Relation.EqvGen (SwapRigidity.Link p E) c c' → p c = p c' := by
      intro E c c' hrel
      induction hrel with
      | rel x y hxy => exact hxy.1
      | refl _ => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    have hp_add_one : ∀ c : ZMod (2 * m), p (c + 1) ≠ p c := by
      intro c
      dsimp only [p]
      have hval : (c + 1).val = (c.val + 1) % (2 * m) := by
        rw [ZMod.val_add, h1_val]
      have hmod2 : ((c.val + 1) % (2 * m)) % 2 = (c.val + 1) % 2 := by
        have hdvd : 2 ∣ 2 * m := ⟨m, rfl⟩
        exact Nat.mod_mod_of_dvd _ hdvd
      rw [hval, hmod2]
      rcases Nat.mod_two_eq_zero_or_one c.val with hc0 | hc1
      · have h1 : (c.val + 1) % 2 = 1 := by omega
        simp [hc0, h1]
      · have h0 : (c.val + 1) % 2 = 0 := by omega
        simp [hc1, h0]
    have hLink01_eq : ∀ c c' : ZMod (2 * m),
        Relation.EqvGen (SwapRigidity.Link p {0, 1}) c c' → c = c' := by
      intro c c' hrel
      induction hrel with
      | rel x y hxy =>
        obtain ⟨hp_xy, δ, hδ, δ', hδ', hsum⟩ := hxy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hδ hδ'
        rcases hδ with rfl | rfl <;> rcases hδ' with rfl | rfl
        · simpa using hsum
        · have hx : x = y + 1 := by simpa using hsum
          subst hx
          exact absurd hp_xy (hp_add_one y)
        · have hy : y = x + 1 := by
            calc y = y + 0 := (add_zero y).symm
              _ = x + 1 := hsum.symm
          subst hy
          exact absurd hp_xy.symm (hp_add_one x)
        · exact add_right_cancel hsum
      | refl _ => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro C hC
      have h02_ne : (0 : ZMod (2 * m)) ≠ 2 := by
        intro hEq
        have hv := congrArg ZMod.val hEq
        rw [ZMod.val_zero, h2_val] at hv
        omega
      have hcardΔ : ({0, 2} : Finset (ZMod (2 * m))).card = 2 := Finset.card_pair h02_ne
      have hcardS : ({0, 1} : Finset (ZMod (2 * m))).card ≤ 2 := Finset.card_le_two
      have hTP := hC.finrank_le (Δ := {0, 2}) (Finset.insert_nonempty _ _) hConn02
      rw [hcardΔ] at hTP
      calc 2 * finrank F C
          ≤ (2 - 1) * ((2 * m) * (2 * m) * finrank F A) +
              (2 * m) * ({0, 1} : Finset (ZMod (2 * m))).card * finrank F A := hTP
        _ ≤ 1 * ((2 * m) * (2 * m) * finrank F A) +
              (2 * m) * 2 * finrank F A := by
              refine Nat.add_le_add_left ?_ _
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcardS)
        _ = ((2 * m) ^ 2 + 2 * (2 * m)) * finrank F A := by ring
    · let e2 : leftComponentSubmodule F p {0, 2} ≃ₗ[F] (Fin 2 → F) :=
        { toFun := fun u i => if i = 0 then u.1 0 else u.1 1
          invFun := fun w =>
            ⟨fun c => if p c = false then w 0 else w 1,
             fun c c' hrel => by dsimp only; rw [hEqvImpP hrel]⟩
          map_add' := fun u v => by
            funext i
            by_cases hi : i = 0 <;> simp [hi]
          map_smul' := fun a u => by
            funext i
            by_cases hi : i = 0 <;> simp [hi]
          left_inv := fun u => by
            apply Subtype.ext
            funext c
            rcases Nat.mod_two_eq_zero_or_one c.val with hc0 | hc1
            · have hp0 : p c = false := by simp [p, hc0]
              have hc_eq : c = ((2 * (c.val / 2) : ℕ) : ZMod (2 * m)) := by
                have hval : 2 * (c.val / 2) = c.val := by omega
                rw [hval, ZMod.natCast_zmod_val]
              have hrel0 : Relation.EqvGen (SwapRigidity.Link p {0, 2}) c 0 := by
                rw [hc_eq]; exact (hStep2 (c.val / 2)).1
              simp [hp0, (u.2 c 0 hrel0).symm]
            · have hp1 : p c = true := by simp [p, hc1]
              have hc_eq : c = ((2 * (c.val / 2) + 1 : ℕ) : ZMod (2 * m)) := by
                have hval : 2 * (c.val / 2) + 1 = c.val := by omega
                rw [hval, ZMod.natCast_zmod_val]
              have hrel1 : Relation.EqvGen (SwapRigidity.Link p {0, 2}) c 1 := by
                rw [hc_eq]; exact (hStep2 (c.val / 2)).2
              simp [hp1, (u.2 c 1 hrel1).symm]
          right_inv := fun w => by
            funext i
            have hp0 : p 0 = false := by simp [p]
            have hp1 : p 1 = true := by simp [p, h1_val]
            rcases i with ⟨iv, hiv⟩
            have h01 : iv = 0 ∨ iv = 1 := by omega
            rcases h01 with rfl | rfl <;> simp [hp0, hp1] }
      rw [e2.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    · rw [eq_top_iff]
      intro u _ c c' hrel
      rw [hLink01_eq c c' hrel]
    · obtain ⟨_, _, _, hCovIff⟩ := antiDiagonalTensorSeparation F (2 * m) Bool A
      rw [eq_top_iff]
      intro X _
      change InShiftSetCovariance p {0, 1} X
      rw [hCovIff]
      intro c c' a hrel
      rw [hLink01_eq c c' hrel]

end AntiDiagTensor

/-! ### 2. General `(d, R)` Bounded-OSR Pipeline Pass Lower Bound -/

section BoundedOSRPipeline

/-- Every row-uniform column operator or column-uniform row operator has Operator Schmidt Rank
at most `1`. -/
theorem isRowOrColUniform_rankLe_one {F : Type*} [Semiring F] {d b : ℕ}
    {K : GridState F d b →ₗ[F] GridState F d b}
    (h : IsRowUniformColOp K ∨ IsColUniformRowOp K) :
    HasOperatorSchmidtRankLe K 1 :=
  h.elim isRowUniformColOp_rankLe_one isColUniformRowOp_rankLe_one

private theorem composeGridOps_rank_le_general {F : Type*} [CommSemiring F] {d b R : ℕ}
    (Ks : List (GridState F d b →ₗ[F] GridState F d b))
    (heavyIndices : Finset (Fin Ks.length))
    (hKs : ∀ i : Fin Ks.length,
      if i ∈ heavyIndices then HasOperatorSchmidtRankLe (Ks.get i) R
      else HasOperatorSchmidtRankLe (Ks.get i) 1) :
    HasOperatorSchmidtRankLe (composeGridOps Ks) (R ^ heavyIndices.card) := by
  induction Ks with
  | nil =>
    have hcard : heavyIndices.card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      exact fun i => Fin.elim0 i
    rw [hcard, pow_zero]
    exact isRowUniformColOp_rankLe_one ⟨LinearMap.id, fun _ _ => rfl⟩
  | cons K Ks' ih =>
    let tailIndices : Finset (Fin Ks'.length) :=
      Finset.univ.filter fun j : Fin Ks'.length => j.succ ∈ heavyIndices
    have htail : ∀ j : Fin Ks'.length,
        if j ∈ tailIndices then HasOperatorSchmidtRankLe (Ks'.get j) R
        else HasOperatorSchmidtRankLe (Ks'.get j) 1 := by
      intro j
      have hj := hKs j.succ
      have hmem : (j ∈ tailIndices) ↔ (j.succ ∈ heavyIndices) := by simp [tailIndices]
      by_cases hjs : j.succ ∈ heavyIndices
      · rw [ite_eq_left (hmem.mpr hjs)]
        rw [ite_eq_left hjs] at hj
        exact hj
      · rw [ite_eq_right (mt hmem.mp hjs)]
        rw [ite_eq_right hjs] at hj
        exact hj
    have hTailRank := ih tailIndices htail
    let idx0 : Fin (K :: Ks').length := 0
    have h0 := hKs idx0
    by_cases h0_mem : idx0 ∈ heavyIndices
    · rw [ite_eq_left h0_mem] at h0
      have hcard : heavyIndices.card = tailIndices.card + 1 := by
        have hEq : heavyIndices = insert idx0 (tailIndices.image Fin.succ) := by
          ext i
          refine Fin.cases ?_ ?_ i
          · simp [idx0, h0_mem]
          · intro j; simp [idx0, tailIndices]
        have hnotMem : idx0 ∉ tailIndices.image Fin.succ := by simp [idx0]
        rw [hEq, Finset.card_insert_of_notMem hnotMem,
            Finset.card_image_of_injective _ (Fin.succ_injective _), add_comm]
      rw [hcard, pow_succ]
      exact hasOperatorSchmidtRankLe_comp h0 hTailRank
    · rw [ite_eq_right h0_mem] at h0
      have hcard : heavyIndices.card = tailIndices.card := by
        have hEq : heavyIndices = tailIndices.image Fin.succ := by
          ext i
          refine Fin.cases ?_ ?_ i
          · simp [idx0, h0_mem]
          · intro j; simp [tailIndices]
        rw [hEq, Finset.card_image_of_injective _ (Fin.succ_injective _)]
      have hComp := hasOperatorSchmidtRankLe_comp h0 hTailRank
      rw [mul_one, ← hcard] at hComp
      exact hComp

/-- **General `(d, R)` Bounded-OSR Pipeline Pass Lower Bound.**
Over every field `F`, for all `d, b, R : ℕ` (`1 ≤ d`, `1 ≤ b`, `1 ≤ R`), any pipeline `Ks`
whose stages outside `heavyIndices` have Operator Schmidt Rank `≤ 1` (including all row-uniform
column and column-uniform row passes via `isRowOrColUniform_rankLe_one`) and whose stages in
`heavyIndices` have Operator Schmidt Rank `≤ R`, if `composeGridOps Ks = gridSwapLinear F d b`,
satisfies:
1. `d ^ 2 ≤ R ^ heavyIndices.card`, and
2. if `2 ≤ R`, `2 * Real.log (d : ℝ) / Real.log (R : ℝ) ≤ (heavyIndices.card : ℝ)`. -/
theorem boundedOSRPipelinePassLowerBound (F : Type*) [Field F] {d b R : ℕ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (_hR : 1 ≤ R)
    (Ks : List (GridState F d b →ₗ[F] GridState F d b))
    (heavyIndices : Finset (Fin Ks.length))
    (hKs : ∀ i : Fin Ks.length,
      if i ∈ heavyIndices then HasOperatorSchmidtRankLe (Ks.get i) R
      else HasOperatorSchmidtRankLe (Ks.get i) 1)
    (hSwap : composeGridOps Ks = gridSwapLinear F d b) :
    d ^ 2 ≤ R ^ heavyIndices.card ∧
    (2 ≤ R → 2 * Real.log (d : ℝ) / Real.log (R : ℝ) ≤ (heavyIndices.card : ℝ)) := by
  have hRank := composeGridOps_rank_le_general Ks heavyIndices hKs
  rw [hSwap] at hRank
  have hExact := operatorSchmidtRankSwap F d b hd hb
  have hPowLe : d ^ 2 ≤ R ^ heavyIndices.card := by
    by_contra hlt
    exact hExact.2 (R ^ heavyIndices.card) (Nat.lt_of_not_ge hlt) hRank
  refine ⟨hPowLe, ?_⟩
  intro hR2
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hPowReal : ((d : ℝ) ^ 2) ≤ ((R : ℝ) ^ heavyIndices.card) := by
    exact_mod_cast hPowLe
  have hLogLe : Real.log ((d : ℝ) ^ 2) ≤ Real.log ((R : ℝ) ^ heavyIndices.card) :=
    Real.log_le_log (pow_pos hd_pos 2) hPowReal
  rw [Real.log_pow, Real.log_pow, Nat.cast_two] at hLogLe
  have hR_gt_one : (1 : ℝ) < (R : ℝ) := by exact_mod_cast hR2
  have hLogR_pos : 0 < Real.log (R : ℝ) := Real.log_pos hR_gt_one
  exact (div_le_iff₀ hLogR_pos).mpr hLogLe

private lemma stoneShuffle_iter_coord_bound {m k r c : ℕ} (hk : k ≤ m)
    (hr : r < 2 ^ m) :
    (c % 2 ^ k) * 2 ^ (m - k) + r / 2 ^ k < 2 ^ m := by
  have hpow : 2 ^ k * 2 ^ (m - k) = 2 ^ m := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  have hc_lt : c % 2 ^ k < 2 ^ k := Nat.mod_lt c (Nat.two_pow_pos k)
  have hr_lt : r / 2 ^ k < 2 ^ (m - k) := by
    apply Nat.div_lt_of_lt_mul
    rwa [hpow]
  have h1 : (c % 2 ^ k + 1) * 2 ^ (m - k) ≤ 2 ^ k * 2 ^ (m - k) :=
    Nat.mul_le_mul_right _ hc_lt
  have h2 : (c % 2 ^ k) * 2 ^ (m - k) + r / 2 ^ k < (c % 2 ^ k + 1) * 2 ^ (m - k) := by
    linarith
  linarith

private lemma nat_mod_two_pow_succ_decomp (c k : ℕ) :
    ((c / 2 ^ k) % 2) * 2 ^ k + c % 2 ^ k = c % 2 ^ (k + 1) := by
  let P := 2 ^ k
  let q := c / P
  let rem := c % P
  have hP_pos : 0 < P := Nat.two_pow_pos k
  have hrem_lt : rem < P := Nat.mod_lt c hP_pos
  have hc_eq : c = P * q + rem := (Nat.div_add_mod c P).symm
  have hq_eq : q = 2 * (q / 2) + q % 2 := (Nat.div_add_mod q 2).symm
  have hq_mod : q % 2 < 2 := Nat.mod_lt q (by omega)
  have hlt : (q % 2) * P + rem < P * 2 := by nlinarith
  have hpow : 2 ^ (k + 1) = P * 2 := pow_succ 2 k
  rw [hpow]
  change (q % 2) * P + rem = c % (P * 2)
  have hdecomp : c = (P * 2) * (q / 2) + ((q % 2) * P + rem) := by
    calc c = P * (2 * (q / 2) + q % 2) + rem := by rw [hc_eq, ← hq_eq]
      _ = (P * 2) * (q / 2) + ((q % 2) * P + rem) := by ring
  rw [hdecomp, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

private lemma stoneShuffle_iter_step_coord {n k r c : ℕ} (hk : k ≤ n) :
    let m := n + 1
    let r_k := (c % 2 ^ k) * 2 ^ (m - k) + r / 2 ^ k
    let c_k := (r % 2 ^ k) * 2 ^ (m - k) + c / 2 ^ k
    (c_k % 2) * 2 ^ n + r_k / 2 =
      (c % 2 ^ (k + 1)) * 2 ^ (m - (k + 1)) + r / 2 ^ (k + 1) := by
  intro m r_k c_k
  have hm_sub : m - k = (n - k) + 1 := by omega
  have hm_sub_succ : m - (k + 1) = n - k := by omega
  have hpow_mk : 2 ^ (m - k) = 2 ^ (n - k) * 2 := by rw [hm_sub, pow_succ]
  have hck_mod : c_k % 2 = (c / 2 ^ k) % 2 := by
    dsimp [c_k]
    rw [hpow_mk, ← mul_assoc]
    let A := (r % 2 ^ k) * 2 ^ (n - k)
    let B := c / 2 ^ k
    have hmod2 : (A * 2 + B) % 2 = B % 2 := by omega
    exact hmod2
  have hrk_div : r_k / 2 = (c % 2 ^ k) * 2 ^ (n - k) + r / 2 ^ (k + 1) := by
    dsimp [r_k]
    rw [hpow_mk, ← mul_assoc]
    let A := (c % 2 ^ k) * 2 ^ (n - k)
    let B := r / 2 ^ k
    have hdiv2 : (A * 2 + B) / 2 = A + B / 2 := by omega
    have hdiv_pow : B / 2 = r / 2 ^ (k + 1) := by
      dsimp [B]
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    exact hdiv2.trans (congrArg (A + ·) hdiv_pow)
  have hpow_n : 2 ^ n = 2 ^ k * 2 ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  rw [hck_mod, hrk_div, hm_sub_succ, hpow_n]
  calc ((c / 2 ^ k) % 2) * (2 ^ k * 2 ^ (n - k)) +
        ((c % 2 ^ k) * 2 ^ (n - k) + r / 2 ^ (k + 1))
      = (((c / 2 ^ k) % 2) * 2 ^ k + c % 2 ^ k) * 2 ^ (n - k) + r / 2 ^ (k + 1) := by ring
    _ = (c % 2 ^ (k + 1)) * 2 ^ (n - k) + r / 2 ^ (k + 1) := by
          rw [nat_mod_two_pow_succ_decomp]

/-- **Attainment of the Stone-Shuffle Pass Lower Bound (`S^m = τ`).**
Iterating Stone's 1-bit shuffle `stoneShuffleGridLinear F m b` `m` times (`d = 2^m`, `m ≥ 0`)
realizes the exact matrix transpose `gridSwapLinear F (2^m) b`, showing that `t = m` in
`stoneShufflePipelinePassLowerBound` is attained with zero row/column-uniform passes. -/
theorem stoneShuffleGridLinear_iterate_eq_swap (F : Type*) [Semiring F] (m b : ℕ) :
    composeGridOps (List.replicate m (stoneShuffleGridLinear F m b)) =
      gridSwapLinear F (2 ^ m) b := by
  cases m with
  | zero =>
      apply LinearMap.ext
      intro X
      funext r c ℓ
      have hr : r = ⟨0, by decide⟩ := Fin.ext (by have := r.isLt; omega)
      have hc : c = ⟨0, by decide⟩ := Fin.ext (by have := c.isLt; omega)
      subst hr hc
      rfl
  | succ n =>
      have hiter : ∀ k : ℕ, (hk : k ≤ n + 1) →
          ∀ (X : GridState F (2 ^ (n + 1)) b) (r c : Fin (2 ^ (n + 1))) (ℓ : Fin b),
            composeGridOps (List.replicate k (stoneShuffleGridLinear F (n + 1) b)) X r c ℓ =
              X ⟨(c.val % 2 ^ k) * 2 ^ (n + 1 - k) + r.val / 2 ^ k,
                  stoneShuffle_iter_coord_bound hk r.isLt⟩
                ⟨(r.val % 2 ^ k) * 2 ^ (n + 1 - k) + c.val / 2 ^ k,
                  stoneShuffle_iter_coord_bound hk c.isLt⟩ ℓ := by
        intro k
        induction k with
        | zero =>
            intro hk X r c ℓ
            simp only [List.replicate_zero, composeGridOps, LinearMap.id_apply]
            have hr0 : (⟨(c.val % 2 ^ 0) * 2 ^ (n + 1 - 0) + r.val / 2 ^ 0,
                stoneShuffle_iter_coord_bound hk r.isLt⟩ : Fin (2 ^ (n + 1))) = r := by
              apply Fin.ext; dsimp; rw [Nat.mod_one, zero_mul, zero_add, Nat.div_one]
            have hc0 : (⟨(r.val % 2 ^ 0) * 2 ^ (n + 1 - 0) + c.val / 2 ^ 0,
                stoneShuffle_iter_coord_bound hk c.isLt⟩ : Fin (2 ^ (n + 1))) = c := by
              apply Fin.ext; dsimp; rw [Nat.mod_one, zero_mul, zero_add, Nat.div_one]
            rw [hr0, hc0]
        | succ k ih =>
            intro hk X r c ℓ
            have hk_le_n : k ≤ n := Nat.le_of_succ_le_succ hk
            have hk_le : k ≤ n + 1 := Nat.le_of_lt hk
            simp only [List.replicate_succ, composeGridOps, LinearMap.comp_apply]
            rw [ih hk_le]
            let rk_fin : Fin (2 ^ (n + 1)) :=
              ⟨(c.val % 2 ^ k) * 2 ^ (n + 1 - k) + r.val / 2 ^ k,
                stoneShuffle_iter_coord_bound hk_le r.isLt⟩
            let ck_fin : Fin (2 ^ (n + 1)) :=
              ⟨(r.val % 2 ^ k) * 2 ^ (n + 1 - k) + c.val / 2 ^ k,
                stoneShuffle_iter_coord_bound hk_le c.isLt⟩
            change stoneShuffleGridLinear F (n + 1) b X rk_fin ck_fin ℓ = _
            dsimp [stoneShuffleGridLinear]
            have hbound1 : (ck_fin.val % 2) * 2 ^ n + rk_fin.val / 2 < 2 ^ (n + 1) :=
              stoneShuffle_iter_coord_bound (Nat.succ_le_of_lt (Nat.succ_pos n)) rk_fin.isLt
            have hbound2 : (rk_fin.val % 2) * 2 ^ n + ck_fin.val / 2 < 2 ^ (n + 1) :=
              stoneShuffle_iter_coord_bound (Nat.succ_le_of_lt (Nat.succ_pos n)) ck_fin.isLt
            have hr_eq : (⟨((ck_fin.val % 2) * 2 ^ n + rk_fin.val / 2) % 2 ^ (n + 1),
                Nat.mod_lt _ (Nat.two_pow_pos (n + 1))⟩ : Fin (2 ^ (n + 1))) =
              ⟨(c.val % 2 ^ (k + 1)) * 2 ^ (n + 1 - (k + 1)) + r.val / 2 ^ (k + 1),
                stoneShuffle_iter_coord_bound hk r.isLt⟩ := by
              apply Fin.ext
              dsimp
              rw [Nat.mod_eq_of_lt hbound1]
              exact stoneShuffle_iter_step_coord hk_le_n
            have hc_eq : (⟨((rk_fin.val % 2) * 2 ^ n + ck_fin.val / 2) % 2 ^ (n + 1),
                Nat.mod_lt _ (Nat.two_pow_pos (n + 1))⟩ : Fin (2 ^ (n + 1))) =
              ⟨(r.val % 2 ^ (k + 1)) * 2 ^ (n + 1 - (k + 1)) + c.val / 2 ^ (k + 1),
                stoneShuffle_iter_coord_bound hk c.isLt⟩ := by
              apply Fin.ext
              dsimp
              rw [Nat.mod_eq_of_lt hbound2]
              exact stoneShuffle_iter_step_coord hk_le_n
            rw [hr_eq, hc_eq]
      apply LinearMap.ext
      intro X
      funext r c ℓ
      rw [hiter (n + 1) (le_refl _)]
      dsimp [gridSwapLinear]
      have hr_final : (⟨(c.val % 2 ^ (n + 1)) * 2 ^ (n + 1 - (n + 1)) + r.val / 2 ^ (n + 1),
          stoneShuffle_iter_coord_bound (le_refl _) r.isLt⟩ : Fin (2 ^ (n + 1))) = c := by
        apply Fin.ext
        dsimp
        rw [Nat.mod_eq_of_lt c.isLt, Nat.sub_self, pow_zero, mul_one,
          Nat.div_eq_of_lt r.isLt, add_zero]
      have hc_final : (⟨(r.val % 2 ^ (n + 1)) * 2 ^ (n + 1 - (n + 1)) + c.val / 2 ^ (n + 1),
          stoneShuffle_iter_coord_bound (le_refl _) c.isLt⟩ : Fin (2 ^ (n + 1))) = r := by
        apply Fin.ext
        dsimp
        rw [Nat.mod_eq_of_lt r.isLt, Nat.sub_self, pow_zero, mul_one,
          Nat.div_eq_of_lt c.isLt, add_zero]
      rw [hr_final, hc_final]

end BoundedOSRPipeline

/-! ### 3. Discrete Shannon Mutual Information `= 0` & Row-Diagonal Gauge Invariance -/

section MutualInfoAndRowDiagGauge

/-- Discrete Shannon mutual information (in bits, base `2`) between random variables `f : Ω → α`
and `g : Ω → β` under the uniform distribution on a nonempty finite sample space `Ω`. -/
noncomputable def uniformShannonMI {Ω α β : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (f : Ω → α) (g : Ω → β) : ℝ :=
  ∑ a : α, ∑ b : β,
    let p_ab := ((Finset.univ.filter fun ω => f ω = a ∧ g ω = b).card : ℝ) / (Fintype.card Ω : ℝ)
    let p_a := ((Finset.univ.filter fun ω => f ω = a).card : ℝ) / (Fintype.card Ω : ℝ)
    let p_b := ((Finset.univ.filter fun ω => g ω = b).card : ℝ) / (Fintype.card Ω : ℝ)
    if p_ab = 0 then 0 else p_ab * (Real.log (p_ab / (p_a * p_b)) / Real.log 2)

/-- Exact multiplicative counting independence implies `uniformShannonMI f g = 0`. -/
theorem uniformShannonMI_eq_zero_of_indep {Ω α β : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (f : Ω → α) (g : Ω → β)
    (hindep : ∀ (a : α) (b : β),
      Fintype.card Ω * (Finset.univ.filter fun ω => f ω = a ∧ g ω = b).card =
        (Finset.univ.filter fun ω => f ω = a).card *
          (Finset.univ.filter fun ω => g ω = b).card) :
    uniformShannonMI f g = 0 := by
  unfold uniformShannonMI
  have hN_pos : (0 : ℝ) < (Fintype.card Ω : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hN_ne : (Fintype.card Ω : ℝ) ≠ 0 := ne_of_gt hN_pos
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  set c_ab : ℝ := ((Finset.univ.filter fun ω => f ω = a ∧ g ω = b).card : ℝ)
  set c_a : ℝ := ((Finset.univ.filter fun ω => f ω = a).card : ℝ)
  set c_b : ℝ := ((Finset.univ.filter fun ω => g ω = b).card : ℝ)
  set N : ℝ := (Fintype.card Ω : ℝ)
  have hMul : N * c_ab = c_a * c_b := by
    dsimp only [N, c_ab, c_a, c_b]
    exact_mod_cast hindep a b
  by_cases hp0 : c_ab / N = 0
  · simp [hp0]
  · have hRatio : (c_ab / N) / ((c_a / N) * (c_b / N)) = 1 := by
      have h1 : (c_a / N) * (c_b / N) = (N * c_ab) / (N * N) := by
        rw [div_mul_div_comm, hMul]
      have h2 : (N * c_ab) / (N * N) = c_ab / N :=
        mul_div_mul_left c_ab N hN_ne
      rw [h1, h2, div_self hp0]
    simp [hp0, hRatio]

/-- **Skew One-Time-Pad Zero Shannon Mutual Information.**
For all `d, b : ℕ` (`[NeZero d]`, `1 ≤ b`) and **every** cell `(r, c)` and target column `c'`,
under uniform `X ∈ State d (Fin b → Bool)` the skew-pad cell `W_{r, c} = skewXorPad X r c` and
target column `X_{:, c'}` have exact discrete Shannon mutual information `0`, even though a single
XOR pass `W ⊕ X = swap X` unmasks the full transpose. -/
theorem skewOneTimePad_ShannonMutualInfoZero (d b : ℕ) [NeZero d] (hb : 1 ≤ b) :
    (∀ (X : State d (Fin b → Bool)) (r c : ZMod d) (ℓ : Fin b),
      xor (skewXorPad X r c ℓ) (X r c ℓ) = swap X r c ℓ) ∧
    (∀ r c c' : ZMod d,
      uniformShannonMI
        (fun X : State d (Fin b → Bool) => skewXorPad X r c)
        (fun X : State d (Fin b → Bool) => fun i => X i c') = 0) := by
  obtain ⟨hUnmask, hIndep⟩ := control_SkewOneTimePadInformationTrap d b hb
  exact ⟨hUnmask, fun r c c' => uniformShannonMI_eq_zero_of_indep _ _ (hIndep r c c')⟩

/-- Two-sided gauge invariance of `HasOutputRowSourceArityLe` under `IsRowDiagonalOp`. -/
theorem HasOutputRowSourceArityLe.rowDiag_conj {F : Type*} [Semiring F] {d b R : ℕ}
    {D₀ D₁ K : GridState F d b →ₗ[F] GridState F d b}
    (hD₀ : IsRowDiagonalOp D₀) (hD₁ : IsRowDiagonalOp D₁)
    (hK : HasOutputRowSourceArityLe K R) :
    HasOutputRowSourceArityLe (D₁.comp (K.comp D₀)) R := by
  obtain ⟨B₀, hB₀⟩ := hD₀
  obtain ⟨B₁, hB₁⟩ := hD₁
  obtain ⟨srcRows, hcard, hdep⟩ := hK
  refine ⟨srcRows, hcard, ?_⟩
  intro r X₁ X₂ hEq
  have hD₀_eq : ∀ r' ∈ srcRows r, D₀ X₁ r' = D₀ X₂ r' := by
    intro r' hr'
    rw [hB₀, hB₀, hEq r' hr']
  change D₁ (K (D₀ X₁)) r = D₁ (K (D₀ X₂)) r
  rw [hB₁, hB₁, hdep r (D₀ X₁) (D₀ X₂) hD₀_eq]

/-- **Row-Diagonal Gauge Invariance vs. Operator Schmidt Rank.**
1. Output-row source arity `HasOutputRowSourceArityLe` is invariant under arbitrary two-sided
   row-diagonal gauges `D₁ ∘ K ∘ D₀` (`IsRowDiagonalOp D₀`, `IsRowDiagonalOp D₁`).
2. By contrast, `HasOperatorSchmidtRankLe` is *not* row-diagonal gauge-invariant: `LinearMap.id`
   has `rk_⊗ ≤ 1`, whereas left-multiplying by the row-diagonal operator `rowShearLinear F d b`
   (`(rowShearLinear F d b).comp LinearMap.id = rowShearLinear F d b`) produces exact Operator
   Schmidt Rank `d`. -/
theorem rowDiagonal_SourceArityGaugeInvariance :
    (∀ (F : Type*) [Semiring F] (d b R : ℕ)
      (D₀ D₁ K : GridState F d b →ₗ[F] GridState F d b),
      IsRowDiagonalOp D₀ →
      IsRowDiagonalOp D₁ →
      HasOutputRowSourceArityLe K R →
      HasOutputRowSourceArityLe (D₁.comp (K.comp D₀)) R) ∧
    (∀ (F : Type*) [Field F] (d b : ℕ) [NeZero d], 1 ≤ b →
      HasOperatorSchmidtRankLe (LinearMap.id : GridState F d b →ₗ[F] GridState F d b) 1 ∧
      IsRowDiagonalOp (rowShearLinear F d b) ∧
      (rowShearLinear F d b).comp LinearMap.id = rowShearLinear F d b ∧
      HasExactOperatorSchmidtRank (rowShearLinear F d b) d) := by
  constructor
  · intro F _ d b R D₀ D₁ K hD₀ hD₁ hK
    exact hK.rowDiag_conj hD₀ hD₁
  · intro F _ d b _ hb
    obtain ⟨hDiag, hExact⟩ := control_RowShearAndRowDiagonalAlternation.{_, 0}.1 F d b hb
    exact ⟨isRowUniformColOp_rankLe_one ⟨LinearMap.id, fun _ _ => rfl⟩,
           hDiag, LinearMap.comp_id _, hExact⟩

end MutualInfoAndRowDiagGauge

/-! ### 4. Unified Three-Term Swap-Code Examples (`Remark 5.6` of Paper 17) -/

section Bonus1Unified

/-- **Unified Three-Term Swap-Code Corollary (`Remark 5.6` of Paper 17).**
1. Explicit padded strict inequalities `7 * (7 + 1) / 2 < 29` (`d = 7`) and
   `4 * (4 + 1) / 2 < 11` (`d = 4`).
2. Over **every** field `F` and **every** `d ∈ {3, 4, 6, 7, 9, 12}`, there exist `3`-term
   factor families `A, B : Fin 3 → Matrix (Fin d) (Fin d) F` whose swap code strictly exceeds the
   symmetric pairing value `d * (d + 1) / 2`. -/
theorem bonus1_UnifiedThreeTermExceedsPairingBound :
    (7 * (7 + 1) / 2 < 29 ∧ 4 * (4 + 1) / 2 < 11) ∧
    (∀ (F : Type*) [Field F], ∀ d ∈ ({3, 4, 6, 7, 9, 12} : Finset ℕ),
      ∃ A B : Fin 3 → Matrix (Fin d) (Fin d) F,
        d * (d + 1) / 2 < finrank F (SwapRigidity.swapCode A B)) := by
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro F _ d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨threeTermBlockA F 1, threeTermBlockB F 1, ?_⟩
    rw [(bonus1_ThreeTermBlockSwapCodeDim.1 F 1).2]
    omega
  · refine ⟨threeTermPaddedA F 1 4, threeTermPaddedB F 1 4, ?_⟩
    rw [(bonus1_ThreeTermPaddedSevenAndFive F).2.1]
    omega
  · refine ⟨threeTermBlockA F 2, threeTermBlockB F 2, ?_⟩
    rw [(bonus1_ThreeTermBlockSwapCodeDim.1 F 2).2]
    omega
  · refine ⟨threeTermPaddedA F 2 7, threeTermPaddedB F 2 7, ?_⟩
    rw [(bonus1_ThreeTermPaddedSevenAndFive F).1]
    omega
  · refine ⟨threeTermBlockA F 3, threeTermBlockB F 3, ?_⟩
    rw [(bonus1_ThreeTermBlockSwapCodeDim.1 F 3).2]
    omega
  · refine ⟨threeTermBlockA F 4, threeTermBlockB F 4, ?_⟩
    rw [(bonus1_ThreeTermBlockSwapCodeDim.1 F 4).2]
    omega

end Bonus1Unified

/-! ### 5. Bonus 2 Asymptotic `1/2 d^2 + o(d^2)` Consequences & Walsh Dichotomy -/

section Bonus2ConsequencesAndWalsh

private lemma le_two_pow_self (m : ℕ) : m ≤ 2 ^ m :=
  Nat.lt_two_pow_self.le

/-- **Asymptotic `1/2 d^2 + o(d^2)` Consequences of `bonus2_MultiscaleIntervalBothSides`.**
1. **Uniform `(ε, δ)` sublinear-profile bound**: For every `ε > 0`, there exist `δ > 0` and
   `M₀ : ℕ` (depending only on `ε`) such that over every field `F`, `m ≥ M₀`, and finite index
   type `α`, whenever `A, B` lie in the multi-scale cyclic-interval-rotation spans with profiles
   `M_A, M_B` satisfying `min (∑ j, M_A j) (∑ j, M_B j) ≤ δ * 2^m`,
   `(finrank F (SwapRigidity.swapCode A B) : ℝ) ≤ (1 / 2 + ε) * (2^m)^2`.
2. **`o(d^2)` sequence bound (`Filter.Tendsto`)**: Along any sequence of multi-scale
   cyclic-interval families whose smaller total interval count satisfies
   `min (∑ j, M_A m j) (∑ j, M_B m j) / 2^m → 0` as `m → ∞`, for every `ε > 0`, eventually
   `(finrank (F m) (SwapRigidity.swapCode (A m) (B m)) : ℝ) ≤ (1 / 2 + ε) * (2^m)^2`. -/
theorem bonus2_SublinearProfileAndTendstoHalf.{u, v} :
    (∀ ε : ℝ, 0 < ε →
      ∃ (δ : ℝ) (M₀ : ℕ), 0 < δ ∧
        ∀ (F : Type u) [Field F] (m : ℕ) (α : Type v) [Fintype α]
          (M_A M_B : Fin m → ℕ)
          (A B : α → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F),
          M₀ ≤ m →
          InMultiscaleIntervalRotSpan M_A A →
          InMultiscaleIntervalRotSpan M_B B →
          ((min (∑ j : Fin m, M_A j) (∑ j : Fin m, M_B j) : ℕ) : ℝ) ≤
            δ * ((2 ^ m : ℕ) : ℝ) →
          (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤
            (1 / 2 + ε) * (((2 ^ m : ℕ) : ℝ) ^ 2)) ∧
    (∀ (F : ℕ → Type u) [∀ m, Field (F m)]
      (α : ℕ → Type v) [∀ m, Fintype (α m)]
      (M_A M_B : ∀ m : ℕ, Fin m → ℕ)
      (A B : ∀ m : ℕ, α m → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) (F m)),
      (∀ m, InMultiscaleIntervalRotSpan (M_A m) (A m)) →
      (∀ m, InMultiscaleIntervalRotSpan (M_B m) (B m)) →
      Filter.Tendsto
        (fun m : ℕ =>
          ((min (∑ j : Fin m, M_A m j) (∑ j : Fin m, M_B m j) : ℕ) : ℝ) /
            ((2 ^ m : ℕ) : ℝ))
        Filter.atTop (nhds 0) →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ m in Filter.atTop,
          (finrank (F m) (SwapRigidity.swapCode (A m) (B m)) : ℝ) ≤
            (1 / 2 + ε) * (((2 ^ m : ℕ) : ℝ) ^ 2)) := by
  have hEpsDelta :
      ∀ ε : ℝ, 0 < ε →
        ∃ (δ : ℝ) (M₀ : ℕ), 0 < δ ∧
          ∀ (F : Type u) [Field F] (m : ℕ) (α : Type v) [Fintype α]
            (M_A M_B : Fin m → ℕ)
            (A B : α → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F),
            M₀ ≤ m →
            InMultiscaleIntervalRotSpan M_A A →
            InMultiscaleIntervalRotSpan M_B B →
            ((min (∑ j : Fin m, M_A j) (∑ j : Fin m, M_B j) : ℕ) : ℝ) ≤
              δ * ((2 ^ m : ℕ) : ℝ) →
            (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤
              (1 / 2 + ε) * (((2 ^ m : ℕ) : ℝ) ^ 2) := by
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
    refine ⟨ε / 2, K, half_pos hε, ?_⟩
    intro F _ m α _ M_A M_B A B hm hA hB hSub
    have hNat := (bonus2_MultiscaleIntervalBothSides F m α M_A M_B A B).2 hA hB
    set S_nat : ℕ := min (∑ j : Fin m, M_A j) (∑ j : Fin m, M_B j)
    have hMinMax :
        min (max 1 (2 * ∑ j : Fin m, M_A j)) (max 1 (2 * ∑ j : Fin m, M_B j)) ≤
          1 + 2 * S_nat := by
      dsimp only [S_nat]
      omega
    have hNat' : 2 * finrank F (SwapRigidity.swapCode A B) ≤
        (2 ^ m) ^ 2 + (2 ^ m) * (1 + 2 * S_nat) :=
      le_trans hNat (Nat.add_le_add_left (Nat.mul_le_mul_left _ hMinMax) _)
    set d_r : ℝ := ((2 ^ m : ℕ) : ℝ)
    set S_r : ℝ := (S_nat : ℝ)
    have hReal : 2 * (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤
        d_r ^ 2 + d_r * (1 + 2 * S_r) := by
      dsimp only [d_r, S_r]
      exact_mod_cast hNat'
    have hd_nonneg : 0 ≤ d_r := Nat.cast_nonneg _
    have hK_le_d : (K : ℝ) ≤ d_r := by
      have hKm : K ≤ 2 ^ m := le_trans hm (le_two_pow_self m)
      dsimp only [d_r]
      exact_mod_cast hKm
    have hOne_le_eps_d : 1 ≤ ε * d_r := by
      have h1 : 1 < ε * (K : ℝ) := by
        have hmul := mul_lt_mul_of_pos_left hK hε
        have hdiv : ε * (1 / ε) = 1 := mul_one_div_cancel (ne_of_gt hε)
        linarith
      have h2 : ε * (K : ℝ) ≤ ε * d_r := mul_le_mul_of_nonneg_left hK_le_d (le_of_lt hε)
      linarith
    have hd_le_eps_sq : d_r ≤ ε * d_r ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hOne_le_eps_d hd_nonneg
      nlinarith
    have hS_le_eps_sq : 2 * d_r * S_r ≤ ε * d_r ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hSub hd_nonneg
      nlinarith
    nlinarith
  refine ⟨hEpsDelta, ?_⟩
  intro F _ α _ M_A M_B A B hA hB hTendsto ε hε
  obtain ⟨δ, M₀, hδ, hBound⟩ := hEpsDelta ε hε
  have hEvLt : ∀ᶠ m in Filter.atTop,
      ((min (∑ j : Fin m, M_A m j) (∑ j : Fin m, M_B m j) : ℕ) : ℝ) /
        ((2 ^ m : ℕ) : ℝ) < δ :=
    hTendsto.eventually (Iio_mem_nhds hδ)
  filter_upwards [Filter.eventually_ge_atTop M₀, hEvLt] with m hm hlt
  have hd_pos : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast Nat.two_pow_pos m
  have hSub : ((min (∑ j : Fin m, M_A m j) (∑ j : Fin m, M_B m j) : ℕ) : ℝ) ≤
      δ * ((2 ^ m : ℕ) : ℝ) :=
    le_of_lt ((div_lt_iff₀ hd_pos).mp hlt)
  exact hBound (F m) m (α m) (M_A m) (M_B m) (A m) (B m) hm (hA m) (hB m) hSub

/-- Explicit quantitative form of `bonus2_SublinearProfileAndTendstoHalf.1` with
`M₀ = ⌊1 / ε⌋₊ + 1` and `δ = ε / 2`. -/
theorem bonus2_SublinearProfileExplicitThreshold.{u, v}
    (ε : ℝ) (hε : 0 < ε)
    (F : Type u) [Field F] (m : ℕ) (α : Type v) [Fintype α]
    (M_A M_B : Fin m → ℕ)
    (A B : α → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F)
    (hm : ⌊1 / ε⌋₊ + 1 ≤ m)
    (hA : InMultiscaleIntervalRotSpan M_A A)
    (hB : InMultiscaleIntervalRotSpan M_B B)
    (hSub : ((min (∑ j : Fin m, M_A j) (∑ j : Fin m, M_B j) : ℕ) : ℝ) ≤
      (ε / 2) * ((2 ^ m : ℕ) : ℝ)) :
    (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤
      (1 / 2 + ε) * (((2 ^ m : ℕ) : ℝ) ^ 2) := by
  set K : ℕ := ⌊1 / ε⌋₊ + 1
  have hK : 1 / ε < (K : ℝ) := by
    dsimp only [K]
    push_cast
    exact Nat.lt_floor_add_one (1 / ε)
  have hNat := (bonus2_MultiscaleIntervalBothSides F m α M_A M_B A B).2 hA hB
  set S_nat : ℕ := min (∑ j : Fin m, M_A j) (∑ j : Fin m, M_B j)
  have hMinMax :
      min (max 1 (2 * ∑ j : Fin m, M_A j)) (max 1 (2 * ∑ j : Fin m, M_B j)) ≤
        1 + 2 * S_nat := by
    dsimp only [S_nat]
    omega
  have hNat' : 2 * finrank F (SwapRigidity.swapCode A B) ≤
      (2 ^ m) ^ 2 + (2 ^ m) * (1 + 2 * S_nat) :=
    le_trans hNat (Nat.add_le_add_left (Nat.mul_le_mul_left _ hMinMax) _)
  set d_r : ℝ := ((2 ^ m : ℕ) : ℝ)
  set S_r : ℝ := (S_nat : ℝ)
  have hReal : 2 * (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤
      d_r ^ 2 + d_r * (1 + 2 * S_r) := by
    dsimp only [d_r, S_r]
    exact_mod_cast hNat'
  have hd_nonneg : 0 ≤ d_r := Nat.cast_nonneg _
  have hK_le_d : (K : ℝ) ≤ d_r := by
    have hKm : K ≤ 2 ^ m := le_trans hm (le_two_pow_self m)
    dsimp only [d_r]
    exact_mod_cast hKm
  have hOne_le_eps_d : 1 ≤ ε * d_r := by
    have h1 : 1 < ε * (K : ℝ) := by
      have hmul := mul_lt_mul_of_pos_left hK hε
      have hdiv : ε * (1 / ε) = 1 := mul_one_div_cancel (ne_of_gt hε)
      linarith
    have h2 : ε * (K : ℝ) ≤ ε * d_r := mul_le_mul_of_nonneg_left hK_le_d (le_of_lt hε)
    linarith
  have hd_le_eps_sq : d_r ≤ ε * d_r ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hOne_le_eps_d hd_nonneg
    nlinarith
  have hS_le_eps_sq : 2 * d_r * S_r ≤ ε * d_r ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hSub hd_nonneg
    nlinarith
  nlinarith

/-- Support `Finset` of the `1`-bit of scale `j : Fin m` in the periodic Rademacher/Walsh dyadic
digit decomposition on `Fin (2^m)`. -/
def walshBitSet (m : ℕ) (j : Fin m) : Finset (Fin (2 ^ m)) :=
  Finset.univ.filter (fun r => (r.val / (2 ^ (m - 1 - j.val))) % 2 = 1)

/-- Number of cyclic `r → (r + 1) mod d` membership transitions of `S : Finset (Fin d)`. -/
def cyclicBoundaryCount {d : ℕ} [NeZero d] (S : Finset (Fin d)) : ℕ :=
  (Finset.univ.filter fun r : Fin d =>
    decide (r ∈ S) ≠ decide (⟨(r.val + 1) % d, Nat.mod_lt _ (NeZero.pos d)⟩ ∈ S)).card

/-- **Walsh Dichotomy Property 1 — Exact `2^(j + 1)` Cyclic Boundaries.**
For every `m : ℕ` and scale `j : Fin m`, `walshBitSet m j` has **exact** cyclic boundary count
`2 ^ (j.val + 1)` (hence at least `4` boundaries at every scale `j` with `1 ≤ j.val`, in contrast
to `≤ 2` for every cyclic interval). -/
theorem walshBitSet_cyclicBoundaryCount (m : ℕ) (j : Fin m) :
    letI : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
    cyclicBoundaryCount (walshBitSet m j) = 2 ^ (j.val + 1) ∧
    (1 ≤ j.val → 4 ≤ cyclicBoundaryCount (walshBitSet m j)) := by
  have : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
  let B := 2 ^ (m - 1 - j.val)
  let K := 2 ^ (j.val + 1)
  have hB_pos : 0 < B := Nat.two_pow_pos _
  have hKB : K * B = 2 ^ m := by
    dsimp only [K, B]
    rw [← pow_add]
    congr 1
    have := j.isLt
    omega
  have hTransIff : ∀ r : Fin (2 ^ m),
      (decide (r ∈ walshBitSet m j) ≠
        decide (⟨(r.val + 1) % (2 ^ m), Nat.mod_lt _ (NeZero.pos (2 ^ m))⟩ ∈ walshBitSet m j)) ↔
      (r.val / B) % 2 ≠ (((r.val + 1) % (2 ^ m)) / B) % 2 := by
    intro r
    simp only [walshBitSet, Finset.mem_filter, Finset.mem_univ, true_and]
    change decide ((r.val / B) % 2 = 1) ≠ decide ((((r.val + 1) % (2 ^ m)) / B) % 2 = 1) ↔ _
    rcases Nat.mod_two_eq_zero_or_one (r.val / B) with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one (((r.val + 1) % (2 ^ m)) / B) with h2 | h2 <;>
      simp [h1, h2]
  let endPt : Fin K → Fin (2 ^ m) := fun k =>
    ⟨k.val * B + (B - 1), by
      have hk1 : k.val + 1 ≤ K := k.isLt
      have hmul : (k.val + 1) * B ≤ K * B := Nat.mul_le_mul_right B hk1
      calc k.val * B + (B - 1)
          < k.val * B + B := by omega
        _ = (k.val + 1) * B := by ring
        _ ≤ 2 ^ m := by rwa [hKB] at hmul⟩
  have hendPt_inj : Function.Injective endPt := by
    intro k₁ k₂ hEq
    have hv : k₁.val * B + (B - 1) = k₂.val * B + (B - 1) := congrArg Fin.val hEq
    have hmul : k₁.val * B = k₂.val * B := by omega
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hB_pos hmul)
  have hFiltEq :
      (Finset.univ.filter fun r : Fin (2 ^ m) =>
        decide (r ∈ walshBitSet m j) ≠
          decide (⟨(r.val + 1) % (2 ^ m), Nat.mod_lt _ (NeZero.pos (2 ^ m))⟩ ∈ walshBitSet m j)) =
      Finset.univ.image endPt := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hTransIff, Finset.mem_image]
    constructor
    · intro hne
      set k_nat := r.val / B
      set rem := r.val % B
      have hk_lt : k_nat < K := Nat.div_lt_of_lt_mul
        (by rw [mul_comm, hKB]; exact r.isLt)
      have hrem_lt : rem < B := Nat.mod_lt r.val hB_pos
      have hr_decomp : r.val = k_nat * B + rem := (Nat.div_add_mod' r.val B).symm
      by_cases hrem_eq : rem = B - 1
      · refine ⟨⟨k_nat, hk_lt⟩, Fin.ext ?_⟩
        dsimp only [endPt]
        omega
      · exfalso
        have hrem1_lt : rem + 1 < B := by omega
        have hr1_lt : r.val + 1 < 2 ^ m := by
          have hk1 : k_nat + 1 ≤ K := hk_lt
          have hmul : (k_nat + 1) * B ≤ K * B := Nat.mul_le_mul_right B hk1
          calc r.val + 1
              = k_nat * B + (rem + 1) := by omega
            _ < k_nat * B + B := by omega
            _ = (k_nat + 1) * B := by ring
            _ ≤ 2 ^ m := by rwa [hKB] at hmul
        have hdiv_eq : ((r.val + 1) % (2 ^ m)) / B = k_nat := by
          rw [Nat.mod_eq_of_lt hr1_lt]
          have e : r.val + 1 = (rem + 1) + k_nat * B := by omega
          rw [e, Nat.add_mul_div_right _ _ hB_pos, Nat.div_eq_of_lt hrem1_lt, zero_add]
        exact hne (by rw [hdiv_eq])
    · rintro ⟨k, rfl⟩
      have hr_div : (endPt k).val / B = k.val := by
        show (k.val * B + (B - 1)) / B = k.val
        have e : k.val * B + (B - 1) = (B - 1) + k.val * B := by ring
        rw [e, Nat.add_mul_div_right _ _ hB_pos, Nat.div_eq_of_lt (by omega : B - 1 < B), zero_add]
      have hr1_eq : (endPt k).val + 1 = (k.val + 1) * B := by
        show k.val * B + (B - 1) + 1 = (k.val + 1) * B
        have e : k.val * B + B = (k.val + 1) * B := by ring
        omega
      rw [hr_div, hr1_eq]
      by_cases hk1_lt : k.val + 1 < K
      · have hmul_lt : (k.val + 1) * B < 2 ^ m := by
          rw [← hKB]
          exact Nat.mul_lt_mul_of_pos_right hk1_lt hB_pos
        rw [Nat.mod_eq_of_lt hmul_lt, Nat.mul_div_left _ hB_pos]
        omega
      · have hk1_eq : k.val + 1 = K := by have := k.isLt; omega
        rw [hk1_eq, hKB, Nat.mod_self, Nat.zero_div]
        have hK_even : K = 2 * 2 ^ j.val := by
          dsimp only [K]
          rw [pow_succ']
        have hj_pos : 0 < 2 ^ j.val := Nat.two_pow_pos j.val
        omega
  have hCard : cyclicBoundaryCount (walshBitSet m j) = 2 ^ (j.val + 1) := by
    unfold cyclicBoundaryCount
    rw [hFiltEq, Finset.card_image_of_injective _ hendPt_inj, Finset.card_univ, Fintype.card_fin]
  refine ⟨hCard, fun hj1 => ?_⟩
  rw [hCard]
  calc 4 = 2 ^ 2 := rfl
    _ ≤ 2 ^ (j.val + 1) := Nat.pow_le_pow_right (by omega) (by omega)

private def finAddMod {d : ℕ} [NeZero d] (sh : ℕ) (r : Fin d) : Fin d :=
  ⟨(r.val + sh) % d, Nat.mod_lt _ (NeZero.pos d)⟩

private lemma add_sub_mod_eq_mul {d : ℕ} (hd : 0 < d) (sh : ℕ) :
    sh + (d - sh % d) = d * (sh / d + 1) := by
  have hlt : sh % d < d := Nat.mod_lt sh hd
  have hdiv : d * (sh / d) + sh % d = sh := Nat.div_add_mod sh d
  have h1 : d * (sh / d) + sh % d + (d - sh % d) = d * (sh / d) + d := by omega
  calc sh + (d - sh % d)
      = d * (sh / d) + sh % d + (d - sh % d) := by rw [hdiv]
    _ = d * (sh / d) + d := h1
    _ = d * (sh / d + 1) := by ring

private lemma finAddMod_cancel {d : ℕ} [NeZero d] (sh : ℕ) (r : Fin d) :
    finAddMod (d - sh % d) (finAddMod sh r) = r := by
  have hd : 0 < d := NeZero.pos d
  apply Fin.ext
  dsimp only [finAddMod]
  rw [Nat.mod_add_mod]
  have hsum : r.val + sh + (d - sh % d) = r.val + d * (sh / d + 1) := by
    rw [add_assoc, add_sub_mod_eq_mul hd sh]
  rw [hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]

private lemma finAddMod_injective {d : ℕ} [NeZero d] (sh : ℕ) :
    Function.Injective (finAddMod (d := d) sh) :=
  Function.LeftInverse.injective (finAddMod_cancel sh)

private lemma finAddMod_comm_one {d : ℕ} [NeZero d] (sh : ℕ) (r : Fin d) :
    finAddMod 1 (finAddMod sh r) = finAddMod sh (finAddMod 1 r) := by
  apply Fin.ext
  dsimp only [finAddMod]
  rw [Nat.mod_add_mod, Nat.mod_add_mod]
  congr 1
  omega

private lemma cyclicBoundaryCount_preimage_add {d : ℕ} [NeZero d] (sh : ℕ)
    (T : Finset (Fin d)) :
    cyclicBoundaryCount (Finset.univ.filter fun r : Fin d => finAddMod sh r ∈ T) =
      cyclicBoundaryCount T := by
  unfold cyclicBoundaryCount
  set S := Finset.univ.filter fun r : Fin d => finAddMod sh r ∈ T
  have hImg :
      (Finset.univ.filter fun r : Fin d =>
        decide (r ∈ S) ≠ decide (finAddMod 1 r ∈ S)).image (finAddMod sh) =
      Finset.univ.filter fun u : Fin d =>
        decide (u ∈ T) ≠ decide (finAddMod 1 u ∈ T) := by
    ext u
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨r, hne, rfl⟩
      have h1 : decide (r ∈ S) = decide (finAddMod sh r ∈ T) := by simp [S]
      have h2 : decide (finAddMod 1 r ∈ S) = decide (finAddMod 1 (finAddMod sh r) ∈ T) := by
        simp [S, finAddMod_comm_one]
      rwa [h1, h2] at hne
    · intro hne
      let r := finAddMod (d - sh % d) u
      have hru : finAddMod sh r = u := by
        dsimp only [r]
        have hd : 0 < d := NeZero.pos d
        apply Fin.ext
        dsimp only [finAddMod]
        rw [Nat.mod_add_mod]
        have hsum : u.val + (d - sh % d) + sh = u.val + d * (sh / d + 1) := by
          calc u.val + (d - sh % d) + sh
              = u.val + (sh + (d - sh % d)) := by ring
            _ = u.val + d * (sh / d + 1) := by rw [add_sub_mod_eq_mul hd sh]
        rw [hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt u.isLt]
      refine ⟨r, ?_, hru⟩
      have h1 : decide (r ∈ S) = decide (u ∈ T) := by simp [S, hru]
      have h2 : decide (finAddMod 1 r ∈ S) = decide (finAddMod 1 u ∈ T) := by
        simp [S, ← finAddMod_comm_one, hru]
      rwa [h1, h2]
  have hEq := congrArg Finset.card hImg
  rw [Finset.card_image_of_injective _ (finAddMod_injective sh)] at hEq
  exact hEq

private lemma cyclicBoundaryCount_sdiff_univ {d : ℕ} [NeZero d] (T : Finset (Fin d)) :
    cyclicBoundaryCount (Finset.univ \ T) = cyclicBoundaryCount T := by
  unfold cyclicBoundaryCount
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  by_cases h1 : r ∈ T <;>
    by_cases h2 : (⟨(r.val + 1) % d, Nat.mod_lt _ (NeZero.pos d)⟩ : Fin d) ∈ T <;>
    simp [h1, h2]

/-- Every cyclic interval `I : Finset (Fin d)` has at most `2` cyclic boundaries. -/
theorem isCyclicInterval_cyclicBoundaryCount_le_two {d len : ℕ} [NeZero d]
    (I : Finset (Fin d)) (hInt : IsCyclicInterval len I) :
    cyclicBoundaryCount I ≤ 2 := by
  have hd : 0 < d := NeZero.pos d
  obtain ⟨start, rfl⟩ := hInt
  by_cases hlen0 : len = 0
  · subst hlen0
    have hEmpty : (Finset.range 0).image
        (fun u => (⟨(start.val + u) % d, Nat.mod_lt _ hd⟩ : Fin d)) = ∅ := by simp
    rw [hEmpty]
    unfold cyclicBoundaryCount
    simp
  · by_cases hlen_ge : d ≤ len
    · have hUniv : (Finset.range len).image
          (fun u => (⟨(start.val + u) % d, Nat.mod_lt _ hd⟩ : Fin d)) = Finset.univ := by
        ext r
        simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, iff_true]
        let u := (r.val + (d - start.val)) % d
        have hu_lt : u < len := lt_of_lt_of_le (Nat.mod_lt _ hd) hlen_ge
        refine ⟨u, hu_lt, Fin.ext ?_⟩
        dsimp only [u]
        rw [Nat.add_mod_mod]
        have hsum : start.val + (r.val + (d - start.val)) = r.val + d := by
          have := start.isLt; omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt r.isLt]
      rw [hUniv]
      unfold cyclicBoundaryCount
      simp
    · have hlen_lt : len < d := Nat.lt_of_not_ge hlen_ge
      have hlen_pos : 0 < len := Nat.pos_of_ne_zero hlen0
      let T : Finset (Fin d) := Finset.univ.filter fun u : Fin d => u.val < len
      have hEqPre :
          (Finset.range len).image
            (fun u => (⟨(start.val + u) % d, Nat.mod_lt _ hd⟩ : Fin d)) =
          Finset.univ.filter (fun r : Fin d => finAddMod (d - start.val) r ∈ T) := by
        ext r
        simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter, Finset.mem_univ,
          true_and, T, finAddMod]
        constructor
        · rintro ⟨u, hu, hEq⟩
          have hr : r.val = (start.val + u) % d := (congrArg Fin.val hEq).symm
          rw [hr, Nat.mod_add_mod]
          have hsum : start.val + u + (d - start.val) = u + d := by
            have := start.isLt; omega
          rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (lt_trans hu hlen_lt)]
          exact hu
        · intro hlt
          refine ⟨(r.val + (d - start.val)) % d, hlt, Fin.ext ?_⟩
          dsimp only
          rw [Nat.add_mod_mod]
          have hsum : start.val + (r.val + (d - start.val)) = r.val + d := by
            have := start.isLt; omega
          rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt r.isLt]
      rw [hEqPre, cyclicBoundaryCount_preimage_add]
      unfold cyclicBoundaryCount
      let p₁ : Fin d := ⟨len - 1, by omega⟩
      let p₂ : Fin d := ⟨d - 1, by omega⟩
      have hSub :
          (Finset.univ.filter fun u : Fin d =>
            decide (u ∈ T) ≠ decide (⟨(u.val + 1) % d, Nat.mod_lt _ hd⟩ ∈ T)) ⊆ {p₁, p₂} := by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, T] at hu
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases hu_lt : u.val < len
        · by_cases hu_end : u.val = len - 1
          · left; exact Fin.ext hu_end
          · exfalso
            have hu1_lt_len : u.val + 1 < len := by omega
            have hu1_lt_d : u.val + 1 < d := by omega
            rw [Nat.mod_eq_of_lt hu1_lt_d] at hu
            simp [hu_lt, hu1_lt_len] at hu
        · by_cases hu_end : u.val = d - 1
          · right; exact Fin.ext hu_end
          · exfalso
            have hu1_lt_d : u.val + 1 < d := by have := u.isLt; omega
            have hu1_not_lt : ¬ (u.val + 1 < len) := by omega
            rw [Nat.mod_eq_of_lt hu1_lt_d] at hu
            simp [hu_lt, hu1_not_lt] at hu
      exact le_trans (Finset.card_le_card hSub) Finset.card_le_two

/-- Every periodic scale-`j` dyadic mask `S` (`IsPeriodicScaleDyadicMask j S`) has **exact** cyclic
boundary count `2 ^ (j.val + 1)`. -/
theorem isPeriodicScaleDyadicMask_cyclicBoundaryCount {m : ℕ} (j : Fin m)
    (S : Finset (Fin (2 ^ m))) (hMask : IsPeriodicScaleDyadicMask j S) :
    letI : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
    cyclicBoundaryCount S = 2 ^ (j.val + 1) := by
  have : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
  obtain ⟨phase, hS⟩ := hMask
  let P := 2 ^ (m - j.val)
  let B := 2 ^ (m - 1 - j.val)
  have hP_eq : P = 2 * B := by
    dsimp only [P, B]
    have hsub : m - j.val = (m - 1 - j.val) + 1 := by have := j.isLt; omega
    rw [hsub, pow_succ']
  have hP_dvd : P ∣ 2 ^ m := by
    dsimp only [P]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hB_pos : 0 < B := Nat.two_pow_pos _
  have hS_eq :
      S = Finset.univ.filter
        (fun r : Fin (2 ^ m) => finAddMod phase.val r ∈ Finset.univ \ walshBitSet m j) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, walshBitSet,
      finAddMod]
    rw [hS r]
    change (r.val + phase.val) % P < B ↔
      ¬ ((((r.val + phase.val) % (2 ^ m)) / B) % 2 = 1)
    set x := (r.val + phase.val) % (2 ^ m)
    have hx_modP : x % P = (r.val + phase.val) % P := Nat.mod_mod_of_dvd _ hP_dvd
    rw [← hx_modP]
    have hx_decomp : x = (x % P) + B * (2 * (x / P)) := by
      have hdiv : P * (x / P) + x % P = x := Nat.div_add_mod x P
      calc x = P * (x / P) + x % P := hdiv.symm
        _ = (2 * B) * (x / P) + x % P := by
            congr 2
        _ = (x % P) + B * (2 * (x / P)) := by ring
    have hx_divB : x / B = (x % P) / B + 2 * (x / P) := by
      conv_lhs => rw [hx_decomp]
      exact Nat.add_mul_div_left (x % P) (2 * (x / P)) hB_pos
    have hx_mod2 : (x / B) % 2 = ((x % P) / B) % 2 := by
      rw [hx_divB, Nat.add_mul_mod_self_left]
    rw [hx_mod2]
    have hrem_lt : x % P < 2 * B := by
      rw [← hP_eq]
      exact Nat.mod_lt x (by omega)
    by_cases hlt : x % P < B
    · have h0 : (x % P) / B = 0 := Nat.div_eq_of_lt hlt
      simp [hlt, h0]
    · have hge : B ≤ x % P := Nat.le_of_not_lt hlt
      have h1 : (x % P) / B = 1 := by
        have hsub_lt : (x % P - B) < B := by omega
        have he : x % P = (x % P - B) + B * 1 := by omega
        rw [he, Nat.add_mul_div_left _ _ hB_pos, Nat.div_eq_of_lt hsub_lt, zero_add]
      simp [hlt, h1]
  rw [hS_eq, cyclicBoundaryCount_preimage_add, cyclicBoundaryCount_sdiff_univ,
      (walshBitSet_cyclicBoundaryCount m j).1]

/-- **Walsh Dichotomy Property 2 — Singleton Joint Class Refinement.**
Across all `m` Walsh bit scales `j : Fin m`, the joint class map separates all `2^m` row indices
into `2^m` singleton atoms (making one-sided class-uniform bounds vacuous). -/
theorem walshBitSet_joint_separates_points (m : ℕ) :
    (∀ r₁ r₂ : Fin (2 ^ m),
      (∀ j : Fin m, (r₁ ∈ walshBitSet m j ↔ r₂ ∈ walshBitSet m j)) ↔ r₁ = r₂) ∧
    (Finset.univ.image (fun r : Fin (2 ^ m) =>
      fun j : Fin m => decide (r ∈ walshBitSet m j))).card = 2 ^ m := by
  have hSep : ∀ r₁ r₂ : Fin (2 ^ m),
      (∀ j : Fin m, (r₁ ∈ walshBitSet m j ↔ r₂ ∈ walshBitSet m j)) ↔ r₁ = r₂ := by
    intro r₁ r₂
    constructor
    · intro hiff
      have hstep : ∀ t : ℕ, t ≤ m → r₁.val / (2 ^ (m - t)) = r₂.val / (2 ^ (m - t)) := by
        intro t
        induction t with
        | zero =>
          intro _
          simp [Nat.div_eq_of_lt r₁.isLt, Nat.div_eq_of_lt r₂.isLt]
        | succ t ih =>
          intro ht
          have hprev := ih (by omega)
          let k := m - 1 - t
          have hsub1 : m - t = k + 1 := by omega
          have hsub2 : m - (t + 1) = k := by omega
          rw [hsub1, pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at hprev
          have hj := hiff ⟨t, ht⟩
          simp only [walshBitSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          change (r₁.val / (2 ^ k)) % 2 = 1 ↔ (r₂.val / (2 ^ k)) % 2 = 1 at hj
          rw [hsub2]
          omega
      have hall := hstep m le_rfl
      simp only [Nat.sub_self, pow_zero, Nat.div_one] at hall
      exact Fin.ext hall
    · rintro rfl
      exact fun _ => Iff.rfl
  refine ⟨hSep, ?_⟩
  have hinj : Function.Injective
      (fun r : Fin (2 ^ m) => fun j : Fin m => decide (r ∈ walshBitSet m j)) := by
    intro r₁ r₂ hEq
    refine (hSep r₁ r₂).mp fun j => ?_
    have hj := congrFun hEq j
    simpa using hj
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- **Walsh Dichotomy Property 3 — Per-Side Operator Span Dimension `≤ (m + 1) * 2^m`.**
Over every field `F` and `m : ℕ`, the entire `m`-scale Walsh digit-rotation span has dimension at
most `(m + 1) * 2^m` (`≪ 4^m`), since `P_{j, false} σ^s + P_{j, true} σ^s = σ^s`. -/
theorem walshDigitMaskRotSpan_finrank_le (F : Type*) [Field F] (m : ℕ) :
    finrank F (Submodule.span F
      {X : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F |
        ∃ (j : Fin m) (bit : Bool) (sh : Fin (2 ^ m)),
          X = walshDigitMaskRotMatrix F j bit sh}) ≤ (m + 1) * 2 ^ m := by
  have : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
  have hSumEq : ∀ (j : Fin m) (sh : Fin (2 ^ m)),
      walshDigitMaskRotMatrix F j false sh + walshDigitMaskRotMatrix F j true sh =
        intervalMaskRotMatrix F Finset.univ sh := by
    intro j sh
    ext r c
    simp only [walshDigitMaskRotMatrix, intervalMaskRotMatrix, Matrix.add_apply,
      Matrix.of_apply, Finset.mem_univ, true_and]
    cases ((r.val / (2 ^ (m - 1 - j.val))) % 2 == 1) <;>
      by_cases hc : c.val = (r.val + sh.val) % (2 ^ m) <;>
      simp [hc]
  let Idx := Fin (2 ^ m) ⊕ (Fin m × Fin (2 ^ m))
  let gen : Idx → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F
    | Sum.inl sh => intervalMaskRotMatrix F Finset.univ sh
    | Sum.inr p => walshDigitMaskRotMatrix F p.1 true p.2
  let Φ : (Idx → F) →ₗ[F] Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F :=
    { toFun := fun w => ∑ i : Idx, w i • gen i
      map_add' := fun u v => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a u => by simp [Finset.smul_sum, smul_smul] }
  have hGenMem : ∀ i : Idx, gen i ∈ LinearMap.range Φ := by
    intro i₀
    classical
    refine ⟨Pi.single (M := fun _ : Idx => F) i₀ 1, ?_⟩
    change (∑ i : Idx, Pi.single (M := fun _ : Idx => F) i₀ 1 i • gen i) = gen i₀
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro i _ hi
      simp [Pi.single_eq_of_ne hi]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  have hSpanLe :
      Submodule.span F
        {X : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F |
          ∃ (j : Fin m) (bit : Bool) (sh : Fin (2 ^ m)),
            X = walshDigitMaskRotMatrix F j bit sh} ≤
      LinearMap.range Φ := by
    rw [Submodule.span_le]
    rintro X ⟨j, bit, sh, rfl⟩
    cases bit
    · have hSub : walshDigitMaskRotMatrix F j false sh =
          gen (Sum.inl sh) - gen (Sum.inr (j, sh)) :=
        eq_sub_of_add_eq (hSumEq j sh)
      rw [hSub]
      exact Submodule.sub_mem _ (hGenMem (Sum.inl sh)) (hGenMem (Sum.inr (j, sh)))
    · exact hGenMem (Sum.inr (j, sh))
  have hRangeLe : finrank F (LinearMap.range Φ) ≤ (m + 1) * 2 ^ m := by
    have hRk := LinearMap.finrank_range_add_finrank_ker Φ
    rw [Module.finrank_fintype_fun_eq_card] at hRk
    have hCard : Fintype.card Idx = (m + 1) * 2 ^ m := by
      dsimp only [Idx]
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      ring
    rw [hCard] at hRk
    omega
  exact le_trans (Submodule.finrank_mono hSpanLe) hRangeLe

/-- **Combined Walsh Dichotomy Structural Package.**
Bundles exact `2^(j + 1)` cyclic boundaries (`walshBitSet_cyclicBoundaryCount`), singleton joint
refinement (`walshBitSet_joint_separates_points`), and per-side dimension `≤ (m + 1) * 2^m`
(`walshDigitMaskRotSpan_finrank_le`). -/
theorem bonus2_WalshDichotomyStructuralProperties :
    (∀ (m : ℕ) (j : Fin m),
      letI : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
      cyclicBoundaryCount (walshBitSet m j) = 2 ^ (j.val + 1) ∧
      (1 ≤ j.val → 4 ≤ cyclicBoundaryCount (walshBitSet m j))) ∧
    (∀ m : ℕ,
      (∀ r₁ r₂ : Fin (2 ^ m),
        (∀ j : Fin m, (r₁ ∈ walshBitSet m j ↔ r₂ ∈ walshBitSet m j)) ↔ r₁ = r₂) ∧
      (Finset.univ.image (fun r : Fin (2 ^ m) =>
        fun j : Fin m => decide (r ∈ walshBitSet m j))).card = 2 ^ m) ∧
    (∀ (F : Type*) [Field F] (m : ℕ),
      finrank F (Submodule.span F
        {X : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F |
          ∃ (j : Fin m) (bit : Bool) (sh : Fin (2 ^ m)),
            X = walshDigitMaskRotMatrix F j bit sh}) ≤ (m + 1) * 2 ^ m) :=
  ⟨walshBitSet_cyclicBoundaryCount,
   walshBitSet_joint_separates_points,
   walshDigitMaskRotSpan_finrank_le⟩

end Bonus2ConsequencesAndWalsh

end BoundedArityDecoders

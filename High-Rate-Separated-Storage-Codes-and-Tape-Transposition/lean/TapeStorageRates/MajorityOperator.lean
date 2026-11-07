import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ext

/-! # The signed-corner majority operator

The finite operator is defined on an n-ary tensor product. Its fixed-vector
lemma does not assume that the original operator is diagonalizable or that
its fixed subspace has an invariant complement.
-/

namespace TapeStorageRates.Majority

open Finset Module PiTensorProduct
open scoped BigOperators TensorProduct

set_option autoImplicit false
noncomputable section

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {m : ℕ}

/-- Boolean signs are interpreted in the field only after taking a majority. -/
def sign (b : Bool) : K := if b then 1 else -1

@[simp] theorem sign_false : sign (K := K) false = -1 := rfl
@[simp] theorem sign_true : sign (K := K) true = 1 := rfl

@[simp] theorem sign_not (b : Bool) : sign (K := K) (!b) = -sign (K := K) b := by
  cases b <;> simp

/-- The number of positive signs, as a natural number. -/
def positiveCount (σ : Fin m → Bool) : ℕ := (univ.filter fun i => σ i = true).card

/-- Ties are assigned the negative sign; all uses of oddness will be explicit. -/
def majoritySign (σ : Fin m → Bool) : K :=
  if m < 2 * positiveCount σ then 1 else -1

theorem positiveCount_add_not (σ : Fin m → Bool) :
    positiveCount σ + positiveCount (fun i => !σ i) = m := by
  simpa [positiveCount] using
    (card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) (fun i => σ i = true))

/-- For an odd number of factors, negating all signs negates their majority. -/
theorem majoritySign_not (hm : Odd m) (σ : Fin m → Bool) :
    majoritySign (K := K) (fun i => !σ i) = -majoritySign (K := K) σ := by
  have hc := positiveCount_add_not σ
  obtain ⟨k, hk⟩ := hm
  by_cases h : m < 2 * positiveCount σ
  · have hn : ¬m < 2 * positiveCount (fun i => !σ i) := by omega
    simp [majoritySign, h, hn]
  · have hn : m < 2 * positiveCount (fun i => !σ i) := by omega
    simp [majoritySign, h, hn]

/-- A tensor corner map, with one choice of `id+A` or `id-A` at every factor. -/
def corner (A : Module.End K W) (σ : Fin m → Bool) :
    Module.End K (⨂[K] _ : Fin m, W) :=
  PiTensorProduct.map fun i => LinearMap.id + sign (K := K) (σ i) • A

/-- The normalized signed sum of all tensor corner maps. -/
def operator (A : Module.End K W) (m : ℕ) : Module.End K (⨂[K] _ : Fin m, W) :=
  ((2 : K) ^ m)⁻¹ • ∑ σ : Fin m → Bool, majoritySign (K := K) σ • corner A σ

@[simp] theorem corner_tprod (A : Module.End K W) (σ : Fin m → Bool) (x : Fin m → W) :
    corner A σ (tprod K x) = tprod K (fun i => x i + sign (K := K) (σ i) • A (x i)) := by
  simp [corner]

/-- Summing the unsigned corners gives exactly `2^m` times the identity. -/
theorem sum_corner (A : Module.End K W) :
    (∑ σ : Fin m → Bool, corner A σ) = (2 : K) ^ m • LinearMap.id := by
  let f := PiTensorProduct.mapMultilinear K (fun _ : Fin m => W) (fun _ : Fin m => W)
  have h := f.map_sum (fun (_ : Fin m) (b : Bool) => LinearMap.id + sign (K := K) b • A)
  have hsum : (fun _ : Fin m => ∑ b : Bool, (LinearMap.id + sign (K := K) b • A)) =
      fun _ : Fin m => (2 : K) • (LinearMap.id : Module.End K W) := by
    funext i
    ext x
    simp [sign, two_smul, add_assoc, add_left_comm, add_comm]
  rw [hsum] at h
  change PiTensorProduct.map (fun _ : Fin m => (2 : K) • (LinearMap.id : Module.End K W)) =
      ∑ σ : Fin m → Bool, corner A σ at h
  rw [← h]
  ext x
  simp [MultilinearMap.map_smul_univ]

/-- A negative-majority sign pattern has a negative sign in every strict
majority of the coordinates. -/
theorem exists_negative_of_majority {S : Finset (Fin m)}
    (hS : m < 2 * S.card) {σ : Fin m → Bool} (hσ : ¬m < 2 * positiveCount σ) :
    ∃ i ∈ S, σ i = false := by
  by_contra! h
  have hsub : S ⊆ univ.filter (fun i => σ i = true) := by
    intro i hi
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    cases he : σ i <;> simp_all
  have hc := card_le_card hsub
  unfold positiveCount at hσ
  omega

/-- A negative-majority corner kills a tensor having a strict majority
of factors fixed by the original operator. -/
theorem corner_tprod_eq_zero_of_majority (A : Module.End K W) (x : Fin m → W)
    {S : Finset (Fin m)} (hS : m < 2 * S.card) (hfix : ∀ i ∈ S, A (x i) = x i)
    {σ : Fin m → Bool} (hσ : ¬m < 2 * positiveCount σ) :
    corner A σ (tprod K x) = 0 := by
  obtain ⟨i, hi, hneg⟩ := exists_negative_of_majority hS hσ
  rw [corner_tprod]
  apply (PiTensorProduct.tprod K).map_coord_zero i
  simp [hneg, hfix i hi]

/-- The majority operator fixes every pure tensor with a strict majority
of fixed factors. Oddness of the number of factors is unnecessary here. -/
theorem operator_tprod_eq_self_of_majority (A : Module.End K W) (h2 : (2 : K) ≠ 0)
    (x : Fin m → W) {S : Finset (Fin m)} (hS : m < 2 * S.card)
    (hfix : ∀ i ∈ S, A (x i) = x i) :
    operator A m (tprod K x) = tprod K x := by
  have hsum : (∑ σ : Fin m → Bool, majoritySign (K := K) σ • corner A σ) (tprod K x) =
      (∑ σ : Fin m → Bool, corner A σ) (tprod K x) := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    apply sum_congr rfl
    intro σ _
    by_cases hσ : m < 2 * positiveCount σ
    · simp [majoritySign, hσ]
    · simp [corner_tprod_eq_zero_of_majority A x hS hfix hσ]
  simp only [operator, LinearMap.smul_apply, hsum, sum_corner, LinearMap.id_apply]
  simp [smul_smul, pow_ne_zero m h2]

section Basis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Tensor basis indices using a strict majority of indices in `P`. -/
def goodIndices (P : Finset ι) (m : ℕ) : Finset (Fin m → ι) :=
  univ.filter fun p => m < 2 * (univ.filter fun i => p i ∈ P).card

/-- A finite independent family in the actual kernel: no invariant
complement, spectral decomposition, or pre-assumed dimension bound. -/
theorem goodIndices_card_le_finrank_ker (A : Module.End K W) (h2 : (2 : K) ≠ 0)
    (b : Basis ι K W) (P : Finset ι) (hfix : ∀ j ∈ P, A (b j) = b j) (m : ℕ) :
    (goodIndices P m).card ≤ finrank K (LinearMap.ker (LinearMap.id - operator A m)) := by
  have : Module.Finite K W := Module.Finite.of_basis b
  let bt := Basis.piTensorProduct (fun _ : Fin m => b)
  have : Module.Finite K (⨂[K] _ : Fin m, W) := Module.Finite.of_basis bt
  have hli := bt.linearIndependent.comp
    (fun p : goodIndices P m => p.val) Subtype.val_injective
  have hmem (p : goodIndices P m) : bt p.val ∈
      LinearMap.ker (LinearMap.id - operator A m) := by
    have hmaj : m < 2 * (univ.filter fun i => p.val i ∈ P).card :=
      (mem_filter.mp p.property).2
    have hfixed := operator_tprod_eq_self_of_majority A h2
      (fun i => b (p.val i)) hmaj (fun i hi => hfix _ (mem_filter.mp hi).2)
    simpa [bt, LinearMap.mem_ker, Basis.piTensorProduct_apply] using sub_eq_zero.mpr hfixed.symm
  let Z : Submodule K (⨂[K] _ : Fin m, W) := LinearMap.ker (LinearMap.id - operator A m)
  let v : goodIndices P m → Z := fun p => ⟨bt p.val, hmem p⟩
  have hliZ : LinearIndependent K v := LinearIndependent.of_comp Z.subtype hli
  simpa only [Fintype.card_coe] using hliZ.fintype_card_le_finrank

end Basis

/-- The left summand of a sum of two finite basis-index types. -/
def leftIndices (k l : ℕ) : Finset (Fin k ⊕ Fin l) :=
  univ.map ⟨Sum.inl, Sum.inl_injective⟩

@[simp] theorem leftIndices_card (k l : ℕ) : (leftIndices k l).card = k := by
  simp [leftIndices]

/-- Every fixed subspace supplies the required majority-good basis family.
The complementary space is arbitrary and need not be invariant under `A`. -/
theorem subspace_goodIndices_card_le_finrank_ker [Module.Finite K W]
    (A : Module.End K W) (h2 : (2 : K) ≠ 0) (U : Submodule K W)
    (hfix : ∀ x ∈ U, A x = x) (m : ℕ) :
    (goodIndices (leftIndices (finrank K U) (finrank K W - finrank K U)) m).card ≤
      finrank K (LinearMap.ker (LinearMap.id - operator A m)) := by
  classical
  obtain ⟨Z, hUZ⟩ := U.exists_isCompl
  have hdim := Submodule.finrank_add_eq_of_isCompl hUZ
  have hZ : finrank K Z = finrank K W - finrank K U := by omega
  let bU := Module.finBasis K U
  let bZ := Module.finBasisOfFinrankEq K Z hZ
  let b := (bU.prod bZ).map (U.prodEquivOfIsCompl Z hUZ)
  apply goodIndices_card_le_finrank_ker A h2 b
  intro j hj
  obtain ⟨i, _, rfl⟩ := mem_map.mp hj
  simpa [b, Basis.prod_apply] using hfix (bU i) (bU i).property

/-- An explicit ambient dimension avoids transporting dependent finite
basis-index types when this bound is used in coordinate spaces. -/
theorem subspace_goodIndices_card_le_finrank_ker_of_dimension [Module.Finite K W]
    (A : Module.End K W) (h2 : (2 : K) ≠ 0) (U : Submodule K W)
    (hfix : ∀ x ∈ U, A x = x) (n : ℕ) (hn : finrank K W = n) (m : ℕ) :
    (goodIndices (leftIndices (finrank K U) (n - finrank K U)) m).card ≤
      finrank K (LinearMap.ker (LinearMap.id - operator A m)) := by
  subst n
  exact subspace_goodIndices_card_le_finrank_ker A h2 U hfix m

end
end TapeStorageRates.Majority

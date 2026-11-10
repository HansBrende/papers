import SwapRigidity.Flag
import SwapRigidity.Pigeonhole
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Twist classes

Let `A B : α → Matrix (Fin n) (Fin n) F` and let `G` be any `n × n` matrix. Suppose the terms fall
into classes `c : α → κ` and there are pairwise commuting matrices `G' k` with
`G * (B a)ᵀ = (B a)ᵀ * G' (c a)` for every term `a`. Then, with `s` the number of classes,

  `(s + 1) * dim (swapCode A B) ≤ s * n ^ 2 + ∑ k, dim {P | Gᵀ * P = P * G' k}`.

The proof is a pigeonhole: the part `𝒳'` of the code that stays in the code after right
multiplication by `G, G ^ 2, …, G ^ s` has dimension at least `(s + 1) * D - s * n ^ 2`, and the
transposes of its elements are killed by the product of the commuting operators
`P ↦ Gᵀ * P - P * G' k`.

## Main results

* `SwapRigidity.twistSpace`: the space `{P | Gᵀ * P = P * G'}`.
* `SwapRigidity.twistCode`: the part of the swap code stable under `X ↦ X * G ^ t`, `t ≤ s`.
* `SwapRigidity.succ_mul_finrank_swapCode_le`: the pigeonhole count for `twistCode`.
* `SwapRigidity.finrank_le_sum_finrank_twistSpace`: the elimination of the classes one at a time.
* `SwapRigidity.succ_mul_finrank_swapCode_le_of_twist_classes`: the general bound.
* `SwapRigidity.two_mul_finrank_swapCode_le_of_twist`: the case of one twist class.
-/

namespace SwapRigidity

open Matrix Module

variable {F : Type*} [Field F] {n : ℕ} {α : Type*} [Fintype α]

/-! ### A dimension count in a finite-dimensional space

The counts `finrank_le_finrank_comap` and `finrank_add_finrank_le_add_finrank_inf` used below are in
`SwapRigidity.Pigeonhole`. -/

section General

variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- A subspace is no larger than its image under a linear map plus the kernel of the map. -/
theorem finrank_le_finrank_map_add_finrank_ker {W : Type*} [AddCommGroup W] [Module F W]
    (φ : V →ₗ[F] W) (S : Submodule F V) :
    finrank F S ≤ finrank F (S.map φ) + finrank F (LinearMap.ker φ) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (φ.domRestrict S)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h1
  have h2 : finrank F ((LinearMap.ker φ).comap S.subtype) ≤ finrank F (LinearMap.ker φ) := by
    rw [← Submodule.finrank_map_subtype_eq S, Submodule.map_comap_subtype]
    exact Submodule.finrank_mono inf_le_right
  omega

end General

/-! ### The twist space and the stable part of the code -/

/-- The *twist space* of `G` and `G'`: the matrices `P` with `Gᵀ * P = P * G'`, defined as the
kernel of `P ↦ Gᵀ * P - P * G'`. -/
def twistSpace (G G' : Matrix (Fin n) (Fin n) F) : Submodule F (Matrix (Fin n) (Fin n) F) :=
  LinearMap.ker (LinearMap.mulLeft F Gᵀ - LinearMap.mulRight F G')

/-- Membership in the twist space is the intertwining equation. -/
@[simp]
theorem mem_twistSpace {G G' P : Matrix (Fin n) (Fin n) F} :
    P ∈ twistSpace G G' ↔ Gᵀ * P = P * G' := by
  rw [twistSpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, sub_eq_zero]

/-- The part of the swap code of `A`, `B` that stays in the code after right multiplication by
`G ^ t` for every `t ≤ s`. -/
def twistCode (A B : α → Matrix (Fin n) (Fin n) F) (G : Matrix (Fin n) (Fin n) F) :
    ℕ → Submodule F (Matrix (Fin n) (Fin n) F)
  | 0 => swapCode A B
  | s + 1 => twistCode A B G s ⊓ (swapCode A B).comap (LinearMap.mulRight F (G ^ (s + 1)))

/-- Membership in `twistCode`: all of `X, X * G, …, X * G ^ s` are solutions. -/
theorem mem_twistCode {A B : α → Matrix (Fin n) (Fin n) F} {G : Matrix (Fin n) (Fin n) F}
    {s : ℕ} {X : Matrix (Fin n) (Fin n) F} :
    X ∈ twistCode A B G s ↔ ∀ t ≤ s, X * G ^ t ∈ swapCode A B := by
  induction s with
  | zero =>
    rw [twistCode]
    constructor
    · intro h t ht
      obtain rfl := Nat.le_zero.mp ht
      rwa [pow_zero, Matrix.mul_one]
    · intro h
      have := h 0 le_rfl
      rwa [pow_zero, Matrix.mul_one] at this
  | succ s ih =>
    rw [twistCode, Submodule.mem_inf, ih, Submodule.mem_comap, LinearMap.mulRight_apply]
    constructor
    · rintro ⟨h1, h2⟩ t ht
      rcases Nat.lt_or_ge t (s + 1) with h | h
      · exact h1 t (by omega)
      · obtain rfl : t = s + 1 := by omega
        exact h2
    · intro h
      exact ⟨fun t ht => h t (by omega), h (s + 1) le_rfl⟩

/-- **Pigeonhole count.** A code of dimension `D` in a space of dimension `n ^ 2` meets its `s`
preimages under `X ↦ X * G ^ t`, `t = 1, …, s`, in dimension at least `(s + 1) * D - s * n ^ 2`. -/
theorem succ_mul_finrank_swapCode_le (A B : α → Matrix (Fin n) (Fin n) F)
    (G : Matrix (Fin n) (Fin n) F) (s : ℕ) :
    (s + 1) * finrank F (swapCode A B) ≤ s * n ^ 2 + finrank F (twistCode A B G s) := by
  induction s with
  | zero => rw [twistCode, zero_mul, zero_add, zero_add, one_mul]
  | succ s ih =>
    have h1 := finrank_le_finrank_comap (swapCode A B) (LinearMap.mulRight F (G ^ (s + 1)))
    have h2 := finrank_add_finrank_le_add_finrank_inf (twistCode A B G s)
      ((swapCode A B).comap (LinearMap.mulRight F (G ^ (s + 1))))
    have h3 : finrank F (Matrix (Fin n) (Fin n) F) = n ^ 2 := by
      rw [finrank_matrix, Fintype.card_fin, finrank_self, mul_one, sq]
    rw [h3] at h2
    rw [twistCode]
    linarith

/-! ### Eliminating the classes one at a time -/

/-- **Elimination of twist classes.** Let `G' k`, `k ∈ S`, be pairwise commuting and let `𝒴` be a
space of matrices `P` such that for some matrices `T k` (depending on `P`) the moment equations
`Gᵀ ^ t * P = ∑ k ∈ S, T k * G' k ^ t` hold for all `t ≤ #S`. Then
`dim 𝒴 ≤ ∑ k ∈ S, dim (twistSpace G (G' k))`.

This is the statement that `𝒴` lies in the kernel of the product of the commuting operators
`P ↦ Gᵀ * P - P * G' k`, and that this kernel has dimension at most the sum of the dimensions of
the kernels of the factors. It is proved by applying the factors one at a time. -/
theorem finrank_le_sum_finrank_twistSpace {κ : Type*} [DecidableEq κ]
    (G : Matrix (Fin n) (Fin n) F) (G' : κ → Matrix (Fin n) (Fin n) F)
    (hcomm : ∀ i j, G' i * G' j = G' j * G' i) (S : Finset κ) :
    ∀ 𝒴 : Submodule F (Matrix (Fin n) (Fin n) F),
      (∀ P ∈ 𝒴, ∃ T : κ → Matrix (Fin n) (Fin n) F,
        ∀ t ≤ S.card, Gᵀ ^ t * P = ∑ k ∈ S, T k * G' k ^ t) →
      finrank F 𝒴 ≤ ∑ k ∈ S, finrank F (twistSpace G (G' k)) := by
  induction S using Finset.induction_on with
  | empty =>
    intro 𝒴 h
    have hbot : 𝒴 = ⊥ := by
      rw [eq_bot_iff]
      intro P hP
      obtain ⟨T, hT⟩ := h P hP
      have h0 := hT 0 le_rfl
      rw [pow_zero, Matrix.one_mul, Finset.sum_empty] at h0
      rw [h0]
      exact Submodule.zero_mem _
    rw [hbot, finrank_bot, Finset.sum_empty]
  | insert k S hk ih =>
    intro 𝒴 h
    -- apply the factor of the class `k`
    have hmap : finrank F (𝒴.map (LinearMap.mulLeft F Gᵀ - LinearMap.mulRight F (G' k)))
        ≤ ∑ j ∈ S, finrank F (twistSpace G (G' j)) := by
      apply ih
      rintro _ ⟨P, hP, rfl⟩
      obtain ⟨T, hT⟩ := h P hP
      refine ⟨fun j => T j * (G' j - G' k), fun t ht => ?_⟩
      have h0 := hT t (by rw [Finset.card_insert_of_notMem hk]; omega)
      have h1 := hT (t + 1) (by rw [Finset.card_insert_of_notMem hk]; omega)
      rw [Finset.sum_insert hk] at h0 h1
      -- `G' j ^ t` commutes with `G' k`
      have hpow : ∀ j, G' j ^ t * G' k = G' k * G' j ^ t := fun j =>
        ((Commute.pow_right (show Commute (G' k) (G' j) from hcomm k j) t).eq).symm
      calc Gᵀ ^ t * (Gᵀ * P - P * G' k)
          = Gᵀ ^ (t + 1) * P - Gᵀ ^ t * P * G' k := by
            rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← pow_succ, ← Matrix.mul_assoc]
        _ = (T k * G' k ^ (t + 1) + ∑ j ∈ S, T j * G' j ^ (t + 1))
              - (T k * G' k ^ t + ∑ j ∈ S, T j * G' j ^ t) * G' k := by rw [h1, h0]
        _ = ∑ j ∈ S, (T j * G' j ^ (t + 1) - T j * G' j ^ t * G' k) := by
            rw [Matrix.add_mul, Finset.sum_mul, Finset.sum_sub_distrib, Matrix.mul_assoc (T k),
              ← pow_succ]
            abel
        _ = ∑ j ∈ S, T j * (G' j - G' k) * G' j ^ t := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Matrix.mul_assoc (T j) (G' j ^ t), hpow j, pow_succ', Matrix.mul_assoc (T j)
              (G' j - G' k), Matrix.sub_mul, Matrix.mul_sub]
    have hker := finrank_le_finrank_map_add_finrank_ker
      (LinearMap.mulLeft F Gᵀ - LinearMap.mulRight F (G' k)) 𝒴
    rw [Finset.sum_insert hk]
    change finrank F 𝒴 ≤ finrank F (LinearMap.ker
      (LinearMap.mulLeft F Gᵀ - LinearMap.mulRight F (G' k))) + _
    omega

/-! ### The bound -/

/-- **Twist classes.** Let the terms fall into classes `c : α → κ`, and let `G' k` be pairwise
commuting matrices with `G * (B a)ᵀ = (B a)ᵀ * G' (c a)` for every term `a`. Then, with `s` the
number of classes and for arbitrary `A a`,
`(s + 1) * dim (swapCode A B) ≤ s * n ^ 2 + ∑ k, dim {P | Gᵀ * P = P * G' k}`. -/
theorem succ_mul_finrank_swapCode_le_of_twist_classes {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A B : α → Matrix (Fin n) (Fin n) F) (c : α → κ) (G : Matrix (Fin n) (Fin n) F)
    (G' : κ → Matrix (Fin n) (Fin n) F) (hcomm : ∀ i j, G' i * G' j = G' j * G' i)
    (hG : ∀ a, G * (B a)ᵀ = (B a)ᵀ * G' (c a)) :
    (Fintype.card κ + 1) * finrank F (swapCode A B)
      ≤ Fintype.card κ * n ^ 2 + ∑ k, finrank F (twistSpace G (G' k)) := by
  have hcount := succ_mul_finrank_swapCode_le A B G (Fintype.card κ)
  -- the transposes of the stable part satisfy the moment equations
  have hbound : finrank F ((twistCode A B G (Fintype.card κ)).map
      (transposeLinearEquiv (Fin n) (Fin n) F F).toLinearMap)
      ≤ ∑ k, finrank F (twistSpace G (G' k)) := by
    apply finrank_le_sum_finrank_twistSpace G G' hcomm Finset.univ
    rintro _ ⟨X, hX, rfl⟩
    refine ⟨fun k => ∑ a with c a = k, A a * X * (B a)ᵀ, fun t ht => ?_⟩
    have hXt := mem_twistCode.mp hX t (by simpa using ht)
    rw [mem_swapCode, transpose_mul, transpose_pow] at hXt
    -- `G ^ t` moves through `(B a)ᵀ` as `G' (c a) ^ t`
    have hpow : ∀ a, G ^ t * (B a)ᵀ = (B a)ᵀ * G' (c a) ^ t := fun a =>
      ((SemiconjBy.pow_right (show SemiconjBy (B a)ᵀ (G' (c a)) G from (hG a).symm) t).eq).symm
    calc Gᵀ ^ t * Xᵀ
        = ∑ a, A a * (X * G ^ t) * (B a)ᵀ := hXt
      _ = ∑ a, A a * X * (B a)ᵀ * G' (c a) ^ t := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Matrix.mul_assoc (A a), Matrix.mul_assoc (A a), Matrix.mul_assoc X, hpow a,
            ← Matrix.mul_assoc X, ← Matrix.mul_assoc (A a), ← Matrix.mul_assoc (A a)]
      _ = ∑ k, ∑ a with c a = k, A a * X * (B a)ᵀ * G' (c a) ^ t :=
          (Finset.sum_fiberwise Finset.univ c _).symm
      _ = ∑ k, (∑ a with c a = k, A a * X * (B a)ᵀ) * G' k ^ t := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [(Finset.mem_filter.mp ha).2]
  rw [LinearEquiv.finrank_map_eq] at hbound
  omega

/-- **One twist class.** If `G * (B a)ᵀ = (B a)ᵀ * G'` for every term `a`, then for arbitrary `A a`
`2 * dim (swapCode A B) ≤ n ^ 2 + dim {P | Gᵀ * P = P * G'}`. -/
theorem two_mul_finrank_swapCode_le_of_twist (A B : α → Matrix (Fin n) (Fin n) F)
    (G G' : Matrix (Fin n) (Fin n) F) (hG : ∀ a, G * (B a)ᵀ = (B a)ᵀ * G') :
    2 * finrank F (swapCode A B) ≤ n ^ 2 + finrank F (twistSpace G G') := by
  have h := succ_mul_finrank_swapCode_le_of_twist_classes A B (fun _ => ()) G (fun _ : Unit => G')
    (fun _ _ => rfl) hG
  simpa using h

end SwapRigidity

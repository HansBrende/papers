import LeanMachine.SparseRankBounds
import LeanMachine.ThreeHelperRank
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

/-!
# Finite-alphabet subsets of affine solution spaces

An independent spanning column family leaves a complementary information
set for every affine fibre. The ambient field need not be finite, and the
code need not be a linear subspace or the complete affine fibre.
-/

namespace LeanMachine.SparseAffineCodes

open Finset Module Submodule
open scoped BigOperators

variable {F V W A : Type*} [Field F] [Fintype V]

/-- A matrix admits an independent column set of cardinality equal to its rank. -/
theorem exists_column_basis (B : Matrix W V F) :
    ∃ T : Finset V, T.card = B.rank ∧
      LinearIndependent F (fun j : T => B.col j) := by
  classical
  obtain ⟨t, _, _, hspan, hli⟩ :=
    exists_linearIndepOn_extension (linearIndepOn_empty F B.col)
      (Set.empty_subset (Set.univ : Set V))
  let T := t.toFinite.toFinset
  have hT : (T : Set V) = t := by simp [T]
  have hliT : LinearIndependent F (fun j : T => B.col j) := by
    change LinearIndepOn F B.col (T : Set V)
    rw [hT]
    exact hli
  refine ⟨T, ?_, hliT⟩
  have he : span F (Set.range fun j : T => B.col j) =
      span F (Set.range B.col) := by
    apply le_antisymm
    · apply span_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨j, rfl⟩
    · apply span_le.mpr
      rintro _ ⟨j, rfl⟩
      have hj := hspan (Set.mem_image_of_mem B.col (Set.mem_univ j))
      have hset : B.col '' t = Set.range (fun j : T => B.col j) := by
        ext z
        constructor
        · rintro ⟨v, hv, rfl⟩
          exact ⟨⟨v, by change v ∈ (T : Set V); rwa [hT]⟩, rfl⟩
        · rintro ⟨v, rfl⟩
          exact ⟨v, by rw [← hT]; exact v.property, rfl⟩
      rwa [hset] at hj
  rw [Matrix.rank_eq_finrank_span_cols, ← he, finrank_span_eq_card hliT,
    Fintype.card_coe]

/-- Agreement off an independent column set determines an affine solution. -/
theorem eq_of_mulVec_eq_of_agree_compl (B : Matrix W V F) (T : Finset V)
    (hli : LinearIndependent F (fun j : T => B.col j))
    {x y : V → F} (hB : B.mulVec x = B.mulVec y)
    (hxy : ∀ j, j ∉ T → x j = y j) : x = y := by
  classical
  have hz : B.mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hB, sub_self]
  have hinj : Function.Injective (B.submatrix id (fun j : T => j.val)).mulVec :=
    Matrix.mulVec_injective_iff.mpr hli
  have hrestricted : (B.submatrix id (fun j : T => j.val)).mulVec
      (fun j : T => x j - y j) = 0 := by
    funext i
    change (∑ j : T, B i j * (x j - y j)) = 0
    rw [Finset.sum_coe_sort T (fun j => B i j * (x j - y j))]
    have he : (∑ j ∈ T, B i j * (x j - y j)) =
        ∑ j : V, B i j * (x j - y j) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp [hxy j hj]
    rw [he]
    exact congrFun hz i
  have hxT : (fun j : T => x j - y j) = 0 :=
    hinj (hrestricted.trans (Matrix.mulVec_zero _).symm)
  funext j
  by_cases hj : j ∈ T
  · exact sub_eq_zero.mp (congrFun hxT ⟨j, hj⟩)
  · exact hxy j hj

variable [Fintype A]

/-- Any finite-alphabet subset of one affine fibre is bounded by the
nullity exponent. The alphabet can be embedded in the field differently at
each coordinate; neither the field nor the complete fibre must be finite. -/
theorem card_affine_le (e : V → A ↪ F) (C : Set (V → A))
    (B : Matrix W V F) (a : W → F)
    (hC : ∀ x ∈ C, B.mulVec (fun v => e v (x v)) = a) :
    Nat.card C ≤ Fintype.card A ^ (Fintype.card V - B.rank) := by
  classical
  obtain ⟨T, hT, hli⟩ := exists_column_basis B
  let S := Tᶜ
  let obs : C → (S → A) := fun x v => x.val v
  have hinj : Function.Injective obs := by
    intro x y hobs
    apply Subtype.ext
    have heq : (fun v => e v (x.val v)) = (fun v => e v (y.val v)) := by
      apply eq_of_mulVec_eq_of_agree_compl B T hli
      · exact (hC x.val x.property).trans (hC y.val y.property).symm
      · intro v hv
        exact congrArg (e v) (congrFun hobs ⟨v, mem_compl.mpr hv⟩)
    funext v
    exact (e v).injective (congrFun heq v)
  let : Fintype C := Fintype.ofFinite C
  have hc := Fintype.card_le_of_injective obs hinj
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe,
    S, card_compl, hT] using hc

/-- The common alphabet embedding is the usual special case. -/
theorem card_affine_le_of_embedding (e : A ↪ F) (C : Set (V → A))
    (B : Matrix W V F) (a : W → F)
    (hC : ∀ x ∈ C, B.mulVec (e ∘ x) = a) :
    Nat.card C ≤ Fintype.card A ^ (Fintype.card V - B.rank) :=
  card_affine_le (fun _ => e) C B a hC

variable [Nonempty A]

/-- A half-rank certificate gives a half-size exponent even for arbitrary
nonlinear subsets of an affine fibre. -/
theorem card_le_pow_half_of_rank (e : V → A ↪ F) (C : Set (V → A))
    (B : Matrix W V F) (a : W → F)
    (hC : ∀ x ∈ C, B.mulVec (fun v => e v (x v)) = a)
    (hrank : Fintype.card V ≤ 2 * B.rank) :
    Nat.card C ≤ Fintype.card A ^ (Fintype.card V / 2) := by
  apply (card_affine_le e C B a hC).trans
  apply Nat.pow_le_pow_right Fintype.card_pos
  omega

/-- A rank certificate of factor `k` bounds the `k`th power of the code
cardinality, with no logarithms or divisibility assumptions. -/
theorem card_pow_le_of_rank (e : V → A ↪ F) (C : Set (V → A))
    (B : Matrix W V F) (a : W → F) (k : ℕ) (hk : 1 ≤ k)
    (hC : ∀ x ∈ C, B.mulVec (fun v => e v (x v)) = a)
    (hrank : Fintype.card V ≤ k * B.rank) :
    Nat.card C ^ k ≤ Fintype.card A ^ ((k - 1) * Fintype.card V) := by
  have hdim : (Fintype.card V - B.rank) * k ≤ (k - 1) * Fintype.card V := by
    have hr := B.rank_le_card_width
    have hs := Nat.sub_add_cancel hr
    have hk' := Nat.sub_add_cancel hk
    nlinarith
  calc
    Nat.card C ^ k ≤ (Fintype.card A ^ (Fintype.card V - B.rank)) ^ k :=
      pow_le_pow_left' (card_affine_le e C B a hC) k
    _ = Fintype.card A ^ ((Fintype.card V - B.rank) * k) := (pow_mul _ _ _).symm
    _ ≤ Fintype.card A ^ ((k - 1) * Fintype.card V) :=
      Nat.pow_le_pow_right Fintype.card_pos hdim

variable [DecidableEq V]

/-- Arbitrary outgoing width, with the four-arc exclusion, gives the
corresponding finite-alphabet affine-code bound over every field. -/
theorem card_pow_le_of_outgoing (e : V → A ↪ F) (C : Set (V → A))
    (B : Matrix V V F) (a : V → F) (k : ℕ) (hk : 2 ≤ k)
    (hC : ∀ x ∈ C, B.mulVec (fun v => e v (x v)) = a)
    (hdiag : ∀ i, B i i ≠ 0) (hpattern : LastRowSupport.NoFourArcPattern B)
    (hdegree : ∀ i, (SparseRankBounds.outgoing B i).card ≤ k) :
    Nat.card C ^ k ≤ Fintype.card A ^ ((k - 1) * Fintype.card V) :=
  card_pow_le_of_rank e C B a k (by omega) hC
    (SparseRankBounds.card_le_mul_rank B k hk hdiag hpattern hdegree)

/-- Three outgoing helpers give half when one-way arcs enter vertices of
outgoing degree at most two. -/
theorem card_le_pow_half_of_three_helpers (e : V → A ↪ F) (C : Set (V → A))
    (B : Matrix V V F) (a : V → F)
    (hC : ∀ x ∈ C, B.mulVec (fun v => e v (x v)) = a)
    (hdiag : ∀ i, B i i ≠ 0) (hpattern : LastRowSupport.NoFourArcPattern B)
    (hdegree : ∀ i, (SparseRankBounds.outgoing B i).card ≤ 3)
    (hheads : ThreeHelperRank.OneWayHeadsLow B) :
    Nat.card C ≤ Fintype.card A ^ (Fintype.card V / 2) :=
  card_le_pow_half_of_rank e C B a hC
    (ThreeHelperRank.card_le_two_mul_rank B hdiag hpattern hdegree hheads)

end LeanMachine.SparseAffineCodes

#print axioms LeanMachine.SparseAffineCodes.exists_column_basis
#print axioms LeanMachine.SparseAffineCodes.eq_of_mulVec_eq_of_agree_compl
#print axioms LeanMachine.SparseAffineCodes.card_affine_le
#print axioms LeanMachine.SparseAffineCodes.card_affine_le_of_embedding
#print axioms LeanMachine.SparseAffineCodes.card_le_pow_half_of_rank
#print axioms LeanMachine.SparseAffineCodes.card_pow_le_of_rank
#print axioms LeanMachine.SparseAffineCodes.card_pow_le_of_outgoing
#print axioms LeanMachine.SparseAffineCodes.card_le_pow_half_of_three_helpers

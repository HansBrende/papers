import LeanMachine.RecoveryAcyclic
import LeanMachine.WholeRow.LiftOrder
import Mathlib.Data.Prod.Lex

/-!
# Exact acyclic sets of whole-row hosts

For arbitrary finite row and column types, every induced acyclic cell set is
contained in the set following the last helper in some row order. Thus the
largest acyclic set has size `|R|*|J| - minimumCost ρ`. Empty helper sets and
empty arrays are allowed. Positions in `LiftOrder.cost` are one-based.

This strengthens the square-array cardinality statement in Proposition
`rows(b)` of *Order, Symmetry, and the Swap* to containment and rectangular
arrays. Acyclicity means no nonempty directed closed walk, not an additional
rank-certificate hypothesis.
-/

namespace LeanMachine.WholeRow.AcyclicOrder

open Finset RecoveryAcyclic LiftOrder
open scoped BigOperators Classical
noncomputable section

variable {R J : Type*} [Fintype R] [Fintype J]

/-- A cell reads every cell in the helper rows of its column. -/
def rowHelpers (ρ : J → Finset R) (x : R × J) : Finset (R × J) :=
  (ρ x.2).product univ

omit [Fintype R] in
@[simp] theorem mem_rowHelpers (ρ : J → Finset R) (x y : R × J) :
    y ∈ rowHelpers ρ x ↔ y.1 ∈ ρ x.2 := by
  simp [rowHelpers]

/-- The canonical acyclic set: cells strictly after their last helper row. -/
def rowSet (ρ : J → Finset R) (o : R ≃ Fin (Fintype.card R)) : Finset (R × J) :=
  univ.filter fun x => (ρ x.2).sup (fun i => (o i).val + 1) < (o x.1).val + 1

/-- Every row order supplies an induced acyclic set. -/
theorem rowSet_acyclic (ρ : J → Finset R) (o : R ≃ Fin (Fintype.card R)) :
    Acyclic (rowHelpers ρ) (rowSet ρ o) := by
  apply (rank_iff_acyclic _ _).mp
  refine ⟨fun x => (o x.1).val, ?_⟩
  intro x hx y _ hy
  have hx' := (mem_filter.mp hx).2
  have hy' : (o y.1).val + 1 ≤ (ρ x.2).sup (fun i => (o i).val + 1) :=
    Finset.le_sup (f := fun i => (o i).val + 1) ((mem_rowHelpers ρ x y).mp hy)
  change (o y.1).val < (o x.1).val
  omega

private theorem refine_order (τ : R → ℕ) :
    ∃ o : R ≃ Fin (Fintype.card R), ∀ x y, τ x < τ y → (o x).val < (o y).val := by
  let e := Fintype.equivFin R
  let f : R → ℕ ×ₗ Fin (Fintype.card R) := fun x => toLex (τ x, e x)
  have hf : Function.Injective f := by
    intro x y h
    exact e.injective (congrArg (fun z => (ofLex z).2) h)
  let : LinearOrder R := LinearOrder.lift' f hf
  let p := (Fintype.orderIsoFinOfCardEq R rfl).symm
  refine ⟨p.toEquiv, ?_⟩
  intro x y h
  apply p.strictMono
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- Every acyclic set is contained in a canonical row-order acyclic set.
This is stronger than merely bounding its cardinality. -/
theorem exists_rowSet_superset (ρ : J → Finset R) (A : Finset (R × J))
    (hA : Acyclic (rowHelpers ρ) A) :
    ∃ o : R ≃ Fin (Fintype.card R), A ⊆ rowSet ρ o := by
  obtain ⟨rank, hrank⟩ := (rank_iff_acyclic _ _).mpr hA
  let τ : R → ℕ := fun i => (univ.filter (fun j => (i, j) ∈ A)).sup
    (fun j => rank (i, j) + 1)
  obtain ⟨o, ho⟩ := refine_order τ
  refine ⟨o, ?_⟩
  intro x hx
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  have hτx : rank x + 1 ≤ τ x.1 :=
    Finset.le_sup (f := fun j => rank (x.1, j) + 1)
      (mem_filter.mpr ⟨mem_univ x.2, hx⟩)
  have hlt : ∀ i ∈ ρ x.2, τ i < τ x.1 := by
    intro i hi
    have hτi : τ i ≤ rank x := by
      apply Finset.sup_le
      intro j hj
      have := hrank x hx (i, j) (mem_filter.mp hj).2
        ((mem_rowHelpers ρ x (i, j)).mpr hi)
      omega
    omega
  have hs : (ρ x.2).sup (fun i => (o i).val + 1) ≤ (o x.1).val := by
    apply Finset.sup_le
    intro i hi
    have := ho i x.1 (hlt i hi)
    omega
  omega

private theorem prefix_card (o : R ≃ Fin (Fintype.card R)) (t : ℕ)
    (ht : t ≤ Fintype.card R) :
    (univ.filter (fun x => (o x).val + 1 ≤ t)).card = t := by
  let S := univ.filter (fun x => (o x).val + 1 ≤ t)
  have hi : Function.Injective (fun x => (o x).val) := by
    intro x y h
    exact o.injective (Fin.ext h)
  have he : S.image (fun x => (o x).val) = range t := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
      exact mem_range.mpr (by have := (mem_filter.mp hx).2; omega)
    · intro hz
      have hz' := mem_range.mp hz
      let v : Fin (Fintype.card R) := ⟨z, lt_of_lt_of_le hz' ht⟩
      refine mem_image.mpr ⟨o.symm v, ?_, ?_⟩
      · apply mem_filter.mpr
        simp only [mem_univ, true_and, o.apply_symm_apply]
        exact Nat.add_one_le_iff.mpr hz'
      · simp [v]
  calc
    S.card = (S.image (fun x => (o x).val)).card := (card_image_of_injective S hi).symm
    _ = t := by rw [he, card_range]

/-- The acyclic cells and the last-helper invoice partition the full array. -/
theorem rowSet_card_add_cost (ρ : J → Finset R) (o : R ≃ Fin (Fintype.card R)) :
    (rowSet ρ o).card + cost ρ o = Fintype.card R * Fintype.card J := by
  let seed := univ.filter (fun x : R × J =>
    (o x.1).val + 1 ≤ (ρ x.2).sup (fun i => (o i).val + 1))
  have hs : seed.card = cost ρ o := by
    unfold cost
    simp only [seed, card_filter, Fintype.sum_prod_type]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    rw [← card_filter]
    apply prefix_card
    exact Finset.sup_le fun i _ => Nat.add_one_le_iff.mpr (o i).isLt
  have hp := card_filter_add_card_filter_not (s := (univ : Finset (R × J)))
    (fun x => (ρ x.2).sup (fun i => (o i).val + 1) < (o x.1).val + 1)
  simpa only [not_lt, ← hs, rowSet, seed, card_univ, Fintype.card_prod] using hp

/-- Every induced acyclic-set invoice is at least some row-order invoice. -/
theorem exists_cost_le_complement (ρ : J → Finset R) (A : Finset (R × J))
    (hA : Acyclic (rowHelpers ρ) A) :
    ∃ o : R ≃ Fin (Fintype.card R),
      A.card + cost ρ o ≤ Fintype.card R * Fintype.card J := by
  obtain ⟨o, ho⟩ := exists_rowSet_superset ρ A hA
  exact ⟨o, (Nat.add_le_add_right (card_le_card ho) _).trans_eq (rowSet_card_add_cost ρ o)⟩

/-- The least row-order cost, including the empty-array cases. -/
def minimumCost (ρ : J → Finset R) : ℕ :=
  Nat.find (show ∃ k, ∃ o : R ≃ Fin (Fintype.card R), cost ρ o = k from
    ⟨cost ρ (Fintype.equivFin R), Fintype.equivFin R, rfl⟩)

theorem exists_minimum_order (ρ : J → Finset R) :
    ∃ o : R ≃ Fin (Fintype.card R), cost ρ o = minimumCost ρ := by
  unfold minimumCost
  exact Nat.find_spec (p := fun k => ∃ o : R ≃ Fin (Fintype.card R), cost ρ o = k) _

theorem minimumCost_le (ρ : J → Finset R) (o : R ≃ Fin (Fintype.card R)) :
    minimumCost ρ ≤ cost ρ o := Nat.find_min' _ ⟨o, rfl⟩

/-- A lower bound attained by one order identifies the minimum. -/
theorem minimumCost_eq_of_bounds (ρ : J → Finset R) (s : ℕ)
    (hl : ∀ o, s ≤ cost ρ o) (hu : ∃ o, cost ρ o = s) : minimumCost ρ = s := by
  obtain ⟨o, ho⟩ := exists_minimum_order ρ
  obtain ⟨p, hp⟩ := hu
  have h₁ := hl o
  have h₂ := minimumCost_le ρ p
  omega

/-- The exact maximum induced acyclic-set size: all sets obey the bound and
one attains it. This includes loops as cycles and needs no square hypothesis. -/
theorem exact_acyclic_card (ρ : J → Finset R) :
    (∀ A, Acyclic (rowHelpers ρ) A →
      A.card ≤ Fintype.card R * Fintype.card J - minimumCost ρ) ∧
    ∃ A, Acyclic (rowHelpers ρ) A ∧
      A.card = Fintype.card R * Fintype.card J - minimumCost ρ := by
  constructor
  · intro A hA
    obtain ⟨o, ho⟩ := exists_cost_le_complement ρ A hA
    have := minimumCost_le ρ o
    omega
  · obtain ⟨o, ho⟩ := exists_minimum_order ρ
    refine ⟨rowSet ρ o, rowSet_acyclic ρ o, ?_⟩
    have := rowSet_card_add_cost ρ o
    omega

end
end LeanMachine.WholeRow.AcyclicOrder

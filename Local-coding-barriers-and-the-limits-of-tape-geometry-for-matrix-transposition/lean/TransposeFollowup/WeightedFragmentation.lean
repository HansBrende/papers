import TransposeFollowup.TreeDecomposition
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Logic.Equiv.Option

/-! Weighted fragmentation witnesses. Labels may coarsen the remaining graph
components. Their masses bound the actual component masses, and removed nodes
are excluded from those masses. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false
universe u v

noncomputable def labelMass {V : Type u} [Fintype V] {K : Type v}
    (w : V → ℕ) (S : Finset V) (label : V → K) (a : K) : ℕ :=
  ∑ x, if x ∉ S ∧ label x = a then w x else 0

structure WeightedFragmentation {V : Type u} [Fintype V]
    (G : SimpleGraph V) (w : V → ℕ) (L : ℕ) where
  removed : Finset V
  Label : Type u
  label : V → Label
  edge_same : ∀ {x y}, x ∉ removed → y ∉ removed → G.Adj x y → label x = label y
  mass_le : ∀ a, labelMass w removed label a ≤ L

/-- Vertex deletion with its vertex type explicit, keeping one canonical
finite-type instance throughout the leaf induction. -/
def withoutVertex {V : Type u} (G : SimpleGraph V) (v : V) :
    SimpleGraph {x : V // x ≠ v} := G.comap Subtype.val

namespace WeightedFragmentation

variable {V : Type u} [Fintype V] {G : SimpleGraph V} {w : V → ℕ} {L : ℕ}
    (F : WeightedFragmentation G w L)

theorem label_eq_of_connected {x y : V}
    (h : OutsideConnected G F.removed x y) : F.label x = F.label y := by
  obtain ⟨hx, hy, ⟨p⟩⟩ := h
  have same : ∀ {a b : {x | x ∉ F.removed}},
      (G.induce {x | x ∉ F.removed}).Walk a b → F.label a.val = F.label b.val := by
    intro a b q
    induction q with
    | nil => rfl
    | @cons a c b h _ ih => exact (F.edge_same a.property c.property h).trans ih
  exact same p

theorem component_mass_le (x : V) :
    ∑ y ∈ componentSet G F.removed x, w y ≤ L := by
  calc
    _ = ∑ y, if y ∈ componentSet G F.removed x then w y else 0 := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ labelMass w F.removed F.label (F.label x) := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y ∈ componentSet G F.removed x
      · have hconn := (mem_componentSet G F.removed x y).mp hy
        have hys := hconn.choose_spec.choose
        simp [hy, hys, (F.label_eq_of_connected hconn).symm]
      · simp [hy]
    _ ≤ L := F.mass_le _

end WeightedFragmentation

/-- Split a finite sum into one vertex and its complement. This identity is
also used after collapsing a leaf's weight onto its unique neighbor. -/
theorem sum_split_vertex {V : Type u} [Fintype V] (f : V → ℕ) (v : V) :
    ∑ x, f x = f v + ∑ x : {x // x ≠ v}, f x.val := by
  rw [← (Equiv.optionSubtypeNe v).sum_comp f]
  simp

/-- Extend a label assignment on the complement of a vertex. -/
noncomputable def extendLabel {V : Type u} {K : Type v} (v : V)
    (c : {x // x ≠ v} → K) (a : Option K) (x : V) : Option K :=
  if hx : x = v then a else some (c ⟨x, hx⟩)

@[simp] theorem extendLabel_at {V : Type u} {K : Type v} (v : V)
    (c : {x // x ≠ v} → K) (a : Option K) : extendLabel v c a v = a := by
  simp [extendLabel]

@[simp] theorem extendLabel_away {V : Type u} {K : Type v} (v : V)
    (c : {x // x ≠ v} → K) (a : Option K) (x : {x // x ≠ v}) :
    extendLabel v c a x.val = some (c x) := by
  simp [extendLabel, x.property]

noncomputable def liftRemoved {V : Type u} (v : V)
    (S : Finset {x // x ≠ v}) : Finset V := S.image Subtype.val

@[simp] theorem mem_liftRemoved {V : Type u} (v : V)
    (S : Finset {x // x ≠ v}) (x : {x // x ≠ v}) :
    x.val ∈ liftRemoved v S ↔ x ∈ S := by
  simp [liftRemoved, x.property]

@[simp] theorem vertex_not_mem_liftRemoved {V : Type u} (v : V)
    (S : Finset {x // x ≠ v}) : v ∉ liftRemoved v S := by
  simp only [liftRemoved, Finset.mem_image]
  rintro ⟨x, _, hx⟩
  exact x.property hx

@[simp] theorem card_liftRemoved {V : Type u} (v : V)
    (S : Finset {x // x ≠ v}) : (liftRemoved v S).card = S.card := by
  exact Finset.card_image_of_injective S Subtype.val_injective

theorem labelMass_extend {V : Type u} [Fintype V] {K : Type v}
    (w : V → ℕ) (v : V) (S : Finset {x // x ≠ v})
    (c : {x // x ≠ v} → K) (a k : Option K) :
    labelMass w (liftRemoved v S) (extendLabel v c a) k =
      (if a = k then w v else 0) +
        labelMass (fun x => w x.val) S (fun x => some (c x)) k := by
  unfold labelMass
  rw [sum_split_vertex _ v]
  simp

theorem labelMass_extend_removed {V : Type u} [Fintype V] {K : Type v}
    (w : V → ℕ) (v : V) (S : Finset {x // x ≠ v})
    (c : {x // x ≠ v} → K) (a k : Option K) :
    labelMass w (insert v (liftRemoved v S)) (extendLabel v c a) k =
      labelMass (fun x => w x.val) S (fun x => some (c x)) k := by
  unfold labelMass
  rw [sum_split_vertex _ v]
  simp only [Finset.mem_insert, true_or, not_true_eq_false, false_and,
    ↓reduceIte, zero_add]
  apply Finset.sum_congr rfl
  intro x _
  simp [x.property]

@[simp] theorem labelMass_some {V : Type u} [Fintype V] {K : Type v}
    (w : V → ℕ) (S : Finset V) (c : V → K) (a : K) :
    labelMass w S (fun x => some (c x)) (some a) = labelMass w S c a := by
  simp [labelMass]

@[simp] theorem labelMass_none {V : Type u} [Fintype V] {K : Type v}
    (w : V → ℕ) (S : Finset V) (c : V → K) :
    labelMass w S (fun x => some (c x)) none = 0 := by
  simp [labelMass]

/-- Accumulate a leaf's weight at its unique neighbor. -/
noncomputable def addWeight {V : Type u} (w : V → ℕ) (v : V) (q : ℕ) (x : V) : ℕ :=
  w x + if x = v then q else 0

theorem sum_addWeight {V : Type u} [Fintype V] (w : V → ℕ) (v : V) (q : ℕ) :
    ∑ x, addWeight w v q x = (∑ x, w x) + q := by
  simp [addWeight, Finset.sum_add_distrib]

theorem labelMass_addWeight {V : Type u} [Fintype V] {K : Type v}
    (w : V → ℕ) (v : V) (q : ℕ) (S : Finset V) (c : V → K) (a : K) :
    labelMass (addWeight w v q) S c a =
      labelMass w S c a + if v ∉ S ∧ c v = a then q else 0 := by
  unfold labelMass addWeight
  have ht (x : V) :
      (if x ∉ S ∧ c x = a then w x + (if x = v then q else 0) else 0) =
      (if x ∉ S ∧ c x = a then w x else 0) +
        (if x = v then (if v ∉ S ∧ c v = a then q else 0) else 0) := by
    by_cases hx : x = v
    · subst x; split_ifs <;> omega
    · simp only [hx, ↓reduceIte, add_zero]
  simp_rw [ht, Finset.sum_add_distrib]
  simp

end TransposeFollowup

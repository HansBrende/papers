import LeanMachine.CausalCutCapacity

/-! Definition 8.1: the actual row-source, column-group and helper-fibre
interface. Field alphabets and real capacity allocations may vary across
fibres. The local conditions are functional, not merely output purity. -/

namespace SourceCovers.CausalGroups

open LeanMachine Finset
open scoped BigOperators Classical
noncomputable section

abbrev Bit (d b : ℕ) := Fin d × Fin d × Fin b
abbrev Input (d b : ℕ) := Bit d b → Bool

/-- A monotone surjection is precisely an ordered partition into nonempty
consecutive column fibres. -/
structure ColumnPartition (d h : ℕ) where
  group : Fin d → Fin h
  onto : Function.Surjective group
  ordered : Monotone group

namespace ColumnPartition

variable {d h : ℕ} (P : ColumnPartition d h)

def columns (a : Fin h) : Finset (Fin d) := univ.filter fun j => P.group j = a

theorem columns_nonempty (a : Fin h) : (P.columns a).Nonempty := by
  obtain ⟨j, hj⟩ := P.onto a
  exact ⟨j, by simpa [columns] using hj⟩

theorem columns_convex (a : Fin h) : Set.OrdConnected (P.group ⁻¹' {a}) := by
  constructor
  intro i hi j hj l hl
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hi hj ⊢
  exact le_antisymm (hj ▸ P.ordered hl.2) (hi ▸ P.ordered hl.1)

theorem columns_ordered {a a' : Fin h} (haa : a < a') {i j : Fin d}
    (hi : P.group i = a) (hj : P.group j = a') : i < j := by
  by_contra hn
  have hle := P.ordered (le_of_not_gt hn)
  rw [hi, hj] at hle
  exact (not_le_of_gt haa) hle

end ColumnPartition

/-- A finite block network with its original row attachments and ordered
transpose outputs. Parallel physical edges are allowed. -/
structure Network (d b h n : ℕ) (Edge : Type*) [Fintype Edge] where
  partition : ColumnPartition d h
  source : Edge → Fin n
  target : Edge → Fin n
  earlier : ∀ e, source e < target e
  spine : Fin (n - 1) → Edge
  spine_source : ∀ v, (source (spine v)).val = v.val
  spine_target : ∀ v, (target (spine v)).val = v.val + 1
  attached : Fin d → Set (Fin n)
  output : Bit d b → Fin n
  output_order : ∀ i j, i.2.1 < j.2.1 → output i ≤ output j
  capacity : Edge → ℝ
  capacity_nonneg : ∀ e, 0 ≤ capacity e

namespace Network

variable {d b h n : ℕ} {Edge : Type*} [Fintype Edge] (G : Network d b h n Edge)

abbrev GroupBit (a : Fin h) := {i : Bit d b // G.partition.group i.2.1 = a}

def projection (a : Fin h) (x : Input d b) : G.GroupBit a → Bool := fun i => x i.val

abbrev GroupColumn (a : Fin h) := {j : Fin d // G.partition.group j = a}

def rowData (a : Fin h) (B : Set (Fin d)) : Set (G.GroupBit a) := {i | i.val.1 ∈ B}

def rowDataEquiv (a : Fin h) (B : Set (Fin d)) :
    G.rowData a B ≃ B × G.GroupColumn a × Fin b where
  toFun i := (⟨i.val.val.1, i.property⟩, ⟨i.val.val.2.1, i.val.property⟩, i.val.val.2.2)
  invFun i := ⟨⟨(i.1.val, i.2.1.val, i.2.2), i.2.1.property⟩, i.1.property⟩
  left_inv := by rintro ⟨⟨⟨i, j, t⟩, hg⟩, hb⟩; rfl
  right_inv := by rintro ⟨⟨i, hi⟩, ⟨j, hj⟩, t⟩; rfl

theorem card_rowData (a : Fin h) (B : Set (Fin d)) :
    Fintype.card (G.rowData a B) = Fintype.card B * Fintype.card (G.GroupColumn a) * b := by
  simpa only [Fintype.card_prod, Fintype.card_fin, mul_assoc] using
    Fintype.card_congr (G.rowDataEquiv a B)

def layout (a : Fin h) : CausalFields.Layout (Fin n) Edge (G.GroupBit a) where
  source := G.source
  target := G.target
  rank := Fin.val
  earlier := G.earlier
  visible := fun v => {i | v ∈ G.attached i.val.1}
  output := fun i => G.output i.val

/-- This supplies the ordered endpoints needed for disjoint collectors;
there is no chronological constraint on edges beyond the network rank. -/
theorem group_output_order {a a' : Fin h} (haa : a < a')
    (i : G.GroupBit a) (j : G.GroupBit a') : G.output i.val ≤ G.output j.val :=
  G.output_order i.val j.val (G.partition.columns_ordered haa i.property j.property)

/-- One attained fibre, with actual field values and locally valid
evaluation. Every group has its own allocation on every physical edge. -/
structure FibreTyping (C : Set (Input d b)) where
  Alphabet : Edge → Fin h → Type
  finite_alphabet : ∀ e a, Fintype (Alphabet e a)
  allocation : Edge → Fin h → ℝ
  allocation_nonneg : ∀ e a, 0 ≤ allocation e a
  alphabet_bound : ∀ e a, (@Fintype.card (Alphabet e a) (finite_alphabet e a) : ℝ) ≤
    (2 : ℝ) ^ allocation e a
  capacity_bound : ∀ e, ∑ a, allocation e a ≤ G.capacity e
  evaluation : ∀ a, CausalFields.Evaluation (G.layout a) (fun e => Alphabet e a) C (G.projection a)

def fibre {Helper : Type*} (C : Set (Input d b)) (Z : Input d b → Helper) (z : Helper) :=
  {x | x ∈ C ∧ Z x = z}

/-- Typing is required on every attained helper value, and nowhere else.
Alphabets, allocations and local rules are fixed on each whole fibre. -/
def CausalGroupTyping {Helper : Type*} (C : Set (Input d b)) (Z : Input d b → Helper) : Prop :=
  ∀ z ∈ Z '' C, Nonempty (G.FibreTyping (fibre C Z z))

theorem fibre_nonempty {Helper : Type*} {C : Set (Input d b)}
    {Z : Input d b → Helper} {z : Helper} (hz : z ∈ Z '' C) : (fibre C Z z).Nonempty := by
  obtain ⟨x, hx, hz⟩ := hz
  exact ⟨x, hx, hz⟩

namespace FibreTyping

variable {G} {C : Set (Input d b)} (F : G.FibreTyping C)

/-- The full original fibre may correlate groups arbitrarily. Fixing just
one raw group projection nevertheless fixes all fields of that group. -/
theorem group_autonomy (a : Fin h) :
    Function.FactorsThrough (F.evaluation a).value (fun x : C => G.projection a x.val) :=
  (F.evaluation a).value_factorsThrough_raw

/-- The code on the actual joint projection, without selecting independent
values in the other groups. -/
def projectedEvaluation (a : Fin h) : CausalFields.Evaluation (G.layout a)
    (fun e => F.Alphabet e a) (Set.range (fun x : C => G.projection a x.val)) (fun y => y) :=
  (F.evaluation a).projected

theorem projected_agrees (a : Fin h) (x : C) :
    (F.projectedEvaluation a).value ⟨G.projection a x.val, ⟨x, rfl⟩⟩ =
      (F.evaluation a).value x :=
  (F.evaluation a).projected_agrees x

theorem local_edge_function [Nonempty C] (a : Fin h) (e : Edge) :
    ∃ f : CausalFields.Observation (Symbol := Bool) (G.layout a)
        (fun e => F.Alphabet e a) (G.source e) → F.Alphabet e a,
      ∀ x : C, f (CausalFields.observe (G.layout a) (fun e => F.Alphabet e a)
        (G.projection a) (F.evaluation a).value x (G.source e)) = (F.evaluation a).value x e :=
  (F.evaluation a).exists_edge_rule e

theorem local_output_function [Nonempty C] (a : Fin h) (i : G.GroupBit a) :
    ∃ f : CausalFields.Observation (Symbol := Bool) (G.layout a)
        (fun e => F.Alphabet e a) (G.output i.val) → Bool,
      ∀ x : C, f (CausalFields.observe (G.layout a) (fun e => F.Alphabet e a)
        (G.projection a) (F.evaluation a).value x (G.output i.val)) = x.val i.val :=
  (F.evaluation a).exists_output_rule i

/-- The support bound for any cut containing the group's outputs. After
collector construction the sole output location will be its collector sink. -/
theorem cut_support_bound [Nonempty C] (a : Fin h) (U : Set (Fin n)) (B : Set (Fin d))
    (hrows : ∀ i v, v ∈ U → v ∈ G.attached i → i ∈ B)
    (houtput : ∀ i : G.GroupBit a, G.output i.val ∈ U) :
    Real.logb 2 (Fintype.card (Set.range (fun x : C => G.projection a x.val))) ≤
      (Fintype.card B * Fintype.card (G.GroupColumn a) * b : ℕ) +
        ∑ e : {e // G.target e ∈ U ∧ G.source e ∉ U}, F.allocation e.val a := by
  let : ∀ e, Fintype (F.Alphabet e a) := fun e => F.finite_alphabet e a
  have he := (F.evaluation a).log_support_le_cut (fun e => F.allocation e a)
    (fun e => F.alphabet_bound e a) U (G.rowData a B)
    (fun v hv i hi => hrows i.val.1 v hv hi) houtput
  simp only [G.card_rowData, layout, ← Nat.card_eq_fintype_card] at he ⊢
  convert he using 2
  congr 1

end FibreTyping
end Network
end
end SourceCovers.CausalGroups

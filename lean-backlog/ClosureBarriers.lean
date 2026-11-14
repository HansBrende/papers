import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Limits of transported coordinate-closure certificates

The assigned-rule bound is proved for explicit finite recovery witnesses.
Each recovered coordinate chooses one displayed rule whose helpers are seeds
or have smaller recovery rank. Its assigned coordinates are an acyclic set
for that copy. The real invoice corollary concerns proof certificates, not
actual code capacity or the full Shannon relaxation.

`RectangleBarrierTarget` records the empty-rectangle theorem; its proof is in
the companion module `RectangleBarrier`.
-/

namespace LeanBacklog.ClosureBarriers

open Finset

universe u v

variable {V : Type u} {J : Type v}

/-- A strict rank on internal helper arcs. In particular, a loop is forbidden. -/
def RankAcyclic (H : V → Finset V) (A : Finset V) : Prop :=
  ∃ rank : V → ℕ, ∀ x ∈ A, ∀ y ∈ A, y ∈ H x → rank y < rank x

/-- A recovery order with one chosen copy for each nonseed coordinate.
The choice is not required at seeds, so an empty copy type is allowed when
every coordinate is initially given. Equal ranks on unrelated cells are harmless. -/
structure RecoveryWitness (H : J → V → Finset V) (S : Finset V) where
  rank : V → ℕ
  copy : {x : V // x ∉ S} → J
  earlier : ∀ x : {x : V // x ∉ S}, ∀ y ∈ H (copy x) x,
    y ∈ S ∨ rank y < rank x

section Counting

variable [Fintype V] [DecidableEq V] [DecidableEq J]
  {H : J → V → Finset V} {S : Finset V}

/-- Coordinates whose recovering rule was chosen from copy `j`. -/
def assigned (W : RecoveryWitness H S) (j : J) : Finset V :=
  (univ.filter fun x : {x : V // x ∉ S} => W.copy x = j).image Subtype.val

theorem assigned_acyclic (W : RecoveryWitness H S) (j : J) :
    RankAcyclic (H j) (assigned W j) := by
  refine ⟨W.rank, ?_⟩
  intro x hx y hy hxy
  obtain ⟨x₀, hx₀, rfl⟩ := mem_image.mp hx
  obtain ⟨y₀, _, rfl⟩ := mem_image.mp hy
  have hj : W.copy x₀ = j := (mem_filter.mp hx₀).2
  have h := W.earlier x₀ y₀ (hj ▸ hxy)
  exact h.resolve_left y₀.property

variable [Fintype J]

/-- The assigned sets partition precisely the nonseed coordinates. -/
theorem sum_assigned_card (W : RecoveryWitness H S) :
    ∑ j : J, (assigned W j).card = Fintype.card V - S.card := by
  simp only [assigned, card_image_of_injective _ Subtype.val_injective]
  have h := card_eq_sum_card_fiberwise (f := W.copy)
    (s := univ) (t := univ) (by intro x hx; exact mem_univ _)
  rw [← h]
  simp [Fintype.card_subtype_compl]

/-- Assigned-rule bound, using any valid acyclic-size caps. This avoids
computing a maximum and includes arbitrary different helper graphs. -/
theorem assigned_rule_card_le (W : RecoveryWitness H S) (a : J → ℕ)
    (ha : ∀ j A, RankAcyclic (H j) A → A.card ≤ a j) :
    Fintype.card V - S.card ≤ ∑ j : J, a j := by
  rw [← sum_assigned_card W]
  exact sum_le_sum fun j _ => ha j _ (assigned_acyclic W j)

/-- Addition form without truncated subtraction. -/
theorem card_le_seed_add (W : RecoveryWitness H S) (a : J → ℕ)
    (ha : ∀ j A, RankAcyclic (H j) A → A.card ≤ a j) :
    Fintype.card V ≤ S.card + ∑ j : J, a j := by
  have h := assigned_rule_card_le W a ha
  have hS : S.card ≤ Fintype.card V := card_le_univ S
  omega

end Counting

section Transport

/-- Relabel both target and helper coordinates by one equivalence. -/
def transport (H : V → Finset V) (e : V ≃ V) (x : V) : Finset V :=
  (H (e.symm x)).map e.toEmbedding

/-- Pull an acyclic set back through a coordinate transport. -/
theorem acyclic_transport_pullback (H : V → Finset V) (e : V ≃ V)
    (A : Finset V) (hA : RankAcyclic (transport H e) A) :
    RankAcyclic H (A.map e.symm.toEmbedding) := by
  obtain ⟨rank, h⟩ := hA
  refine ⟨fun x => rank (e x), ?_⟩
  intro x hx y hy hxy
  obtain ⟨x₀, hx₀, rfl⟩ := mem_map.mp hx
  obtain ⟨y₀, hy₀, rfl⟩ := mem_map.mp hy
  have hmem : y₀ ∈ transport H e x₀ := by
    exact mem_map.mpr ⟨e.symm y₀, hxy, by simp⟩
  simpa using h x₀ hx₀ y₀ hy₀ hmem

/-- Coordinate transports preserve every uniform acyclic-size cap. -/
theorem acyclic_cap_transport (H : V → Finset V) (a : ℕ)
    (ha : ∀ A, RankAcyclic H A → A.card ≤ a) (e : V ≃ V)
    (A : Finset V) (hA : RankAcyclic (transport H e) A) : A.card ≤ a := by
  simpa using ha _ (acyclic_transport_pullback H e A hA)

variable [Fintype V] [DecidableEq V]

/-- The additive intersection/seed invoice of transported copies is no
smaller than the original acyclic-set invoice. Positive `m` may grow with `V`.
No statement about actual capacity is made or needed. -/
theorem transported_invoice_ge (H : V → Finset V) (a m : ℕ) (hm : 0 < m)
    (ha : ∀ A, RankAcyclic H A → A.card ≤ a) (e : Fin m → V ≃ V)
    (S : Finset V) (W : RecoveryWitness (fun j => transport H (e j)) S) :
    (Fintype.card V : ℝ) - a ≤
      (((m : ℝ) - 1) * Fintype.card V + S.card) / m := by
  have hN : Fintype.card V ≤ S.card + m * a := by
    simpa using card_le_seed_add W (fun _ => a)
      (fun j A hA => acyclic_cap_transport H a ha (e j) A hA)
  have hN' : (Fintype.card V : ℝ) ≤ (S.card : ℝ) + (m : ℝ) * a := by
    exact_mod_cast hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  apply (le_div_iff₀ hm').2
  nlinarith only [hN']

end Transport

/-- No two equally sized row/column sets form an empty incidence rectangle. -/
def NoEmptyRectangle {d : ℕ} (ρ : Fin d → Finset (Fin d)) (r : ℕ) : Prop :=
  ∀ R C : Finset (Fin d), R.card = r → C.card = r →
    ∃ i ∈ R, ∃ j ∈ C, i ∈ ρ j

/-- A layout's target column reads all cells in its helper rows. -/
def gridHelpers [Fintype V] [DecidableEq V] {d : ℕ}
    (ρ : Fin d → Finset (Fin d)) (layout : V ≃ Fin d × Fin d) (x : V) : Finset V :=
  univ.filter fun y => (layout y).1 ∈ ρ (layout x).2

/-- The rectangle barrier for arbitrary transported grid layouts, proved in
`RectangleBarrier.rectangleBarrierTarget`. The addition form is the exact
integer inequality and does not use truncated subtraction of areas. -/
def RectangleBarrierTarget (V : Type u) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (d m r : ℕ), 0 < m → 1 ≤ r → r ≤ d →
    ∀ (ρ : Fin d → Finset (Fin d)), NoEmptyRectangle ρ r →
      ∀ (layout : Fin m → V ≃ Fin d × Fin d) (S : Finset V),
        Nonempty (RecoveryWitness (fun j => gridHelpers ρ (layout j)) S) →
        d * d + (r - 1) ^ 2 ≤ S.card + (m + 1) * d * (r - 1)

#print axioms assigned_acyclic
#print axioms sum_assigned_card
#print axioms assigned_rule_card_le
#print axioms card_le_seed_add
#print axioms acyclic_transport_pullback
#print axioms acyclic_cap_transport
#print axioms transported_invoice_ge
#check RectangleBarrierTarget

end LeanBacklog.ClosureBarriers

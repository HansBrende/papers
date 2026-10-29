import LeanMachine.CausalCutCapacity
import Mathlib.Order.Interval.Finset.Fin

/-! Collecting distributed outputs along a finite memory spine. Each added
field contains only the coordinates already output, rather than a padded
copy of the entire raw vector. The local evaluation works on any support. -/

namespace LeanMachine.CausalFields

open Finset
open scoped BigOperators Classical
noncomputable section

universe u
variable {n : ℕ} {Edge Input : Type*} {Bit Symbol : Type u}

/-- An interval containing all outputs of a forward network. Endpoints
need not be attained, and coincident endpoints are allowed. -/
structure Collector (G : Layout (Fin n) Edge Bit) where
  first : Fin n
  last : Fin n
  ordered : first ≤ last
  output_ge : ∀ i, first ≤ G.output i
  output_le : ∀ i, G.output i ≤ last
  forward : ∀ e, G.source e < G.target e

namespace Collector

variable {G : Layout (Fin n) Edge Bit} (S : Collector G)

abbrev Link := {v : Fin n // S.first ≤ v ∧ v < S.last}

def next (v : S.Link) : Fin n := ⟨v.val.val + 1, by
  have := v.property.2
  have := S.last.isLt
  omega⟩

abbrev Prefix (_S : Collector G) (v : Fin n) := {i : Bit // G.output i ≤ v}

def layout : Layout (Fin n) (Edge ⊕ S.Link) Bit where
  source := Sum.elim G.source Subtype.val
  target := Sum.elim G.target S.next
  rank := Fin.val
  earlier := by
    rintro (e | v)
    · exact S.forward e
    · change v.val.val < v.val.val + 1
      omega
  visible := G.visible
  output := fun _ => S.last

def Field (F : Edge → Type u) : Edge ⊕ S.Link → Type u
  | .inl e => F e
  | .inr v => S.Prefix v.val → Symbol

variable {F : Edge → Type u} {C : Set Input} {raw : Input → Bit → Symbol}
variable (E : Evaluation G F C raw)

def value (x : C) : (e : Edge ⊕ S.Link) → S.Field (Symbol := Symbol) F e
  | .inl e => E.value x e
  | .inr _ => fun i => raw x.val i.val

/-- Original incoming observations are retained unchanged. -/
theorem original_observation_eq {x y : C} {v : Fin n}
    (h : observe S.layout (S.Field F) raw (S.value E) x v =
      observe S.layout (S.Field F) raw (S.value E) y v) :
    observe G F raw E.value x v = observe G F raw E.value y v := by
  obtain ⟨hf, hr⟩ := (observe_eq_iff _ _ _ _ _ _ _).mp h
  exact (observe_eq_iff _ _ _ _ _ _ _).mpr
    ⟨fun e he => hf (.inl e) he, hr⟩

/-- At a node no later than the collector sink, the incoming collector
and the original local rule recover every coordinate already output. -/
theorem raw_eq_of_observation {x y : C} {v : Fin n} (hv : v ≤ S.last)
    (h : observe S.layout (S.Field F) raw (S.value E) x v =
      observe S.layout (S.Field F) raw (S.value E) y v)
    (i : Bit) (hi : G.output i ≤ v) : raw x.val i = raw y.val i := by
  rcases lt_or_eq_of_le hi with hi | hi
  · have hlo := S.output_ge i
    let p : S.Link := ⟨⟨v.val - 1, by omega⟩, by
      constructor
      · change S.first.val ≤ v.val - 1
        omega
      · change v.val - 1 < S.last.val
        omega⟩
    have hp : S.next p = v := by
      apply Fin.ext
      change v.val - 1 + 1 = v.val
      omega
    have hip : G.output i ≤ p.val := by
      change (G.output i).val ≤ v.val - 1
      omega
    have hf := ((observe_eq_iff _ _ _ _ _ _ _).mp h).1 (.inr p) hp
    exact congrFun hf ⟨i, hip⟩
  · subst v
    exact E.output_local i (S.original_observation_eq E h)

/-- The same raw support and original fields, with all outputs recovered
at the collector's last node using only permitted local observations. -/
def evaluation : Evaluation S.layout (S.Field (Symbol := Symbol) F) C raw where
  value := S.value E
  edge_local := by
    rintro (e | v) x y h
    · exact E.edge_local e (S.original_observation_eq E h)
    · funext i
      exact S.raw_eq_of_observation E (le_of_lt v.property.2) h i.val i.property
  output_local := fun i x y h =>
    S.raw_eq_of_observation E le_rfl h i (S.output_le i)

@[simp] theorem evaluation_original (x : C) (e : Edge) :
    (S.evaluation E).value x (.inl e) = E.value x e := rfl

@[simp] theorem evaluation_collector (x : C) (v : S.Link) (i : S.Prefix v.val) :
    (S.evaluation E).value x (.inr v) i = raw x.val i.val := rfl

/-- The collector uses exactly the indicated half-open interval. -/
theorem card_link : Fintype.card S.Link = S.last.val - S.first.val := by
  simp only [Link, ← mem_Ico, Fintype.card_coe, Fin.card_Ico]

/-- No collector edge is needed when all outputs are at one node. -/
theorem link_empty (h : S.first = S.last) : IsEmpty S.Link := by
  refine ⟨fun v => ?_⟩
  exact (not_lt_of_ge (h.ge.trans v.property.1)) v.property.2

/-- A coordinate is present on exactly the spine edges from its original
output node to the collector sink. -/
def linksAfterEquiv (i : Bit) : {v : S.Link // G.output i ≤ v.val} ≃
    ↥(Ico (G.output i) S.last) where
  toFun v := ⟨v.val.val, mem_Ico.mpr ⟨v.property, v.val.property.2⟩⟩
  invFun v := ⟨⟨v.val, le_trans (S.output_ge i) (mem_Ico.mp v.property).1,
    (mem_Ico.mp v.property).2⟩, (mem_Ico.mp v.property).1⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem card_links_after (i : Bit) :
    Fintype.card {v : S.Link // G.output i ≤ v.val} = S.last.val - (G.output i).val := by
  simpa only [Fintype.card_coe, Fin.card_Ico] using Fintype.card_congr (S.linksAfterEquiv i)

variable [Fintype Bit]

theorem prefix_card_le (v : Fin n) : Fintype.card (S.Prefix v) ≤ Fintype.card Bit :=
  Fintype.card_subtype_le _

/-- Exact collector volume: sum the delay of each output to the sink.
This retains the output positions instead of charging the whole group
on every collector edge. -/
theorem sum_prefix_card :
    ∑ v : S.Link, Fintype.card (S.Prefix v.val) =
      ∑ i : Bit, (S.last.val - (G.output i).val) := by
  simp_rw [Fintype.card_subtype, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simpa only [Fintype.card_subtype, card_eq_sum_ones, sum_filter] using S.card_links_after i

theorem sum_prefix_card_le :
    ∑ v : S.Link, Fintype.card (S.Prefix v.val) ≤
      Fintype.card Bit * (S.last.val - S.first.val) := by
  calc
    _ ≤ ∑ _v : S.Link, Fintype.card Bit := sum_le_sum fun v _ => S.prefix_card_le v.val
    _ = _ := by simp [S.card_link, mul_comm]

instance fieldFintype [Fintype Symbol] [∀ e, Fintype (F e)] :
    ∀ e, Fintype (S.Field (Symbol := Symbol) F e) := by
  intro e
  cases e <;> dsimp [Field] <;> infer_instance

theorem card_field_collector [Fintype Symbol] [∀ e, Fintype (F e)] (v : S.Link) :
    Fintype.card (S.Field (Symbol := Symbol) F (.inr v)) =
      Fintype.card Symbol ^ Fintype.card (S.Prefix v.val) := Fintype.card_fun

/-- The original capacities plus the exact binary prefix cost. -/
def cost (original : Edge → ℝ) : Edge ⊕ S.Link → ℝ :=
  Sum.elim original (fun v => Fintype.card (S.Prefix v.val))

theorem cost_nonneg (original : Edge → ℝ) (ho : ∀ e, 0 ≤ original e) :
    ∀ e, 0 ≤ S.cost original e := by
  rintro (e | v)
  · exact ho e
  · exact Nat.cast_nonneg _

theorem sum_cost [Fintype Edge] (original : Edge → ℝ) :
    ∑ e, S.cost original e = (∑ e, original e) +
      ∑ i : Bit, (S.last.val - (G.output i).val : ℕ) := by
  rw [Fintype.sum_sum_type]
  change (∑ e, original e) + (∑ v : S.Link, (Fintype.card (S.Prefix v.val) : ℝ)) = _
  congr 1
  exact_mod_cast S.sum_prefix_card

/-- Capacity and recovery at the sole sink, with the exact prefix payment.
The full joint support is counted; the support may correlate all coordinates. -/
theorem log_support_le_collected_cut {Bit : Type} [Fintype Bit] [Fintype Edge]
    {G : Layout (Fin n) Edge Bit} (S : Collector G) {F : Edge → Type}
    [∀ e, Fintype (F e)] {C : Set Input} [Nonempty C] {raw : Input → Bit → Bool}
    (E : Evaluation G F C raw) (original : Edge → ℝ)
    (ho : ∀ e, (Fintype.card (F e) : ℝ) ≤ (2 : ℝ) ^ original e)
    (U : Set (Fin n)) (B : Set Bit)
    (hvisible : ∀ v ∈ U, G.visible v ⊆ B) (hsink : S.last ∈ U) :
    Real.logb 2 (Fintype.card (Set.range (fun x : C => raw x.val))) ≤
      Fintype.card B +
        ∑ e : {e // S.layout.target e ∈ U ∧ S.layout.source e ∉ U}, S.cost original e.val := by
  apply (S.evaluation E).log_support_le_cut (S.cost original) ?_ U B hvisible (fun _ => hsink)
  rintro (e | v)
  · exact ho e
  · simp [Field, cost, Real.rpow_natCast]

end Collector
end
end LeanMachine.CausalFields

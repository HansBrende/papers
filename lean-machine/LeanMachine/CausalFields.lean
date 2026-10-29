import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic
import Mathlib.Order.RelClasses

/-! Local deterministic fields on a ranked acyclic network. The support
need not be a product set. Equality-based factorization is equivalent to
actual local functions, including arbitrary extensions off the support. -/

namespace LeanMachine.CausalFields

structure Layout (Node Edge Bit : Type*) where
  source : Edge → Node
  target : Edge → Node
  rank : Node → ℕ
  earlier : ∀ e, rank (source e) < rank (target e)
  visible : Node → Set Bit
  output : Bit → Node

variable {Node Edge Bit Input Symbol : Type*}
variable (G : Layout Node Edge Bit) (Field : Edge → Type*)

/-- Exactly the incoming fields and directly visible raw coordinates. -/
abbrev Observation (v : Node) :=
  ((e : {e // G.target e = v}) → Field e.val) × (G.visible v → Symbol)

def observe {C : Set Input} (raw : Input → Bit → Symbol)
    (value : C → (e : Edge) → Field e) (x : C) (v : Node) :
    Observation (Symbol := Symbol) G Field v :=
  (fun e => value x e.val, fun i => raw x.val i.val)

theorem observe_eq_iff {C : Set Input} (raw : Input → Bit → Symbol)
    (value : C → (e : Edge) → Field e) (x y : C) (v : Node) :
    observe G Field raw value x v = observe G Field raw value y v ↔
      (∀ e, G.target e = v → value x e = value y e) ∧
      Set.EqOn (raw x.val) (raw y.val) (G.visible v) := by
  constructor
  · intro h
    exact ⟨fun e he => congrFun (congrArg Prod.fst h) ⟨e, he⟩,
      fun i hi => congrFun (congrArg Prod.snd h) ⟨i, hi⟩⟩
  · rintro ⟨hf, hr⟩
    exact Prod.ext (funext fun e => hf e.val e.property) (funext fun i => hr i.property)

/-- Values on an arbitrary correctness set, with local rules expressed by
Mathlib's exact function-factorization predicate. -/
structure Evaluation (C : Set Input) (raw : Input → Bit → Symbol) where
  value : C → (e : Edge) → Field e
  edge_local : ∀ e, Function.FactorsThrough (fun x : C => value x e)
    (fun x => observe G Field raw value x (G.source e))
  output_local : ∀ i, Function.FactorsThrough (fun x : C => raw x.val i)
    (fun x => observe G Field raw value x (G.output i))

namespace Evaluation

variable {G Field} {C : Set Input} {raw : Input → Bit → Symbol}
variable (E : Evaluation G Field C raw)

/-- Conversely, ordinary local functions with the stated agreement give
the equality-based formulation, without any extra extension condition. -/
def ofRules (value : C → (e : Edge) → Field e)
    (edge : (e : Edge) → Observation (Symbol := Symbol) G Field (G.source e) → Field e)
    (output : (i : Bit) → Observation (Symbol := Symbol) G Field (G.output i) → Symbol)
    (hedge : ∀ e x, edge e (observe G Field raw value x (G.source e)) = value x e)
    (houtput : ∀ i x, output i (observe G Field raw value x (G.output i)) = raw x.val i) :
    Evaluation G Field C raw where
  value := value
  edge_local := fun e x y hxy => (hedge e x).symm.trans ((congrArg (edge e) hxy).trans (hedge e y))
  output_local := fun i x y hxy =>
    (houtput i x).symm.trans ((congrArg (output i) hxy).trans (houtput i y))

theorem edge_eq {x y : C} (e : Edge)
    (hf : ∀ f, G.target f = G.source e → E.value x f = E.value y f)
    (hr : Set.EqOn (raw x.val) (raw y.val) (G.visible (G.source e))) :
    E.value x e = E.value y e :=
  E.edge_local e ((observe_eq_iff G Field raw E.value x y _).mpr ⟨hf, hr⟩)

theorem output_eq {x y : C} (i : Bit)
    (hf : ∀ f, G.target f = G.output i → E.value x f = E.value y f)
    (hr : Set.EqOn (raw x.val) (raw y.val) (G.visible (G.output i))) :
    raw x.val i = raw y.val i :=
  E.output_local i ((observe_eq_iff G Field raw E.value x y _).mpr ⟨hf, hr⟩)

/-- The factorization premise supplies actual functions on all local
tuples. An attained support supplies values for otherwise unused tuples. -/
theorem exists_edge_rule [Nonempty C] (e : Edge) :
    ∃ f : Observation (Symbol := Symbol) G Field (G.source e) → Field e,
      ∀ x : C, f (observe G Field raw E.value x (G.source e)) = E.value x e := by
  let : Nonempty (Field e) := ⟨E.value (Classical.choice ‹Nonempty C›) e⟩
  obtain ⟨f, hf⟩ := (Function.factorsThrough_iff _).mp (E.edge_local e)
  exact ⟨f, fun x => (congrFun hf x).symm⟩

theorem exists_output_rule [Nonempty C] (i : Bit) :
    ∃ f : Observation (Symbol := Symbol) G Field (G.output i) → Symbol,
      ∀ x : C, f (observe G Field raw E.value x (G.output i)) = raw x.val i := by
  let : Nonempty Symbol := ⟨raw (Classical.choice ‹Nonempty C›).val i⟩
  obtain ⟨f, hf⟩ := (Function.factorsThrough_iff _).mp (E.output_local i)
  exact ⟨f, fun x => (congrFun hf x).symm⟩

/-- Every entering field is retained, including fields that re-enter after
an earlier departure. Raw data visible inside and those fields determine
all fields generated inside, with no independence assumption. -/
theorem value_eq_of_cut (U : Set Node) {x y : C}
    (hr : ∀ v ∈ U, Set.EqOn (raw x.val) (raw y.val) (G.visible v))
    (hc : ∀ e, G.target e ∈ U → G.source e ∉ U → E.value x e = E.value y e) :
    ∀ e, G.source e ∈ U → E.value x e = E.value y e := by
  have hv : ∀ v ∈ U, ∀ e, G.source e = v → E.value x e = E.value y e := by
    intro v
    induction v using (measure G.rank).wf.induction with
    | h v ih =>
      intro hv e he
      apply E.edge_eq e
      · intro f hf
        by_cases hs : G.source f ∈ U
        · apply ih (G.source f) ?_ hs f rfl
          change G.rank (G.source f) < G.rank v
          simpa only [hf, he] using G.earlier f
        · exact hc f (by simpa only [hf, he] using hv) hs
      · exact he ▸ hr v hv
  exact fun e he => hv (G.source e) he e rfl

theorem output_eq_of_cut (U : Set Node) {x y : C}
    (hr : ∀ v ∈ U, Set.EqOn (raw x.val) (raw y.val) (G.visible v))
    (hc : ∀ e, G.target e ∈ U → G.source e ∉ U → E.value x e = E.value y e)
    (i : Bit) (hi : G.output i ∈ U) : raw x.val i = raw y.val i := by
  apply E.output_eq i
  · intro e he
    by_cases hs : G.source e ∈ U
    · exact E.value_eq_of_cut U hr hc e hs
    · exact hc e (by simpa only [he] using hi) hs
  · exact hr _ hi

/-- Fixing the whole group's raw projection fixes every field of that
group, even when the original support correlates it with other groups. -/
theorem value_factorsThrough_raw :
    Function.FactorsThrough E.value (fun x : C => raw x.val) := by
  intro x y hxy
  funext e
  exact E.value_eq_of_cut Set.univ (fun _ _ _ _ => congrFun hxy _) (by simp) e (Set.mem_univ _)

/-- The complete entering-edge tuple, together with a chosen raw set. -/
def cutObservation (U : Set Node) (B : Set Bit) (x : C) :
    ((e : {e // G.target e ∈ U ∧ G.source e ∉ U}) → Field e.val) × (B → Symbol) :=
  (fun e => E.value x e.val, fun i => raw x.val i.val)

/-- If every requested output lies inside a cut, its entire raw projection
is determined by the cut tuple. The raw set may over-cover the visible data. -/
theorem raw_factorsThrough_cut (U : Set Node) (B : Set Bit)
    (hvisible : ∀ v ∈ U, G.visible v ⊆ B) (houtput : ∀ i, G.output i ∈ U) :
    Function.FactorsThrough (fun x : C => raw x.val) (E.cutObservation U B) := by
  intro x y hxy
  funext i
  apply E.output_eq_of_cut U ?_ ?_ i (houtput i)
  · intro v hv j hj
    exact congrFun (congrArg Prod.snd hxy) ⟨j, hvisible v hv hj⟩
  · intro e ht hs
    exact congrFun (congrArg Prod.fst hxy) ⟨e, ht, hs⟩

/-- Pulling a local evaluation back along a support map preserves exactly
the same field alphabets and local observations. -/
def comap {Input' : Type*} (D : Set Input') (raw' : Input' → Bit → Symbol)
    (lift : D → C) (hraw : ∀ x, raw (lift x).val = raw' x.val) :
    Evaluation G Field D raw' where
  value := fun x => E.value (lift x)
  edge_local := by
    intro e x y hxy
    obtain ⟨hf, hr⟩ := (observe_eq_iff G Field raw' _ x y _).mp hxy
    apply E.edge_eq e hf
    simpa only [hraw] using hr
  output_local := by
    intro i x y hxy
    obtain ⟨hf, hr⟩ := (observe_eq_iff G Field raw' _ x y _).mp hxy
    have he := E.output_eq i hf (by simpa only [hraw] using hr)
    simpa only [hraw] using he

/-- Evaluate directly on the joint projected support, retaining the exact
local rules. A choice of extension does not assume product support. -/
noncomputable def projected : Evaluation G Field
    (Set.range (fun x : C => raw x.val)) (fun y => y) :=
  E.comap _ _ (fun y => Classical.choose y.property)
    (fun y => Classical.choose_spec y.property)

theorem projected_agrees (x : C) :
    E.projected.value ⟨raw x.val, ⟨x, rfl⟩⟩ = E.value x :=
  E.value_factorsThrough_raw (Classical.choose_spec (show raw x.val ∈
    Set.range (fun x : C => raw x.val) from ⟨x, rfl⟩))

end Evaluation
end LeanMachine.CausalFields

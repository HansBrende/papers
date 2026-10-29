import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic

/-!
# Recovery from paid causal dependencies

Local determinism on an arbitrary correctness set gives functional recovery
from revealed records and the complete surviving raw-source cone. A paid root
is still retained: payment blocks a dependency at its lower endpoint, not the
root or its own direct reads. No alphabet, linearity or independence assumption
is needed.
-/

namespace LeanMachine.CausalRecovery

variable {Input Ω Raw Value : Type*}

/-- A complete backward cone retains its root, including a paid root, and
follows every edge whose lower endpoint has not been paid. -/
inductive Ancestor (parents : ℕ → Finset ℕ) (Γ : Set ℕ) (root : ℕ) : ℕ → Prop
  | root : Ancestor parents Γ root root
  | step {v u} : Ancestor parents Γ root v → u ∈ parents v → u ∉ Γ →
      Ancestor parents Γ root u

/-- All direct raw reads of the complete surviving cone. A read set may be
empty, a singleton, or contain several coordinates. -/
def sourceCone (parents : ℕ → Finset ℕ) (reads : ℕ → Set Ω)
    (Γ : Set ℕ) (root : ℕ) : Set Ω :=
  {z | ∃ t, Ancestor parents Γ root t ∧ z ∈ reads t}

variable {parents : ℕ → Finset ℕ} {reads : ℕ → Set Ω} {Γ : Set ℕ} {T : ℕ}

theorem Ancestor.trans {r t u : ℕ} (hrt : Ancestor parents Γ r t)
    (htu : Ancestor parents Γ t u) : Ancestor parents Γ r u := by
  induction htu with
  | root => exact hrt
  | step _ hp hΓ ih => exact ih.step hp hΓ

/-- Finite-horizon causality suffices; no claim about later times is required. -/
theorem Ancestor.le
    (hearlier : ∀ t ≤ T, ∀ u ∈ parents t, u < t)
    {r t : ℕ} (hr : r ≤ T) (h : Ancestor parents Γ r t) : t ≤ r := by
  induction h with
  | root => exact le_rfl
  | step _ hp _ ih => exact (hearlier _ (ih.trans hr) _ hp).le.trans ih

theorem reads_subset_sourceCone (t : ℕ) :
    reads t ⊆ sourceCone parents reads Γ t :=
  fun _ hz => ⟨t, .root, hz⟩

theorem sourceCone_subset_of_ancestor {r t : ℕ} (h : Ancestor parents Γ r t) :
    sourceCone parents reads Γ t ⊆ sourceCone parents reads Γ r := by
  rintro z ⟨u, hu, hz⟩
  exact ⟨u, h.trans hu, hz⟩

/-- Containment on each surviving edge propagates to the full source cone. -/
theorem sourceCone_subset (A : ℕ → Set Ω)
    (hearlier : ∀ t ≤ T, ∀ u ∈ parents t, u < t)
    (hreads : ∀ t ≤ T, reads t ⊆ A t)
    (hclosed : ∀ t ≤ T, ∀ u ∈ parents t, u ∉ Γ → A u ⊆ A t)
    {root : ℕ} (hr : root ≤ T) :
    sourceCone parents reads Γ root ⊆ A root := by
  rintro z ⟨t, ht, hz⟩
  have hA : A t ⊆ A root := by
    clear hz
    induction ht with
    | root => exact Set.Subset.rfl
    | step h hp hΓ ih =>
        exact (hclosed _ ((h.le hearlier hr).trans hr) _ hp hΓ).trans ih
  exact hA (hreads t ((ht.le hearlier hr).trans hr) hz)

/-- The current record is determined by its direct raw reads and all parent
records, for inputs in the correctness set. This is a local premise, not an
assumption of recovery from a global source set. -/
def LocallyDetermined (parents : ℕ → Finset ℕ) (reads : ℕ → Set Ω) (T : ℕ)
    (C : Set Input) (raw : Input → Ω → Raw) (record : Input → ℕ → Value) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, ∀ t ≤ T,
    Set.EqOn (raw a) (raw b) (reads t) →
    (∀ u ∈ parents t, record a u = record b u) → record a t = record b t

variable {C : Set Input} {raw : Input → Ω → Raw} {record : Input → ℕ → Value}

/-- Strong induction evaluates every unpaid parent. The root is always
evaluated by its local rule, even if its record was also revealed. -/
theorem record_eq_of_sourceCone
    (hearlier : ∀ t ≤ T, ∀ u ∈ parents t, u < t)
    (hlocal : LocallyDetermined parents reads T C raw record)
    {a b : Input} (ha : a ∈ C) (hb : b ∈ C)
    (hpaid : Set.EqOn (record a) (record b) Γ)
    (root : ℕ) (hr : root ≤ T)
    (hraw : Set.EqOn (raw a) (raw b) (sourceCone parents reads Γ root)) :
    record a root = record b root := by
  induction root using Nat.strong_induction_on with
  | h t ih =>
    apply hlocal a ha b hb t hr
    · exact hraw.mono (reads_subset_sourceCone t)
    · intro u hu
      by_cases hΓ : u ∈ Γ
      · exact hpaid hΓ
      · exact ih u (hearlier t hr u hu) ((hearlier t hr u hu).le.trans hr)
          (hraw.mono (sourceCone_subset_of_ancestor (Ancestor.root.step hu hΓ)))

/-- A convenient adapter: any sets closed along unpaid edges suffice. The
same paid transcript works at every root; the raw set may vary with the root. -/
theorem record_eq_of_closed_sources (A : ℕ → Set Ω)
    (hearlier : ∀ t ≤ T, ∀ u ∈ parents t, u < t)
    (hlocal : LocallyDetermined parents reads T C raw record)
    (hreads : ∀ t ≤ T, reads t ⊆ A t)
    (hclosed : ∀ t ≤ T, ∀ u ∈ parents t, u ∉ Γ → A u ⊆ A t)
    {a b : Input} (ha : a ∈ C) (hb : b ∈ C)
    (hpaid : Set.EqOn (record a) (record b) Γ)
    (root : ℕ) (hr : root ≤ T) (hraw : Set.EqOn (raw a) (raw b) (A root)) :
    record a root = record b root :=
  record_eq_of_sourceCone hearlier hlocal ha hb hpaid root hr
    (hraw.mono (sourceCone_subset A hearlier hreads hclosed hr))

/-- The common paid transcript and the raw coordinates in `S`. -/
def observation (record : Input → ℕ → Value) (raw : Input → Ω → Raw)
    (Γ : Set ℕ) (S : Set Ω) (a : Input) : (Γ → Value) × (S → Raw) :=
  (fun t => record a t, fun z => raw a z)

/-- Equality-based determination supplies an actual decoder on all observations,
using Mathlib's existing factorization theorem. Nonemptiness only supplies an
arbitrary value for observations not realized on the correctness set. -/
theorem exists_decoder [Nonempty Value] (S : Set Ω) (root : ℕ)
    (hrec : ∀ a ∈ C, ∀ b ∈ C,
      Set.EqOn (record a) (record b) Γ → Set.EqOn (raw a) (raw b) S →
      record a root = record b root) :
    ∃ decode : ((Γ → Value) × (S → Raw)) → Value,
      ∀ a ∈ C, decode (observation record raw Γ S a) = record a root := by
  have hf : Function.FactorsThrough (fun a : C => record a.val root)
      (fun a : C => observation record raw Γ S a.val) := by
    intro a b hab
    apply hrec a a.property b b.property
    · intro t ht
      exact congrFun (congrArg Prod.fst hab) ⟨t, ht⟩
    · intro z hz
      exact congrFun (congrArg Prod.snd hab) ⟨z, hz⟩
  obtain ⟨decode, hd⟩ := (Function.factorsThrough_iff _).mp hf
  exact ⟨decode, fun a ha => (congrFun hd ⟨a, ha⟩).symm⟩

end LeanMachine.CausalRecovery

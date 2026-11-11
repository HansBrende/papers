import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Basic

/-! Total chronological programs with one private input block per owner.
The exported fields are exactly earlier values consumed by another owner.
All local rules are actual total functions. No rectangular-fibre or global
recovery premise is part of the program. Field alphabets may vary by date. -/

namespace LeanMachine

structure OwnerProgram (Owner : Type*) (Raw : Owner → Type*) (Value : ℕ → Type*) where
  owner : ℕ → Owner
  parents : ℕ → Finset ℕ
  earlier : ∀ t, ∀ u ∈ parents t, u < t
  rule : (t : ℕ) → Raw (owner t) → ((u : parents t) → Value u.val) → Value t

namespace OwnerProgram

variable {O : Type*} {R : O → Type*} {V : ℕ → Type*} (p : OwnerProgram O R V)

/-- Actual evaluation of the given total local maps. -/
def eval (p : OwnerProgram O R V) (x : (o : O) → R o) (t : ℕ) : V t :=
  p.rule t (x (p.owner t)) (fun u => eval p x u.val)
termination_by t
decreasing_by exact p.earlier t u.val u.property

theorem eval_eq (x : (o : O) → R o) (t : ℕ) :
    p.eval x t = p.rule t (x (p.owner t)) (fun u => p.eval x u.val) := by
  rw [eval]

/-- A field is paid once if any later operation uses it under a different owner. -/
noncomputable def exports (T : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range T).filter (fun u =>
    ∃ t < T, u ∈ p.parents t ∧ p.owner u ≠ p.owner t)

noncomputable def transcript (T : ℕ) (x : (o : O) → R o) :
    (u : p.exports T) → V u.val := fun u => p.eval x u.val

theorem mem_exports {T t u : ℕ} (ht : t < T) (hu : u ∈ p.parents t)
    (hne : p.owner u ≠ p.owner t) : u ∈ p.exports T := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((p.earlier t u hu).trans ht),
    t, ht, hu, hne⟩

/-- Mixing witnesses independently at each owner preserves every local field
relative to the witness of that field's owner, when all witnesses agree on
the actual paid transcript. -/
theorem eval_mix {T : ℕ} (xs : O → ((o : O) → R o))
    (z : (u : p.exports T) → V u.val)
    (hz : ∀ o, p.transcript T (xs o) = z) (t : ℕ) (ht : t < T) :
    p.eval (fun o => xs o o) t = p.eval (xs (p.owner t)) t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    rw [p.eval_eq, p.eval_eq]
    congr 1
    funext u
    have hu := p.earlier t u.val u.property
    have he := ih u.val hu (hu.trans ht)
    by_cases ho : p.owner u.val = p.owner t
    · simpa only [ho] using he
    · have hm := p.mem_exports ht u.property ho
      have h₁ := congrFun (hz (p.owner u.val)) ⟨u.val, hm⟩
      have h₂ := congrFun (hz (p.owner t)) ⟨u.val, hm⟩
      exact he.trans (h₁.trans h₂.symm)

/-- Full transcript fibres are products over the original owner blocks.
This concerns the full domain, not the possibly correlated correct subfamily. -/
theorem transcript_mix {T : ℕ} (xs : O → ((o : O) → R o))
    (z : (u : p.exports T) → V u.val)
    (hz : ∀ o, p.transcript T (xs o) = z) :
    p.transcript T (fun o => xs o o) = z := by
  classical
  funext u
  have ht : u.val < T := Finset.mem_range.mp (Finset.mem_filter.mp u.property).1
  exact (p.eval_mix xs z hz u.val ht).trans (congrFun (hz (p.owner u.val)) u)

/-- A field is determined by its owner's raw block and the one joint transcript. -/
theorem eval_eq_of_owner_transcript {T : ℕ} {x y : (o : O) → R o}
    (hz : p.transcript T x = p.transcript T y)
    (o : O) (hraw : x o = y o) (t : ℕ) (ht : t < T) (ho : p.owner t = o) :
    p.eval x t = p.eval y t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    rw [p.eval_eq, p.eval_eq]
    have hr : x (p.owner t) = y (p.owner t) := by cases ho; exact hraw
    rw [hr]
    congr 1
    funext u
    have hu := p.earlier t u.val u.property
    by_cases hop : p.owner u.val = p.owner t
    · exact ih u.val hu (hu.trans ht) (hop.trans ho)
    · exact congrFun hz ⟨u.val, p.mem_exports ht u.property hop⟩

/-- The common local function exists on all observations, including those that
are never attained. No correctness of mixed inputs is asserted. -/
theorem eval_factorsThrough (T t : ℕ) (ht : t < T) :
    (fun x : (o : O) → R o => p.eval x t).FactorsThrough
      (fun x => (p.transcript T x, x (p.owner t))) := by
  intro x y he
  exact p.eval_eq_of_owner_transcript (congrArg Prod.fst he) (p.owner t)
    (congrArg Prod.snd he) t ht rfl

end OwnerProgram
end LeanMachine

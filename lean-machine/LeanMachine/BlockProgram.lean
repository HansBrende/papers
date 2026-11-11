import LeanMachine.OwnerProgram
import Mathlib.Tactic

/-! A fixed finite word of producer operations, extended by arbitrary total
operations beyond its horizon. A step reads its complete resident state,
its owner's raw input, and a specified set of earlier block dates. It emits
a new resident state and one dated value (a dummy constant for non-writes).
The causal field program separates state from block values, so exporting a
block never pays the resident state again. -/

namespace LeanMachine

structure BlockProgram (Owner : Type*) (Raw : Owner → Type*) (State Block : Type*) where
  initial : State
  constant : Block
  owner : ℕ → Owner
  reads : ℕ → Finset ℕ
  earlier : ∀ t, ∀ j ∈ reads t, j < t
  update : (t : ℕ) → State → Raw (owner t) → (reads t → Block) → State × Block

namespace BlockProgram

open Finset
variable {O S A : Type*} {R : O → Type*} (p : BlockProgram O R S A)

/-- Literal chronological evaluation. The retained history is mathematical
bookkeeping for dated reads, not extra resident state. -/
def eval (p : BlockProgram O R S A) (x : (o : O) → R o) (t : ℕ) : S × A :=
  p.update t (if h : t = 0 then p.initial else (eval p x (t - 1)).1)
    (x (p.owner t)) (fun j => (eval p x j.val).2)
termination_by t
decreasing_by
  · omega
  · exact p.earlier t j.val j.property

theorem eval_eq (x : (o : O) → R o) (t : ℕ) :
    p.eval x t = p.update t
      (if t = 0 then p.initial else (p.eval x (t - 1)).1)
      (x (p.owner t)) (fun j => (p.eval x j.val).2) := by
  rw [eval]
  split_ifs <;> rfl

/-- The state field is even and the dated block field odd. -/
def fieldParents (t : ℕ) : Finset ℕ :=
  (if t = 0 then ∅ else {2 * (t - 1)}) ∪ (p.reads t).image (fun j => 2 * j + 1)

theorem state_parent_mem {t : ℕ} (ht : t ≠ 0) : 2 * (t - 1) ∈ p.fieldParents t := by
  simp [fieldParents, ht]

theorem read_parent_mem {t j : ℕ} (hj : j ∈ p.reads t) : 2 * j + 1 ∈ p.fieldParents t := by
  exact mem_union_right _ (mem_image.mpr ⟨j, hj, rfl⟩)

theorem field_parent_earlier {t u : ℕ} (hu : u ∈ p.fieldParents t) : u < 2 * t := by
  rcases mem_union.mp hu with hs | hr
  · by_cases ht : t = 0
    · simp [ht] at hs
    · have he : u = 2 * (t - 1) := by simpa only [ht, ite_false, mem_singleton] using hs
      omega
  · obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
    have h := p.earlier t j hj
    omega

def fieldUpdate (t : ℕ) (raw : R (p.owner t)) (v : p.fieldParents t → S × A) : S × A :=
  p.update t
    (if h : t = 0 then p.initial else (v ⟨2 * (t - 1), p.state_parent_mem h⟩).1)
    raw (fun j => (v ⟨2 * j.val + 1, p.read_parent_mem j.property⟩).2)

/-- Normalizing the unused component makes field capacities independent:
state nodes carry a fixed block constant, and block nodes a fixed state. -/
def fields : OwnerProgram O R (fun _ => S × A) where
  owner n := p.owner (n / 2)
  parents n := p.fieldParents (n / 2)
  earlier n u hu := by
    have h := p.field_parent_earlier hu
    omega
  rule n raw v :=
    let result := p.fieldUpdate (n / 2) raw v
    if n % 2 = 0 then (result.1, p.constant) else (p.initial, result.2)

/-- The field graph evaluates exactly the given block program. -/
theorem fields_eval (x : (o : O) → R o) (t : ℕ) :
    p.fields.eval x (2 * t) = ((p.eval x t).1, p.constant) ∧
      p.fields.eval x (2 * t + 1) = (p.initial, (p.eval x t).2) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    have hstate : (if h : t = 0 then p.initial else
        (p.fields.eval x (2 * (t - 1))).1) =
        (if t = 0 then p.initial else (p.eval x (t - 1)).1) := by
      split_ifs with ht
      · rfl
      · have hh := (ih (t - 1) (by omega)).1
        rw [hh]
    have hread : (fun j : p.reads t => (p.fields.eval x (2 * j.val + 1)).2) =
        fun j : p.reads t => (p.eval x j.val).2 := by
      funext j
      rw [(ih j.val (p.earlier t j.val j.property)).2]
    have hu : p.fieldUpdate t (x (p.owner t))
        (fun u => p.fields.eval x u.val) = p.eval x t := by
      rw [p.eval_eq]
      unfold fieldUpdate
      rw [hstate, hread]
    constructor
    · rw [p.fields.eval_eq]
      have hd : 2 * t / 2 = t := by omega
      have hm : 2 * t % 2 = 0 := by omega
      let F (j : ℕ) := p.fieldUpdate j (x (p.owner j)) (fun u => p.fields.eval x u.val)
      change (if 2 * t % 2 = 0 then ((F (2 * t / 2)).1, p.constant)
        else (p.initial, (F (2 * t / 2)).2)) = _
      rw [ite_eq_left hm, hd]
      exact congrArg (fun v : S × A => (v.1, p.constant)) hu
    · rw [p.fields.eval_eq]
      have hd : (2 * t + 1) / 2 = t := by omega
      have hm : (2 * t + 1) % 2 ≠ 0 := by omega
      let F (j : ℕ) := p.fieldUpdate j (x (p.owner j)) (fun u => p.fields.eval x u.val)
      change (if (2 * t + 1) % 2 = 0 then ((F ((2 * t + 1) / 2)).1, p.constant)
        else (p.initial, (F ((2 * t + 1) / 2)).2)) = _
      rw [ite_eq_right hm, hd]
      exact congrArg (fun v : S × A => (p.initial, v.2)) hu

end BlockProgram
end LeanMachine

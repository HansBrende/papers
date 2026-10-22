import Mathlib.Tactic

/-! Generic bounded-call composition. The machine supplies actual local
transitions; this file does not attach a cost to abstract list operations. -/
namespace FixedTapeCompiler.OperationalTrace

variable {C : Type*}

def run (step : C → C) : ℕ → C → C
  | 0,c => c
  | n+1,c => run step n (step c)

inductive Trace (step : C → C) (active : C → Prop) : ℕ → C → C → Prop
  | refl (c : C) : Trace step active 0 c c
  | cons {n c d} : active c → Trace step active n (step c) d → Trace step active (n+1) c d

theorem run_fixed (step : C → C) (c : C) (h : step c = c) (n : ℕ) :
    run step n c = c := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [run,h] using ih

theorem prune (step : C → C) (active : C → Prop)
    (fixed : ∀ c, ¬active c → step c = c) (n : ℕ) (c : C) :
    ∃ t ≤ n, Trace step active t c (run step n c) := by
  classical
  induction n generalizing c with
  | zero => exact ⟨0,le_rfl,.refl c⟩
  | succ n ih =>
    by_cases h : active c
    · rcases ih (step c) with ⟨t,ht,tr⟩
      exact ⟨t+1,by omega,.cons h tr⟩
    · rw [run_fixed step c (fixed c h)]
      exact ⟨0,by omega,.refl c⟩

/-- Embed an active subroutine in a caller which can react immediately at
its return state. All steps counted here are caller-machine transitions. -/
theorem lift {D : Type*} {step : C → C} {active : C → Prop}
    (outer : D → D) (embed : C → D)
    (sim : ∀ c, active c → outer (embed c) = embed (step c))
    {n : ℕ} {c d : C} (h : Trace step active n c d) :
    run outer n (embed c) = embed d := by
  induction h with
  | refl => rfl
  | cons ha tr ih => simpa only [run,sim _ ha] using ih

theorem run_add (step : C → C) (n k : ℕ) (c : C) :
    run step (n+k) c = run step k (run step n c) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih => simp only [Nat.succ_add,run,ih]

end FixedTapeCompiler.OperationalTrace

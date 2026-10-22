import FixedTapeCompiler.OperationalTrace

namespace FixedTapeCompiler.OperationalTrace
set_option autoImplicit false
variable {C : Type*} {step : C → C} {active : C → Prop} {n : ℕ} {c d : C}

theorem trace_run (h:Trace step active n c d) : run step n c=d := by
  induction h with
  | refl => rfl
  | cons _ _ ih => exact ih

theorem take_trace (h:Trace step active n c d) (m : ℕ) (hm:m≤n) :
    Trace step active m c (run step m c) := by
  induction h generalizing m with
  | refl =>
    have he:m=0:=by omega
    subst m
    exact .refl _
  | cons ha tr ih =>
    cases m with
    | zero => exact .refl _
    | succ m => exact .cons ha (ih m (by omega))

end FixedTapeCompiler.OperationalTrace

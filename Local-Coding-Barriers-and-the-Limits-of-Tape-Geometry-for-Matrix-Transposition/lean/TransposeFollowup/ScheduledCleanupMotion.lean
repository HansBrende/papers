import TransposeFollowup.ScheduledBankCleanup
import TransposeFollowup.ScheduledMotion

/-! Exact all-prefix geometry of the already checked cleanup passes. -/
namespace TransposeFollowup.ScheduledBankCleanup
open FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
set_option autoImplicit false
variable {M : Type*}

def path (W : ℕ) (t : Fin 2) (n : ℕ) : ℤ :=
  (if t=1 then ((min n W : ℕ) : ℤ)-(min (n-W) W : ℕ) else 0)-
    if t=0 then (n-2*W : ℕ) else 0

theorem schedule_position (P W : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (n : ℕ) (hn : n≤ticks P W) (t : Fin 2) :
    (trajectory (schedule P W) w c n).work.pos t=c.work.pos t+path W t n := by
  have hr (p : Fin 2) (d : NativeIO.Config (Fin 2) M) (m : ℕ) :
      (trajectory (fun _ => action p ⟨none,.left⟩) w d m).work.pos t=
        d.work.pos t+(-(if t=p then (m : ℤ) else 0)) := by
    by_cases ht : t=p <;> simpa [rewind,ht,sub_eq_add_neg] using rewind_position p w d m t
  have hi := append_position _ _ W P w t _ _
    (fun d m _ => hr 1 d m) (fun d m _ => hr 0 d m)
  have ho := append_position _ _ W (W+P) w t _ _
    (fun d m _ => erase_position 1 w d m t) hi
  have h := ho c n hn
  change (trajectory (schedule P W) w c n).work.pos t=_ at h
  fin_cases t <;>
    simpa [path,Nat.sub_sub,two_mul,sub_eq_add_neg,add_assoc] using h

theorem scratch_bounds (W n : ℕ) : 0≤path W 1 n ∧ path W 1 n≤W := by
  have h : min (n-W) W ≤ min n W := min_le_min_right W (Nat.sub_le _ _)
  have hu := Nat.min_le_right n W
  simp only [path,one_ne_zero,ite_true,ite_false]
  constructor <;> omega

end TransposeFollowup.ScheduledBankCleanup

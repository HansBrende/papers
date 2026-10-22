import TransposeFollowup.RawBankProgram
import TransposeFollowup.ScheduledRawIOMotion
import Transpose.Tape.MStarTM

/-! The actual whole-word native head paths, including raw IO, every
stage/reset, and the frozen halted tail. Internal stage excursions are
added at their paid public start times. -/
namespace TransposeFollowup.RawBankProgram
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (State)
set_option autoImplicit false

structure Motion (B : Body) where
  path : Fin 2 → ℕ → ℤ
  position : ∀ w c n, n ≤ B.cost → ∀ t,
    (trajectory B.code w c n).work.pos t = c.work.pos t+path t n
  after : ∀ t n, B.cost ≤ n → path t n=0

theorem motion_frozen (B : Body) (M : Motion B) (t : Fin 2) (n : ℕ) :
    M.path t (min n B.cost)=M.path t n := by
  by_cases hn : n ≤ B.cost
  · rw [Nat.min_eq_left hn]
  · rw [Nat.min_eq_right (by omega),M.after t _ le_rfl,M.after t n (by omega)]

def path (P : ℕ) (B : Body) (M : Motion B) (t : Fin 2) (n : ℕ) : ℤ :=
  M.path t (n-4*P)+
    if t=0 then ((min ((n+1)/3) P : ℕ) : ℤ)-(min (n-3*P) P : ℕ)+
      (min ((n-(4*P+B.cost))/3) P : ℕ) else 0

theorem schedule_position (P : ℕ) (B : Body) (M : Motion B)
    (w : List Bool) (c : State) (n : ℕ) (hn : n ≤ ticks P B) (t : Fin 2) :
    (trajectory (schedule P B) w c n).work.pos t = c.work.pos t+path P B M t n := by
  have hr (d : State) (m : ℕ) :
      (trajectory (fun _ => action 0 ⟨none,.left⟩) w d m).work.pos t =
        d.work.pos t+(-(if t=0 then (m : ℤ) else 0)) := by
    by_cases ht : t=0 <;> simpa [rewind,ht,sub_eq_add_neg] using rewind_position 0 w d m t
  have h3 := append_position _ _ (B.cost) (3*P) w t _ _
    (fun d m hm => M.position w d m hm t)
    (fun d m _ => ScheduledRawOutput.schedule_position w d m t)
  have h2 := append_position _ _ P (B.cost+3*P) w t _ _ (fun d m _ => hr d m) h3
  have h1 := append_position _ _ (3*P) (P+(B.cost+3*P)) w t _ _
    (fun d m _ => ScheduledRawInput.schedule_position w d m t) h2
  have h := h1 c n hn
  change (trajectory (schedule P B) w c n).work.pos t = _ at h
  have hload : (min n (3*P)+1)/3 = min ((n+1)/3) P := by omega
  have hstart : n-3*P-P = n-4*P := by omega
  have hout : (n-4*P-B.cost)/3 =
      min ((n-(4*P+B.cost))/3) P := by unfold ticks at hn; omega
  simp only [hload,hstart,hout,motion_frozen B M] at h
  fin_cases t <;>
    simpa [path,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using h

theorem path_after (P : ℕ) (B : Body) (M : Motion B) (t : Fin 2)
    (n : ℕ) (hn : ticks P B ≤ n) : path P B M t n = if t=0 then (P : ℤ) else 0 := by
  have ht : ticks P B = 7*P+B.cost := by unfold ticks; omega
  have hword : M.path t (n-4*P) = 0 :=
    M.after t _ (by omega)
  have hload : min ((n+1)/3) P = P := by omega
  have hrewind : min (n-3*P) P = P := by omega
  have hout : min ((n-(4*P+B.cost))/3) P = P := by omega
  simp only [path,hword,hload,hrewind,hout,sub_self,zero_add]

theorem path_frozen (P : ℕ) (B : Body) (M : Motion B) (t : Fin 2) (n : ℕ) :
    path P B M t (min n (ticks P B)) = path P B M t n := by
  by_cases hn : n ≤ ticks P B
  · rw [Nat.min_eq_left hn]
  · rw [Nat.min_eq_right (by omega),path_after P B M t _ le_rfl,path_after P B M t n (by omega)]

theorem workTraj_position (P : ℕ) (B : Body) (M : Motion B) (hc : Correct P B)
    (w : List Bool) (n : ℕ) (t : Fin 2) :
    Transpose.Tape.workTraj (machine P B) w n ((encoding P B).port t) = path P B M t n := by
  let m := min n (ticks P B)
  have hm : m ≤ ticks P B := Nat.min_le_right _ _
  have h := native_prefix (encoding P B) (schedule P B) w RawMaskedStride.initial
    (fun i _ => schedule_active P B hc.active i _) m hm
  have hb : (lift (⟨0,by omega⟩ : Fin (ticks P B+1)) RawMaskedStride.initial).denote
      (encoding P B) (program (schedule P B) (ticks P B)) = Transpose.init (machine P B) :=
    NativeIO.blank_denote (encoding P B) _ _ (NativeMicrocode.initialEncoding_start _)
  rw [hb] at h
  have hp := congrArg (fun d => d.workPos ((encoding P B).port t))
    ((Transpose.Tape.Impl.stepN_init_eq_some_iff m _).mp h).2
  change Transpose.Tape.workTraj (machine P B) w m _ = _ at hp
  have hx : Transpose.Tape.workTraj (machine P B) w m ((encoding P B).port t) = path P B M t m := by
    refine hp.trans ?_
    simpa only [NativeIO.Config.denote,lift,Equiv.symm_apply_apply,RawMaskedStride.initial,
      NativeMicrocode.blankConfig,zero_add] using schedule_position P B M w RawMaskedStride.initial m hm t
  have hf := congrFun (Transpose.Tape.Impl.workTraj_frozen (native_halts P B hc w) ((encoding P B).port t)) n
  exact hf.symm.trans (hx.trans (path_frozen P B M t n))

end TransposeFollowup.RawBankProgram

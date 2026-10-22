import TransposeFollowup.BackwardMaskedStride
import TransposeFollowup.BankReversalMotion
import TransposeFollowup.MaskedStrideWordMotion

/-! Backward scans reuse the exact paths of their three paid stages.
No new movement or uncharged change of coordinates is introduced. -/
namespace TransposeFollowup.BackwardMaskedStride
open Classical FixedTapeCompiler ScheduledNativeIO
open MaskedStrideCell (State)
set_option autoImplicit false

def path (P S : ℕ) (h : Fin 2) (n : ℕ) : ℤ :=
  BankReversal.path P h n+
    MaskedStrideBankStage.path P S h (n-BankReversal.ticks P)+
    BankReversal.path P h (n-BankReversal.ticks P-MaskedStrideBankStage.ticks P S)

theorem schedule_position (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ}
    (hS : 0<S) (w : List Bool) (c : State) (n : ℕ) (hn : n≤ticks P S) (h : Fin 2) :
    (trajectory (schedule isPrefix mask P S) w c n).work.pos h=c.work.pos h+path P S h n := by
  have htail := append_position _ _ (MaskedStrideBankStage.ticks P S) (BankReversal.ticks P) w h _ _
    (fun d m hm => MaskedStrideBankStage.schedule_position isPrefix (reflected P mask) P hS w d m hm h)
    (fun d m hm => BankReversal.schedule_position P w d m hm h)
  have hall := append_position _ _ (BankReversal.ticks P)
    (MaskedStrideBankStage.ticks P S+BankReversal.ticks P) w h _ _
    (fun d m hm => BankReversal.schedule_position P w d m hm h) htail c n hn
  simpa only [schedule,path,BankReversal.path_frozen,MaskedStrideBankStage.path_frozen,add_assoc] using hall

theorem path_zero (P : ℕ) {S : ℕ} (hS : 0<S) (h : Fin 2) : path P S h 0=0 := by
  simp only [path,Nat.zero_sub,BankReversal.path_zero,MaskedStrideBankStage.path_zero P hS,add_zero]

theorem path_after (P : ℕ) {S : ℕ} (hS : 0<S) (h : Fin 2) (n : ℕ) (hn : ticks P S≤n) :
    path P S h n=0 := by
  unfold ticks at hn
  rw [path,BankReversal.path_after P h n (by omega),
    MaskedStrideBankStage.path_after P hS h _ (by omega),
    BankReversal.path_after P h _ (by omega)]
  rfl

theorem path_frozen (P : ℕ) {S : ℕ} (hS : 0<S) (h : Fin 2) (n : ℕ) :
    path P S h (min n (ticks P S))=path P S h n := by
  by_cases hn : n≤ticks P S
  · rw [Nat.min_eq_left hn]
  · rw [Nat.min_eq_right (by omega),path_after P hS h _ le_rfl,path_after P hS h n (by omega)]

end TransposeFollowup.BackwardMaskedStride

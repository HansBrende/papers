import TransposeFollowup.MaskedStrideWord
import TransposeFollowup.MaskedStrideMotion
import TransposeFollowup.ScheduledMotion

/-! Exact head displacements through the internal stages and their finite
compositions. Each stage path returns to zero after its paid reset, so a
word is a sum of delayed stage excursions on the same physical heads. -/
namespace TransposeFollowup.MaskedStrideBankStage
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (State)
set_option autoImplicit false

def path (P S : ℕ) (t : Fin 2) (n : ℕ) : ℤ :=
  if t=0 then (MaskedStrideScan.bankPosition P S (min n (MaskedStrideScan.ticks P S)) : ℕ)-
    (min (n-MaskedStrideScan.ticks P S-S-S) P : ℕ)
  else MaskedStrideScan.scratchPosition P S (min n (MaskedStrideScan.ticks P S))+
    (min (n-MaskedStrideScan.ticks P S) S : ℕ)-(min (n-MaskedStrideScan.ticks P S-S) S : ℕ)

theorem schedule_position (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ}
    (hS : 0 < S) (w : List Bool) (c : State) (n : ℕ) (hn : n ≤ ticks P S) (t : Fin 2) :
    (trajectory (schedule isPrefix mask P S) w c n).work.pos t = c.work.pos t+path P S t n := by
  have hr (p : Fin 2) (d : State) (m : ℕ) :
      (trajectory (fun _ => action p ⟨none,.left⟩) w d m).work.pos t =
        d.work.pos t+(-(if t=p then (m : ℤ) else 0)) := by
    by_cases ht : t=p <;> simpa [rewind,ht,sub_eq_add_neg] using rewind_position p w d m t
  have he (d : State) (m : ℕ) :
      (trajectory (fun _ => action 1 ⟨some .blank,.right⟩) w d m).work.pos t =
        d.work.pos t+(if t=1 then (m : ℤ) else 0) := by
    by_cases ht : t=1 <;> simpa [erase,ht] using erase_position 1 w d m t
  have hp (d : State) (m : ℕ) :
      (trajectory (MaskedStrideScan.schedule isPrefix mask P S) w d m).work.pos t =
        d.work.pos t+(if t=0 then (MaskedStrideScan.bankPosition P S m : ℤ)
          else MaskedStrideScan.scratchPosition P S m) := by
    have h := MaskedStrideScan.schedule_positions isPrefix mask P hS w d m
    fin_cases t
    · simpa using h.1
    · simpa using h.2
  have h3 := append_position _ _ S P w t _ _ (fun d m _ => hr 1 d m) (fun d m _ => hr 0 d m)
  have h2 := append_position _ _ S (S+P) w t _ _ (fun d m _ => he d m) h3
  have h1 := append_position _ _ (MaskedStrideScan.ticks P S) (S+(S+P)) w t _ _
    (fun d m _ => hp d m) h2
  have h := h1 c n hn
  change (trajectory (schedule isPrefix mask P S) w c n).work.pos t = _ at h
  have hlast : n-MaskedStrideScan.ticks P S-S-S ≤ P := by unfold ticks at hn; omega
  fin_cases t <;> simpa [path,Nat.min_eq_left hlast,sub_eq_add_neg,add_assoc] using h

theorem path_frozen (P S : ℕ) (t : Fin 2) (n : ℕ) : path P S t (min n (ticks P S)) = path P S t n := by
  have ht : ticks P S = MaskedStrideScan.ticks P S+2*S+P := by unfold ticks; omega
  have h0 : min (min n (ticks P S)) (MaskedStrideScan.ticks P S) = min n (MaskedStrideScan.ticks P S) := by omega
  have h1 : min (min n (ticks P S)-MaskedStrideScan.ticks P S-S-S) P =
      min (n-MaskedStrideScan.ticks P S-S-S) P := by omega
  have h2 : min (min n (ticks P S)-MaskedStrideScan.ticks P S) S =
      min (n-MaskedStrideScan.ticks P S) S := by omega
  have h3 : min (min n (ticks P S)-MaskedStrideScan.ticks P S-S) S =
      min (n-MaskedStrideScan.ticks P S-S) S := by omega
  simp only [path,h0,h1,h2,h3]

theorem path_zero (P : ℕ) {S : ℕ} (hS : 0 < S) (t : Fin 2) : path P S t 0 = 0 := by
  have h := schedule_position false (fun _ => false) P hS [] RawMaskedStride.initial 0 (Nat.zero_le _) t
  change RawMaskedStride.initial.work.pos t = RawMaskedStride.initial.work.pos t+path P S t 0 at h
  omega

theorem path_end (P : ℕ) {S : ℕ} (hS : 0 < S) (t : Fin 2) : path P S t (ticks P S) = 0 := by
  have h := schedule_position false (fun _ => false) P hS [] RawMaskedStride.initial (ticks P S) le_rfl t
  rw [schedule_exact false (fun _ => false) P hS] at h
  have hs := (result_spec false (fun _ => false) P hS [] RawMaskedStride.initial
    (RawMaskedStride.initial_cells 1)).1 t
  rw [hs] at h
  omega

theorem path_after (P : ℕ) {S : ℕ} (hS : 0 < S) (t : Fin 2) (n : ℕ) (hn : ticks P S ≤ n) :
    path P S t n = 0 := by
  rw [← path_frozen P S t n,Nat.min_eq_right hn,path_end P hS]

end TransposeFollowup.MaskedStrideBankStage

namespace TransposeFollowup.MaskedStrideWord
open Classical ScheduledNativeIO
open MaskedStrideCell (State)
set_option autoImplicit false

def path (P : ℕ) (ops : List Operation) : Fin 2 → ℕ → ℤ :=
  ScheduledWord.path (fun op => MaskedStrideBankStage.ticks P op.stride)
    (fun op => MaskedStrideBankStage.path P op.stride) ops

theorem path_zero (P : ℕ) (ops : List Operation) (hv : Valid P ops) (t : Fin 2) : path P ops t 0 = 0 := by
  exact ScheduledWord.path_zero _ _ ops t
    (fun op hop => MaskedStrideBankStage.path_zero P (hv op hop).1 t)

theorem path_after (P : ℕ) (ops : List Operation) (hv : Valid P ops) (t : Fin 2)
    (n : ℕ) (hn : ticks P ops ≤ n) : path P ops t n = 0 := by
  exact ScheduledWord.path_after _ _ ops t
    (fun op hop m hm => MaskedStrideBankStage.path_after P (hv op hop).1 t m hm) n hn

theorem path_frozen (P : ℕ) (ops : List Operation) (hv : Valid P ops) (t : Fin 2) (n : ℕ) :
    path P ops t (min n (ticks P ops)) = path P ops t n := by
  exact ScheduledWord.path_frozen _ _ ops t
    (fun op hop m hm => MaskedStrideBankStage.path_after P (hv op hop).1 t m hm) n

theorem schedule_position (P : ℕ) (ops : List Operation) (hv : Valid P ops)
    (w : List Bool) (c : State) (n : ℕ) (hn : n ≤ ticks P ops) (t : Fin 2) :
    (trajectory (schedule P ops) w c n).work.pos t = c.work.pos t+path P ops t n := by
  exact ScheduledWord.schedule_position _ _ _ _ ops w c n hn t
    (fun op hop d m hm => MaskedStrideBankStage.schedule_position op.isPrefix op.mask P (hv op hop).1 w d m hm t)
    (fun op _ m => MaskedStrideBankStage.path_frozen P op.stride t m)

end TransposeFollowup.MaskedStrideWord

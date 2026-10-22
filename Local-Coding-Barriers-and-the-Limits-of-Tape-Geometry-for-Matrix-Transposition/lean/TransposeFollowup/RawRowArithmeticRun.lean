import TransposeFollowup.RawRowArithmeticData
import TransposeFollowup.CoupledRowMoves

/-! One unmarked raw-row update. The seeks, reset and stationary padding
are scheduled native instructions. Bank advances one row; buffer returns. -/
namespace TransposeFollowup.RawRowArithmetic
open Classical FixedTapeCompiler ScheduledNativeIO
open CopyMachine (Sym Tape symbols)
open CoupledRowCell (Mode State cfg)
set_option autoImplicit false

def reset {C : Type} (sub : C) : NativeIO.Program (Fin 2) (Mode C) :=
  fun _ => .work (.jump (sub,.blank,.blank))

def bankOnly (t : Fin 2) : Bool := t==0

def ticks (W : ℕ) : ℕ := 1+(W+(4*W+(W+(W-1))))

def scheduleWithUpdate {C : Type} (f : Mode C → Mode C) (carry : C) (W : ℕ) :
    ℕ → NativeIO.Program (Fin 2) (Mode C) :=
  append (fun _ => reset carry)
    (append (fun _ => CoupledRowMoves.right (fun _ => true))
      (append (CoupledRowScan.schedule f W)
        (append (fun _ => CoupledRowMoves.right bankOnly)
          (fun _ => CoupledRowScan.idle) W) (4*W)) W) 1

def scheduleWithCarry (sub carry : Bool) (W : ℕ) : ℕ → NativeIO.Program (Fin 2) Mode :=
  scheduleWithUpdate (update sub) carry W

def schedule (sub : Bool) (W : ℕ) : ℕ → NativeIO.Program (Fin 2) Mode :=
  scheduleWithCarry sub sub W

def initial {C : Type} (m : Mode C) (xs ys la lb ra rb : List (Sym Bool))
    (pos : Fin 2 → ℤ) (ip : ℤ) (out : List Bool) : State C :=
  cfg m ![⟨la,xs++ra⟩,⟨lb,ys++rb⟩] pos ip out

def finalCarry (sub : Bool) (xs ys : List (Sym Bool)) : Bool :=
  (CoupledRowScan.evaluate (update sub) sub xs.reverse ys.reverse).1

def final (sub : Bool) (xs ys la lb ra rb : List (Sym Bool))
    (pos : Fin 2 → ℤ) (ip : ℤ) (out : List Bool) : State :=
  cfg (finalCarry sub xs ys,.blank,.blank)
    ![⟨(symbols (output sub xs ys)).reverse++la,ra⟩,⟨lb,symbols (saved sub xs ys)++rb⟩]
    (fun t => pos t+if bankOnly t then (xs.length : ℤ) else 0) ip out

theorem scheduleWithUpdate_active {C : Type} (f : Mode C → Mode C) (carry : C)
    (W i : ℕ) (c : State C) :
    NativeIO.Active (scheduleWithUpdate f carry W i) c := by
  unfold scheduleWithUpdate
  apply append_active
  · intro _; simp [reset,NativeIO.Active]
  · intro _
    apply append_active
    · intro _; exact CoupledRowMoves.right_active _ _
    · intro _
      apply append_active
      · intro j; exact CoupledRowScan.schedule_active _ _ j _
      · intro _
        apply append_active
        · intro _; exact CoupledRowMoves.right_active _ _
        · intro _; simp [CoupledRowScan.idle,NativeIO.Active]

theorem scheduleWithCarry_active (sub carry : Bool) (W i : ℕ) (c : State) :
    NativeIO.Active (scheduleWithCarry sub carry W i) c :=
  scheduleWithUpdate_active (update sub) carry W i c

theorem schedule_active (sub : Bool) (W i : ℕ) (c : State) :
    NativeIO.Active (schedule sub W i) c := scheduleWithCarry_active sub sub W i c

theorem seek_pair {C : Type} (sub : C) (xs ys la lb ra rb : List (Sym Bool))
    (h : xs.length=ys.length) (pos : Fin 2 → ℤ) (ip : ℤ) (out w : List Bool) :
    trajectory (fun _ => CoupledRowMoves.right (fun _ => true)) w
      (initial (sub,.blank,.blank) xs ys la lb ra rb pos ip out) xs.length=
      cfg (sub,.blank,.blank) ![⟨xs.reverse++la,ra⟩,⟨ys.reverse++lb,rb⟩]
        (fun t => pos t+xs.length) ip out := by
  rw [initial,CoupledRowMoves.right_exact]
  simp only [ite_true]
  congr 1
  funext t
  fin_cases t
  · exact CoupledRowMoves.right_word xs la ra
  · rw [h]
    exact CoupledRowMoves.right_word ys lb rb

theorem scan_pair (sub : Bool) (xs ys la lb ra rb : List (Sym Bool))
    (h : xs.length=ys.length) (pos : Fin 2 → ℤ) (ip : ℤ) (out w : List Bool) :
    trajectory (CoupledRowScan.schedule (update sub) xs.length) w
      (cfg (sub,.blank,.blank) ![⟨xs.reverse++la,ra⟩,⟨ys.reverse++lb,rb⟩]
        (fun t => pos t+xs.length) ip out) (4*xs.length)=
      cfg (finalCarry sub xs ys,.blank,.blank)
        ![⟨la,symbols (output sub xs ys)++ra⟩,⟨lb,symbols (saved sub xs ys)++rb⟩]
        pos ip out := by
  rw [CoupledRowScan.schedule_exact]
  have ht := CoupledRowScan.run_pair (update sub) sub xs.reverse ys.reverse
    (by simpa using h) la lb ra rb (fun t => pos t+xs.length) ip out
  simpa only [List.length_reverse,add_sub_cancel_right,(raw_outputs sub xs ys h).1,
    (raw_outputs sub xs ys h).2,finalCarry] using ht

theorem finish_pair (sub : Bool) (xs ys la lb ra rb : List (Sym Bool))
    (h : xs.length=ys.length) (pos : Fin 2 → ℤ) (ip : ℤ) (out w : List Bool) :
    trajectory (fun _ => CoupledRowMoves.right bankOnly) w
      (cfg (finalCarry sub xs ys,.blank,.blank)
        ![⟨la,symbols (output sub xs ys)++ra⟩,⟨lb,symbols (saved sub xs ys)++rb⟩]
        pos ip out) xs.length=final sub xs ys la lb ra rb pos ip out := by
  rw [CoupledRowMoves.right_exact]
  unfold final
  congr 1
  funext t
  fin_cases t
  · simp only [bankOnly]
    rw [← show (symbols (output sub xs ys)).length=xs.length by simp [symbols,output_length _ _ _ h]]
    exact CoupledRowMoves.right_word _ _ _
  · rfl

def finalWithUpdate {C : Type} (f : Mode C → Mode C) (carry : C) (xs ys la lb ra rb : List (Sym Bool))
    (pos : Fin 2 → ℤ) (ip : ℤ) (out : List Bool) : State C :=
  let r := CoupledRowScan.evaluate f carry xs.reverse ys.reverse
  cfg (r.1,.blank,.blank) ![⟨r.2.1++la,ra⟩,⟨lb,r.2.2.reverse++rb⟩]
    (fun t => pos t+if bankOnly t then (xs.length : ℤ) else 0) ip out

theorem scheduleWithUpdate_exact {C : Type} (f : Mode C → Mode C) (carry : C) (m : Mode C) (xs ys la lb ra rb : List (Sym Bool))
    (h : xs.length=ys.length) (pos : Fin 2 → ℤ) (ip : ℤ) (out w : List Bool) :
    trajectory (scheduleWithUpdate f carry xs.length) w (initial m xs ys la lb ra rb pos ip out)
      (ticks xs.length)=finalWithUpdate f carry xs ys la lb ra rb pos ip out := by
  simp only [scheduleWithUpdate,ticks,append_exact]
  have hr : trajectory (fun _ => reset carry) w (initial m xs ys la lb ra rb pos ip out) 1=
      initial (carry,.blank,.blank) xs ys la lb ra rb pos ip out := rfl
  rw [hr,seek_pair carry xs ys la lb ra rb h pos ip out w,CoupledRowScan.schedule_exact]
  have hs := CoupledRowScan.run_pair f carry xs.reverse ys.reverse
    (by simpa using h) la lb ra rb (fun t => pos t+xs.length) ip out
  simp only [List.length_reverse,add_sub_cancel_right] at hs
  rw [hs,CoupledRowMoves.right_exact,CoupledRowScan.idle_exact]
  have hl := (CoupledRowScan.evaluate_lengths f carry xs.reverse ys.reverse
    (by simpa using h)).1
  simp only [List.length_reverse] at hl
  have hrev : (CoupledRowScan.evaluate f carry xs.reverse ys.reverse).2.1.reverse.length=
      xs.length := by simpa only [List.length_reverse] using hl
  unfold finalWithUpdate
  congr 1
  funext t
  fin_cases t
  · change (Tape.moveRight^[xs.length])
        ⟨la,(CoupledRowScan.evaluate f carry xs.reverse ys.reverse).2.1.reverse++ra⟩=
      ⟨(CoupledRowScan.evaluate f carry xs.reverse ys.reverse).2.1++la,ra⟩
    rw [← hrev,CoupledRowMoves.right_word,List.reverse_reverse]
  · rfl

def finalWithCarry (sub carry : Bool) (xs ys la lb ra rb : List (Sym Bool))
    (pos : Fin 2 → ℤ) (ip : ℤ) (out : List Bool) : State :=
  finalWithUpdate (update sub) carry xs ys la lb ra rb pos ip out

theorem scheduleWithCarry_exact (sub carry : Bool) (m : Mode) (xs ys la lb ra rb : List (Sym Bool))
    (h : xs.length=ys.length) (pos : Fin 2 → ℤ) (ip : ℤ) (out w : List Bool) :
    trajectory (scheduleWithCarry sub carry xs.length) w (initial m xs ys la lb ra rb pos ip out)
      (ticks xs.length)=finalWithCarry sub carry xs ys la lb ra rb pos ip out :=
  scheduleWithUpdate_exact (update sub) carry m xs ys la lb ra rb h pos ip out w

theorem schedule_exact (sub : Bool) (m : Mode) (xs ys la lb ra rb : List (Sym Bool))
    (h : xs.length=ys.length) (pos : Fin 2 → ℤ) (ip : ℤ) (out w : List Bool) :
    trajectory (schedule sub xs.length) w (initial m xs ys la lb ra rb pos ip out)
      (ticks xs.length)=final sub xs ys la lb ra rb pos ip out := by
  have ho : (CoupledRowScan.evaluate (update sub) sub xs.reverse ys.reverse).2.1=
      (symbols (output sub xs ys)).reverse := by
    simpa only [List.reverse_reverse] using congrArg List.reverse (raw_outputs sub xs ys h).1
  simpa only [schedule,finalWithCarry,finalWithUpdate,final,finalCarry,ho,(raw_outputs sub xs ys h).2]
    using scheduleWithCarry_exact sub sub m xs ys la lb ra rb h pos ip out w

theorem ticks_eq (W : ℕ) (h : 0 < W) : ticks W=7*W := by unfold ticks; omega

end TransposeFollowup.RawRowArithmetic

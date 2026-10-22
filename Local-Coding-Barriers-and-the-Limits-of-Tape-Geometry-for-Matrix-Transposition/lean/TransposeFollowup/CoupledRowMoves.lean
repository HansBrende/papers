import TransposeFollowup.CoupledRowCell

/-! Paid rightward seeks, expressed using existing zipper denotation and
mathlib iteration. Selection is public and does not inspect tape contents. -/
namespace TransposeFollowup.CoupledRowMoves
open Classical FixedTapeCompiler ScheduledNativeIO
open CopyMachine (Sym Tape)
open CoupledRowCell (Mode State cfg)
set_option autoImplicit false
variable {C : Type}

def right (select : Fin 2 → Bool) : NativeIO.Program (Fin 2) (Mode C) :=
  fun m => .work (.act (fun t => ⟨none,if select t then .right else .stay⟩) m)

theorem right_active (select : Fin 2 → Bool) (c : (State C)) : NativeIO.Active (right select) c := by
  simp [right,NativeIO.Active]

theorem right_cfg (select : Fin 2 → Bool) (w : List Bool) (m : (Mode C))
    (ts : Fin 2 → Tape Bool) (pos : Fin 2 → ℤ) (ip : ℤ) (out : List Bool) :
    NativeIO.step (right select) w (cfg m ts pos ip out)=
      cfg m (fun t => if select t then (ts t).moveRight else ts t)
        (fun t => pos t+if select t then 1 else 0) ip out := by
  simp only [right,NativeIO.step,NativeIO.workProgram,NativeMicrocode.step,
    Microcode.actualStep,cfg]
  congr 2
  · congr 1
    funext t
    cases select t <;> simp [Microcode.Action.actual]
  · funext t
    cases select t <;> simp [NativeMicrocode.direction,Transpose.Dir.shift]

theorem right_exact (select : Fin 2 → Bool) (w : List Bool) (m : (Mode C))
    (ts : Fin 2 → Tape Bool) (pos : Fin 2 → ℤ) (ip : ℤ) (out : List Bool) (n : ℕ) :
    trajectory (fun _ => right select) w (cfg m ts pos ip out) n=
      cfg m (fun t => if select t then (Tape.moveRight^[n]) (ts t) else ts t)
        (fun t => pos t+if select t then (n : ℤ) else 0) ip out := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
    rw [trajectory,ih,right_cfg]
    congr 1 <;> funext t <;> cases select t <;>
      simp [Function.iterate_succ_apply',Nat.cast_add,add_assoc]

theorem right_word (xs pre suffix : List (Sym Bool)) :
    (Tape.moveRight^[xs.length]) (⟨pre,xs++suffix⟩ : Tape Bool)=
      ⟨xs.reverse++pre,suffix⟩ := by
  induction xs generalizing pre with
  | nil => rfl
  | cons a xs ih =>
    simpa only [List.length_cons,Function.iterate_succ_apply,List.cons_append,
      Tape.moveRight,Tape.read,List.headD_cons,List.tail_cons,List.reverse_cons,
      List.append_assoc,List.singleton_append,List.nil_append] using ih (a::pre)

end TransposeFollowup.CoupledRowMoves

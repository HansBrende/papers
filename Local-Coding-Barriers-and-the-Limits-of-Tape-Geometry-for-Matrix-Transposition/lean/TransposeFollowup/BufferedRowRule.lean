import TransposeFollowup.RawRowArithmeticRun

/-! A finite paired-cell rule with its list semantics. This packages the
existing paid row executor; it does not add an abstract machine operation.
Integer carries and componentwise ternary updates use the same schedule. -/
namespace TransposeFollowup.BufferedRows
open FixedTapeCompiler ScheduledNativeIO
open CopyMachine (Sym Tape)
open CoupledRowCell (Mode State cfg)
set_option autoImplicit false

structure Rule (C : Type) where
  table : Mode C → Mode C
  carry : C
  output : List (Sym Bool) → List (Sym Bool) → List (Sym Bool)
  saved : List (Sym Bool) → List (Sym Bool) → List (Sym Bool)
  realizes : ∀ xs ys, xs.length=ys.length →
    (CoupledRowScan.evaluate table carry xs.reverse ys.reverse).2.1.reverse=output xs ys ∧
    (CoupledRowScan.evaluate table carry xs.reverse ys.reverse).2.2.reverse=saved xs ys

variable {C : Type} (u : Rule C)

def schedule (W : ℕ) : ℕ → NativeIO.Program (Fin 2) (Mode C) :=
  RawRowArithmetic.scheduleWithUpdate u.table u.carry W

def finalCarry (xs ys : List (Sym Bool)) : C :=
  (CoupledRowScan.evaluate u.table u.carry xs.reverse ys.reverse).1

def final (xs ys la lb ra rb : List (Sym Bool))
    (pos : Fin 2 → ℤ) (ip : ℤ) (out : List Bool) : State C :=
  cfg (finalCarry u xs ys,.blank,.blank)
    ![⟨(u.output xs ys).reverse++la,ra⟩,⟨lb,u.saved xs ys++rb⟩]
    (fun t => pos t+if RawRowArithmetic.bankOnly t then (xs.length : ℤ) else 0) ip out

theorem output_length (xs ys : List (Sym Bool)) (h : xs.length=ys.length) :
    (u.output xs ys).length=xs.length := by
  rw [← (u.realizes xs ys h).1,List.length_reverse]
  simpa only [List.length_reverse] using
    (CoupledRowScan.evaluate_lengths u.table u.carry xs.reverse ys.reverse (by simpa using h)).1

theorem saved_length (xs ys : List (Sym Bool)) (h : xs.length=ys.length) :
    (u.saved xs ys).length=xs.length := by
  rw [← (u.realizes xs ys h).2,List.length_reverse]
  simpa only [List.length_reverse] using
    (CoupledRowScan.evaluate_lengths u.table u.carry xs.reverse ys.reverse (by simpa using h)).2

theorem schedule_active (W i : ℕ) (c : State C) :
    NativeIO.Active (schedule u W i) c :=
  RawRowArithmetic.scheduleWithUpdate_active u.table u.carry W i c

theorem schedule_exact (m : Mode C) (xs ys la lb ra rb : List (Sym Bool))
    (h : xs.length=ys.length) (pos : Fin 2 → ℤ) (ip : ℤ) (out w : List Bool) :
    trajectory (schedule u xs.length) w (RawRowArithmetic.initial m xs ys la lb ra rb pos ip out)
      (RawRowArithmetic.ticks xs.length)=final u xs ys la lb ra rb pos ip out := by
  have ho : (CoupledRowScan.evaluate u.table u.carry xs.reverse ys.reverse).2.1=
      (u.output xs ys).reverse := by
    simpa only [List.reverse_reverse] using congrArg List.reverse (u.realizes xs ys h).1
  simpa only [schedule,RawRowArithmetic.finalWithUpdate,final,finalCarry,ho,(u.realizes xs ys h).2]
    using RawRowArithmetic.scheduleWithUpdate_exact u.table u.carry m xs ys la lb ra rb h pos ip out w

end TransposeFollowup.BufferedRows

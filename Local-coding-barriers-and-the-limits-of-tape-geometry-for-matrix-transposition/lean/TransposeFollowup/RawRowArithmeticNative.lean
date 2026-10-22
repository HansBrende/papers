import TransposeFollowup.RawRowArithmeticRun
import TransposeFollowup.ScheduledHeadDisplacement

/-! The raw-row controller runs on the original native TM. No input/output
staging or tape preparation is implicit: both fields and all surrounding
cells occur in the initial configuration. Compilation and prefix traces
use the shared public-schedule compiler. -/
namespace TransposeFollowup.RawRowArithmetic
open Classical FixedTapeCompiler ScheduledNativeIO
open CopyMachine (Sym)
open CoupledRowCell (Mode)
set_option autoImplicit false
variable {k q : ℕ}

theorem fixed_resources (sub : Bool) (W : ℕ) :
    let e := NativeMicrocode.initialEncoding (T:=Fin 2)
      ((⟨0,by omega⟩,(sub,Sym.blank,Sym.blank)) : Fin (ticks W+1) × Mode)
    let M := NativeIO.machine e (program (schedule sub W) (ticks W))
    M.k=2 ∧ M.g+1=5 ∧ M.q+1=(ticks W+1)*50 := by
  refine ⟨rfl,rfl,?_⟩
  have hc : Fintype.card Mode=50 := by decide +kernel
  simpa only [hc] using native_state_count (T:=Fin 2)
    (schedule sub W) (ticks W) (sub,Sym.blank,Sym.blank)

theorem native_complete (sub : Bool) (m : Mode)
    (xs ys la lb ra rb : List (Sym Bool)) (h : xs.length=ys.length)
    (e : NativeMicrocode.Encoding (Fin 2) (Fin (ticks xs.length+1) × Mode) k q)
    (pos : Fin 2 → ℤ) (ip : ℤ) (out w : List Bool) :
    let p := program (schedule sub xs.length) (ticks xs.length)
    Transpose.stepN (NativeIO.machine e p) w (ticks xs.length)
      ((lift ⟨0,by omega⟩ (initial m xs ys la lb ra rb pos ip out)).denote e p) =
      some ((lift ⟨ticks xs.length,by omega⟩
        (final sub xs ys la lb ra rb pos ip out)).denote e p) ∧
    Transpose.step (NativeIO.machine e p) w
      ((lift ⟨ticks xs.length,by omega⟩
        (final sub xs ys la lb ra rb pos ip out)).denote e p)=none := by
  have ht := native_run_and_halt e (schedule sub xs.length) w
    (initial m xs ys la lb ra rb pos ip out) (fun i _ => schedule_active sub _ i _)
  simpa only [schedule_exact sub m xs ys la lb ra rb h pos ip out w] using ht

theorem native_prefix_excursion (sub : Bool) (m : Mode)
    (xs ys la lb ra rb : List (Sym Bool))
    (e : NativeMicrocode.Encoding (Fin 2) (Fin (ticks xs.length+1) × Mode) k q)
    (pos : Fin 2 → ℤ) (ip : ℤ) (out w : List Bool)
    (n : ℕ) (hn : n≤ticks xs.length) :
    let p := program (schedule sub xs.length) (ticks xs.length)
    ∃ d : Transpose.Config (NativeIO.machine e p),
      Transpose.stepN (NativeIO.machine e p) w n
        ((lift ⟨0,by omega⟩ (initial m xs ys la lb ra rb pos ip out)).denote e p)=some d ∧
      ∀ t : Fin 2, |d.workPos (e.port t)-pos t|≤n := by
  refine ⟨_,native_prefix e (schedule sub xs.length) w
    (initial m xs ys la lb ra rb pos ip out)
    (fun i _ => schedule_active sub _ i _) n hn,?_⟩
  intro t
  simpa only [NativeIO.Config.denote,lift,Equiv.symm_apply_apply,
    initial,CoupledRowCell.cfg] using trajectory_displacement
      (schedule sub xs.length) w (initial m xs ys la lb ra rb pos ip out) n t

end TransposeFollowup.RawRowArithmetic

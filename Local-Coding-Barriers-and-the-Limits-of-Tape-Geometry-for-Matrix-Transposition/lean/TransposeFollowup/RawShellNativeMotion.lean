import TransposeFollowup.RawShellPosition
import Transpose.Tape.MStarTM

/-! Transport actual body-prefix positions to the complete original-TM
trajectory, including the frozen tail. The body may move differently on
different data; its actual prepared-state trajectory remains explicit. -/
namespace TransposeFollowup.RawProgramShell
open Classical FixedTapeCompiler ScheduledNativeIO
set_option autoImplicit false
variable {F : Type*} [Fintype F]

theorem native_halts (f : F) (P N : ℕ) (σ : ℕ → NativeIO.Program (Fin 2) (Mode F))
    (ha : ∀ i c, NativeIO.Active (σ i) c) (w : List Bool) :
    Transpose.Tape.HaltsAt (machine f P N σ) w (ticks P N) := by
  obtain ⟨hs,hh⟩ := native_complete f P N σ ha w
  have hr := (Transpose.Tape.Impl.stepN_init_eq_some_iff (ticks P N) _).mp hs
  refine ⟨hr.1,(Transpose.Tape.Impl.step_run_eq_none_iff (ticks P N)).mp ?_⟩
  rw [hr.2]
  exact hh

theorem workTraj_decomposition (f : F) (P N : ℕ) (σ : ℕ → NativeIO.Program (Fin 2) (Mode F))
    (ha : ∀ i c, NativeIO.Active (σ i) c) (w : List Bool) (n : ℕ) (t : Fin 2) :
    Transpose.Tape.workTraj (machine f P N σ) w n ((encoding f P N).port t)=
      (trajectory σ w (prepared f P w) (min (n-4*P) N)).work.pos t+
        RawBankProgram.ioPath P N t n := by
  let m := min n (ticks P N)
  have hm : m≤ticks P N := Nat.min_le_right _ _
  have hs := native_prefix (encoding f P N) (schedule P N σ) w (initial f)
    (fun i _ => schedule_active P N σ ha i _) m hm
  have hb : (lift (⟨0,by omega⟩ : Fin (ticks P N+1)) (initial f)).denote
      (encoding f P N) (program (schedule P N σ) (ticks P N))=Transpose.init (machine f P N σ) :=
    NativeIO.blank_denote (encoding f P N) _ _ (NativeMicrocode.initialEncoding_start _)
  rw [hb] at hs
  have hp := congrArg (fun d => d.workPos ((encoding f P N).port t))
    ((Transpose.Tape.Impl.stepN_init_eq_some_iff m _).mp hs).2
  change Transpose.Tape.workTraj (machine f P N σ) w m _ = _ at hp
  have he : Transpose.Tape.workTraj (machine f P N σ) w m ((encoding f P N).port t)=
      (trajectory (schedule P N σ) w (initial f) m).work.pos t := by
    simpa only [NativeIO.Config.denote,lift,Equiv.symm_apply_apply] using hp
  rw [position_decomposition f P N σ w m hm t] at he
  have hmin : min (m-4*P) N=min (n-4*P) N := by dsimp [m,ticks]; omega
  have hio : RawBankProgram.ioPath P N t m=RawBankProgram.ioPath P N t n := ioPath_frozen P N t n
  rw [hmin,hio] at he
  have hf := congrFun (Transpose.Tape.Impl.workTraj_frozen (native_halts f P N σ ha w)
    ((encoding f P N).port t)) n
  exact hf.symm.trans he

end TransposeFollowup.RawProgramShell

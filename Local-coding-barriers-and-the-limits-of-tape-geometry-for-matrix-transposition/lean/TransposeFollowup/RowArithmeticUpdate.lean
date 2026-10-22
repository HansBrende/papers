import TransposeFollowup.RepeatedAddBody
import TransposeFollowup.PaddedWorkSchedule

/-! One prepared fixed-width add/subtract update, with paid recycling and a
public duration. The old repeated-addition body and this controller share
the same call/composition proofs. Raw row staging remains a separate task. -/
namespace TransposeFollowup.RowArithmeticUpdate
open Classical FixedTapeCompiler ScheduledNativeIO
open RepeatedAdd (Port Label Bank cfg ready)
set_option autoImplicit false

def program : Microcode.Program Port Label
  | .counter _ => .halt
  | pc => RepeatedAdd.program pc

def start (sub : Bool) : Label := .arithmetic false (.scan sub sub)

def ticks (W : ℕ) : ℕ := 18*W+30

def schedule (_ : ℕ) : NativeIO.Program Port Label := PaddedWorkSchedule.code program

def initial (sub : Bool) (fuel a x : List Bool) (pos : Port → ℤ)
    (ip : ℤ) (out : List Bool) : NativeIO.Config Port Label :=
  ⟨cfg (start sub) (ready fuel a x) pos,ip,out⟩

def final (sub : Bool) (fuel a x : List Bool) (pos : Port → ℤ)
    (ip : ℤ) (out : List Bool) : NativeIO.Config Port Label :=
  ⟨cfg (.counter 0) (ready fuel (ModularRowWord.operation sub a x) x) pos,ip,out⟩

theorem body_trace (sub : Bool) (fuel a x : List Bool) (h : a.length=x.length)
    (pos : Port → ℤ) :
    ∃ t ≤ ticks x.length,
      OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
        (cfg (start sub) (ready fuel a x) pos)
        (cfg (.counter 0) (ready fuel (ModularRowWord.operation sub a x) x) pos) := by
  apply RepeatedAdd.update_trace_to program
  · intro copy pc hh hr
    exact RepeatedAdd.arithmetic_code copy pc hh hr
  · intro scratch pc hh hr
    exact RepeatedAdd.clear_code scratch pc hh hr
  · intro copy carry; rfl
  · intro scratch; cases scratch <;> rfl
  · exact h

theorem schedule_active (w : List Bool) (c : NativeIO.Config Port Label) (n : ℕ) :
    NativeIO.Active (schedule n) (trajectory schedule w c n) :=
  PaddedWorkSchedule.active program _

theorem schedule_exact (sub : Bool) (fuel a x : List Bool) (h : a.length=x.length)
    (pos : Port → ℤ) (w : List Bool) (ip : ℤ) (out : List Bool) :
    trajectory schedule w (initial sub fuel a x pos ip out) (ticks x.length)=
      final sub fuel a x pos ip out := by
  obtain ⟨t,ht,htr⟩ := body_trace sub fuel a x h pos
  exact PaddedWorkSchedule.trajectory_of_trace program w _ _ ip out ht htr
    (by simp [NativeMicrocode.Active,cfg,program])

theorem schedule_excursion (sub : Bool) (fuel a x : List Bool)
    (pos : Port → ℤ) (w : List Bool) (ip : ℤ) (out : List Bool) (n : ℕ) (t : Port) :
    |(trajectory schedule w (initial sub fuel a x pos ip out) n).work.pos t-pos t|≤n :=
  PaddedWorkSchedule.trajectory_displacement program w _ n t

noncomputable def encoding (sub : Bool) (W : ℕ) :=
  NativeMicrocode.initialEncoding (T:=Port)
    ((⟨0,by omega⟩,start sub) : Fin (ticks W+1) × Label)

noncomputable def machine (sub : Bool) (W : ℕ) : Transpose.TM :=
  NativeIO.machine (encoding sub W) (ScheduledNativeIO.program schedule (ticks W))

theorem fixed_resources (sub : Bool) (W : ℕ) :
    (machine sub W).k=5 ∧ (machine sub W).g+1=5 ∧
      (machine sub W).q+1=(ticks W+1)*99 := by
  refine ⟨?_,rfl,?_⟩
  · change Fintype.card Port=5
    decide +kernel
  · have h := native_state_count (T:=Port) schedule (ticks W) (start sub)
    have hc : Fintype.card Label=99 := by decide +kernel
    simpa only [machine,encoding,hc] using h

theorem native_complete (sub : Bool) (fuel a x : List Bool) (h : a.length=x.length)
    (pos : Port → ℤ) (w : List Bool) (ip : ℤ) (out : List Bool) :
    Transpose.stepN (machine sub x.length) w (ticks x.length)
      ((lift ⟨0,by omega⟩ (initial sub fuel a x pos ip out)).denote
        (encoding sub x.length) (ScheduledNativeIO.program schedule (ticks x.length))) =
      some ((lift ⟨ticks x.length,by omega⟩ (final sub fuel a x pos ip out)).denote
        (encoding sub x.length) (ScheduledNativeIO.program schedule (ticks x.length))) ∧
    Transpose.step (machine sub x.length) w
      ((lift ⟨ticks x.length,by omega⟩ (final sub fuel a x pos ip out)).denote
        (encoding sub x.length) (ScheduledNativeIO.program schedule (ticks x.length)))=none := by
  have ht := native_run_and_halt (encoding sub x.length) schedule w
    (initial sub fuel a x pos ip out) (fun n _ => schedule_active w _ n)
  simpa only [machine,schedule_exact sub fuel a x h pos w ip out] using ht

theorem native_prefix_excursion (sub : Bool) (fuel a x : List Bool)
    (pos : Port → ℤ) (w : List Bool) (ip : ℤ) (out : List Bool)
    (n : ℕ) (hn : n ≤ ticks x.length) :
    ∃ d : Transpose.Config (machine sub x.length),
      Transpose.stepN (machine sub x.length) w n
        ((lift ⟨0,by omega⟩ (initial sub fuel a x pos ip out)).denote
          (encoding sub x.length) (ScheduledNativeIO.program schedule (ticks x.length)))=some d ∧
      ∀ t : Port, |d.workPos ((encoding sub x.length).port t)-pos t|≤n := by
  refine ⟨_,native_prefix (encoding sub x.length) schedule w
    (initial sub fuel a x pos ip out) (fun i _ => schedule_active w _ i) n hn,?_⟩
  intro t
  simpa only [NativeIO.Config.denote,NativeMicrocode.Config.denote,lift,
    Equiv.symm_apply_apply] using schedule_excursion sub fuel a x pos w ip out n t

theorem ticks_linear (W : ℕ) (hW : 0 < W) : ticks W≤48*W := by
  unfold ticks
  omega

end TransposeFollowup.RowArithmeticUpdate

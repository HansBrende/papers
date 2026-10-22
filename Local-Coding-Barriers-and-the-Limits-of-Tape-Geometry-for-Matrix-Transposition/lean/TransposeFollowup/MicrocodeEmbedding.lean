import TransposeFollowup.NativeMicrocodeRunCore

/-! Bind a finite subroutine to distinct caller tapes and caller labels.
Active instructions must agree with the explicit binding. Return labels
may contain arbitrary caller continuations. All unused tapes and absolute
positions are retained, and the native transition count is unchanged. -/

namespace TransposeFollowup.MicrocodeEmbedding

open FixedTapeCompiler
open CopyMachine (Sym)
open Microcode (Action Instruction Program)
set_option autoImplicit false
variable {T U L J A : Type*}

@[simp] theorem extend_at (ports : T ↪ U) (t : T) (g : T → A) (f : U → A) :
    Function.extend ports g f (ports t) = g t := ports.injective.extend_apply g f t

theorem extend_outside (ports : T ↪ U) (u : U) (h : ¬∃ t, ports t = u)
    (g : T → A) (f : U → A) : Function.extend ports g f u = f u :=
  Function.extend_apply' g f u h

def idle : Action := ⟨none, .stay⟩

noncomputable def instruction (ports : T ↪ U) (labels : L → J) :
    Instruction T L → Instruction U J
  | .read t next => .read (ports t) (labels ∘ next)
  | .act acts next => .act (Function.extend ports acts (fun _ => idle)) (labels next)
  | .jump next => .jump (labels next)
  | .halt => .halt
  | .reject => .reject

structure Frame (U : Type*) where
  tapes : U → Turing.Tape (Sym Bool)
  pos : U → ℤ

noncomputable def embed (ports : T ↪ U) (labels : L → J)
    (c : NativeMicrocode.Config T L) (frame : Frame U) : NativeMicrocode.Config U J where
  core := ⟨labels c.core.pc, Function.extend ports c.core.tapes frame.tapes⟩
  pos := Function.extend ports c.pos frame.pos

theorem action_tapes (ports : T ↪ U) (acts : T → Action)
    (bank : T → Turing.Tape (Sym Bool)) (frame : U → Turing.Tape (Sym Bool)) :
    (fun u => (Function.extend ports acts (fun _ => idle) u).actual
      (Function.extend ports bank frame u)) =
      Function.extend ports (fun t => (acts t).actual (bank t)) frame := by
  classical
  funext u
  by_cases hu : ∃ t, ports t = u
  · obtain ⟨t, rfl⟩ := hu
    simp only [extend_at]
  · simp only [extend_outside ports u hu, idle, Microcode.Action.actual]

theorem action_positions (ports : T ↪ U) (acts : T → Action)
    (pos : T → ℤ) (frame : U → ℤ) :
    (fun u => (NativeMicrocode.direction
      (Function.extend ports acts (fun _ => idle) u).move).shift
        (Function.extend ports pos frame u)) =
      Function.extend ports (fun t => (NativeMicrocode.direction (acts t).move).shift (pos t))
        frame := by
  classical
  funext u
  by_cases hu : ∃ t, ports t = u
  · obtain ⟨t, rfl⟩ := hu
    simp only [extend_at]
  · simp only [extend_outside ports u hu, idle, NativeMicrocode.direction, Transpose.Dir.shift]

theorem step_embed (ports : T ↪ U) (labels : L → J)
    (source : Program T L) (target : Program U J)
    (c : NativeMicrocode.Config T L) (frame : Frame U)
    (hc : target (labels c.core.pc) = instruction ports labels (source c.core.pc)) :
    NativeMicrocode.step target (embed ports labels c frame) =
      embed ports labels (NativeMicrocode.step source c) frame := by
  cases hs : source c.core.pc <;>
    simp only [NativeMicrocode.step, Microcode.actualStep, embed, hc, hs, instruction,
      Function.comp_apply, extend_at, action_tapes, action_positions]

theorem active_embed (ports : T ↪ U) (labels : L → J)
    (source : Program T L) (target : Program U J)
    (c : NativeMicrocode.Config T L) (frame : Frame U)
    (hc : target (labels c.core.pc) = instruction ports labels (source c.core.pc))
    (ha : NativeMicrocode.Active source c) :
    NativeMicrocode.Active target (embed ports labels c frame) := by
  cases hs : source c.core.pc <;>
    simp_all [NativeMicrocode.Active, embed, instruction]

/-- Only active source labels impose code equations. In particular the
caller may replace the source's halting return labels by useful next code. -/
theorem trace_embed (ports : T ↪ U) (labels : L → J)
    (source : Program T L) (target : Program U J) (frame : Frame U)
    (hc : ∀ pc, source pc ≠ .halt → source pc ≠ .reject →
      target (labels pc) = instruction ports labels (source pc))
    {n : ℕ} {c d : NativeMicrocode.Config T L}
    (h : OperationalTrace.Trace (NativeMicrocode.step source) (NativeMicrocode.Active source)
      n c d) :
    OperationalTrace.Trace (NativeMicrocode.step target) (NativeMicrocode.Active target)
      n (embed ports labels c frame) (embed ports labels d frame) := by
  induction h with
  | refl c => exact .refl _
  | @cons n c d ha tr ih =>
    have hcode := hc c.core.pc ha.1 ha.2
    refine .cons (active_embed ports labels source target c frame hcode ha) ?_
    rw [step_embed ports labels source target c frame hcode]
    exact ih

theorem native_call {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : T ↪ U) (labels : L → J) (source : Program T L) (target : Program U J)
    (frame : Frame U) (w : List Bool) (inputPos : ℤ) (outRev : List Bool)
    (hc : ∀ pc, source pc ≠ .halt → source pc ≠ .reject →
      target (labels pc) = instruction ports labels (source pc))
    {n : ℕ} {c d : NativeMicrocode.Config T L}
    (h : OperationalTrace.Trace (NativeMicrocode.step source) (NativeMicrocode.Active source)
      n c d) :
    Transpose.stepN (NativeMicrocode.machine encoding target) w n
      ((embed ports labels c frame).denote encoding target inputPos outRev) =
      some ((embed ports labels d frame).denote encoding target inputPos outRev) :=
  NativeMicrocode.trace_stepN encoding target w inputPos outRev
    (trace_embed ports labels source target frame hc h)

theorem unused_tape (ports : T ↪ U) (labels : L → J) (c : NativeMicrocode.Config T L)
    (frame : Frame U) (u : U) (h : ¬∃ t, ports t = u) :
    (embed ports labels c frame).core.tapes u = frame.tapes u ∧
      (embed ports labels c frame).pos u = frame.pos u := by
  simp only [embed, extend_outside ports u h, and_self]

end TransposeFollowup.MicrocodeEmbedding

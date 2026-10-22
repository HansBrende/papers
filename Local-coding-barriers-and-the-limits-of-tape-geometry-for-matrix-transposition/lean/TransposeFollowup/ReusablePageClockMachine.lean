import TransposeFollowup.PageClockTrace
import TransposeFollowup.NativeClosedStreamExact

/-! The clock scan and the existing rewind execute in one finite program.
All page tapes remain blank; only their head positions change. The clock
word and its head are restored for the next row. -/
namespace TransposeFollowup.ReusablePageClock
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}
abbrev Port := PageClock.Port
abbrev Label := PageClock.Label ⊕ NativeSealBack.Label

def identityBinding (q : ℕ) : FinitePortBinding (Port q) (Port q) where
  ports:=Function.Embedding.refl _
  decode:=some
  decode_spec:=by intros;simp [eq_comm]

def clockBinding (q : ℕ) : FinitePortBinding (Fin 1) (Port q) where
  ports:=⟨fun _ => none,fun _ _ _ => Subsingleton.elim _ _⟩
  decode | none => some 0 | some _ => none
  decode_spec:=by
    intro p i
    change (match p with | none => some 0 | some _ => none)=some i ↔ (none:Option (Fin q))=p
    fin_cases i;cases p <;> simp

def program (ops : Fin q → PageOpcode) : Microcode.Program (Port q) Label
  | .inl .done => .jump (.inr .back)
  | .inl pc => (identityBinding q).instruction Sum.inl (PageClock.program ops pc)
  | .inr pc => (clockBinding q).instruction Sum.inr (NativeSealBack.program pc)
def cfg (pc : Label) (clock : Tape Bool) (pos : Port q → ℤ) : NativeMicrocode.Config (Port q) Label :=
  ⟨⟨pc,PageClock.bank clock⟩,pos⟩
def frame (clock : Tape Bool) (pos : Port q → ℤ) : MicrocodeEmbedding.Frame (Port q) :=
  ⟨PageClock.bank clock,pos⟩
abbrev Trace (ops : Fin q → PageOpcode) :=
  OperationalTrace.Trace (NativeMicrocode.step (program ops)) (NativeMicrocode.Active (program ops))

theorem scan_code (ops : Fin q → PageOpcode) (pc : PageClock.Label)
    (hh:PageClock.program ops pc≠.halt) (_:PageClock.program ops pc≠.reject) :
    program ops (.inl pc)=MicrocodeEmbedding.instruction (identityBinding q).ports Sum.inl (PageClock.program ops pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]
theorem rewind_code (ops : Fin q → PageOpcode) (pc : NativeSealBack.Label)
    (_:NativeSealBack.program pc≠.halt) (_:NativeSealBack.program pc≠.reject) :
    program ops (.inr pc)=MicrocodeEmbedding.instruction (clockBinding q).ports Sum.inr (NativeSealBack.program pc) := by
  simp only [program,FinitePortBinding.instruction_eq]

theorem embed_scan (pc : PageClock.Label) (clock base : Tape Bool) (pos basePos : Port q → ℤ) :
    MicrocodeEmbedding.embed (identityBinding q).ports Sum.inl (PageClock.cfg pc clock pos) (frame base basePos)=
      cfg (.inl pc) clock pos := by
  unfold MicrocodeEmbedding.embed PageClock.cfg frame cfg
  simp only [← (identityBinding q).values_eq_extend]
  rfl

theorem embed_rewind (pc : NativeSealBack.Label) (clock base : Tape Bool) (rpos : Fin 1 → ℤ) (pos : Port q → ℤ) :
    MicrocodeEmbedding.embed (clockBinding q).ports Sum.inr (NativeSealBack.cfg pc clock rpos).denote (frame base pos)=
      cfg (.inr pc) clock ((clockBinding q).values rpos pos) := by
  unfold MicrocodeEmbedding.embed NativeSealBack.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus frame cfg
  simp only [← (clockBinding q).values_eq_extend]
  congr 1
  congr 1
  funext p;cases p <;> rfl

theorem clock_positions (pos : Port q → ℤ) :
    (clockBinding q).values (fun _ => pos none) pos=pos := by funext p;cases p <;> rfl

theorem rewind_positions (ops : Fin q → PageOpcode) (pos : Port q → ℤ) (cells count : ℕ) :
    (clockBinding q).values (fun _ => PageClock.advance ops pos cells count none-cells)
      (PageClock.advance ops pos cells count)=PageClock.advance ops pos 0 count := by
  funext p;cases p <;> simp [clockBinding,FinitePortBinding.values,PageClock.advance]

theorem scan_call (ops : Fin q → PageOpcode) (xs : List Bool) (pos : Port q → ℤ) :
    Trace ops (2*xs.length+1) (cfg (.inl .read) (Counter.marked xs) pos)
      (cfg (.inl .done) (RowStream.closedTape xs) (PageClock.advance ops pos xs.length (xs.count true))) := by
  have h:=MicrocodeEmbedding.trace_embed (identityBinding q).ports Sum.inl (PageClock.program ops) (program ops)
    (frame (Counter.marked xs) pos) (scan_code ops) (PageClock.complete_trace ops xs pos)
  simpa only [embed_scan] using h

theorem transfer_trace (ops : Fin q → PageOpcode) (clock : Tape Bool) (pos : Port q → ℤ) :
    Trace ops 1 (cfg (.inl .done) clock pos) (cfg (.inr .back) clock pos) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,program,cfg]
  · exact .refl _

theorem rewind_call (ops : Fin q → PageOpcode) (xs : List Bool) (pos : Port q → ℤ) :
    Trace ops (2*xs.length+4)
      (cfg (.inr .back) (RowStream.closedTape xs) (PageClock.advance ops pos xs.length (xs.count true)))
      (cfg (.inr .done) (Counter.marked xs) (PageClock.advance ops pos 0 (xs.count true))) := by
  let p:=PageClock.advance ops pos xs.length (xs.count true)
  have h:=MicrocodeEmbedding.trace_embed (clockBinding q).ports Sum.inr NativeSealBack.program (program ops)
    (frame (RowStream.closedTape xs) p) (rewind_code ops) (NativeClosedStream.rewind_exact xs (fun _ => p none))
  simpa only [embed_rewind,clock_positions,p,rewind_positions] using h

end TransposeFollowup.ReusablePageClock

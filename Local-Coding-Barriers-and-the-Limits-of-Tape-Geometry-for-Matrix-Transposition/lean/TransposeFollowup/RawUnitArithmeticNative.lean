import TransposeFollowup.RawUnitArithmeticData
import TransposeFollowup.RawCarryBank
import TransposeFollowup.RawRowProgram

/-! The two whole-word unit updates on the shared controller and actual
raw IO shell. Increment/decrement are specified modulo 2^P. -/
namespace TransposeFollowup.RawUnitArithmetic
open Classical FixedTapeCompiler ScheduledNativeIO
open CopyMachine (Sym symbols)
open MaskedStrideCell (bit)
set_option autoImplicit false

def value (sub : Bool) (P : ℕ) : (ℕ → Sym Bool) → ℕ → Sym Bool :=
  RawCarryBank.value sub (!sub) P

theorem value_congr (sub : Bool) (P : ℕ) : BankWord.Congruent P (value sub P) :=
  RawCarryBank.value_congr sub (!sub) P

noncomputable def schedule (sub : Bool) (P i : ℕ) : NativeIO.Program (Fin 2) SharedRowBank.Mode :=
  NativeIOModeProduct.program SharedRowBank.rowModes (RawCarryBank.schedule sub (!sub) P i)

theorem schedule_active (sub : Bool) (P i : ℕ) (c : SharedRowBank.State) :
    NativeIO.Active (schedule sub P i) c :=
  NativeIOModeProduct.active SharedRowBank.rowModes _ (RawCarryBank.schedule_active sub (!sub) P i) c

theorem represents (sub : Bool) (P : ℕ) (w : List Bool) (c : SharedRowBank.State)
    (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols P c (trajectory (schedule sub P) w c (RawCarryBank.ticks P))
      (value sub P (BankWord.input BankWord.symbols c)) := by
  unfold schedule
  rw [NativeIOModeProduct.trajectory_eq,RawCarryBank.schedule_exact]
  exact RawCarryBank.represents sub (!sub) P w (NativeIOModeProduct.project SharedRowBank.rowModes c) hc

def rawTicks (P : ℕ) : ℕ := RawProgramShell.ticks P (RawCarryBank.ticks P)

noncomputable def machine (sub : Bool) (P : ℕ) :=
  RawProgramShell.machine SharedRowBank.initialRowMode P (RawCarryBank.ticks P) (schedule sub P)

def input (P : ℕ) (w : List Bool) : List Bool :=
  List.ofFn (fun i : Fin P => ScheduledRawInput.inputBit w i)

def rawOutput (sub : Bool) (P : ℕ) (w : List Bool) : List Bool :=
  (List.range P).map (fun j => bit (value sub P (fun i => .data (ScheduledRawInput.inputBit w i)) j))

theorem rawOutput_eq (sub : Bool) (P : ℕ) (w : List Bool) : rawOutput sub P w=output sub (input P w) := by
  have hw : (RawCarryBank.word P (fun i => .data (ScheduledRawInput.inputBit w i))).map bit=input P w := by
    simp [RawCarryBank.word,input,List.map_ofFn,Function.comp_def,bit]
  have he := evaluate_output sub (RawCarryBank.word P (fun i => .data (ScheduledRawInput.inputBit w i)))
  rw [hw] at he
  change RawCarryBank.resultWord sub (!sub)
    (RawCarryBank.word P (fun i => .data (ScheduledRawInput.inputBit w i)))=symbols (output sub (input P w)) at he
  apply List.ext_getElem
  · simp [rawOutput,output_length,input]
  · intro j hj hk
    have hjP : j < P := by simpa only [rawOutput,List.length_map,List.length_range] using hj
    simp only [rawOutput,List.getElem_map,List.getElem_range,value,RawCarryBank.value,he]
    rw [List.getI_eq_getElem _ (by simpa only [symbols,List.length_map,output_length,input,List.length_ofFn] using hjP)]
    simp only [symbols,List.getElem_map,bit]

theorem rawOutput_value (sub : Bool) (P : ℕ) (w : List Bool) :
    ModularRowWord.rawValue (rawOutput sub P w)=
      (if sub then ModularRowWord.rawValue (input P w)+2^P-1
        else ModularRowWord.rawValue (input P w)+1)%2^P := by
  rw [rawOutput_eq,output_value]
  simp only [input,List.length_ofFn]

theorem raw_ticks_eq (P : ℕ) (hP : 0 < P) : rawTicks P=17*P := by
  rw [rawTicks,RawProgramShell.ticks_eq,RawCarryBank.ticks_eq P hP]
  omega

theorem native_correct (sub : Bool) (P : ℕ) (w : List Bool) :
    ∃ d : Transpose.Config (machine sub P),
      Transpose.stepN (machine sub P) w (rawTicks P) (Transpose.init (machine sub P))=some d ∧
      Transpose.step (machine sub P) w d=none ∧ d.outRev=(output sub (input P w)).reverse ∧
      ∀ z, d.work ((RawProgramShell.encoding SharedRowBank.initialRowMode P (RawCarryBank.ticks P)).port 1) z=0 := by
  rw [← rawOutput_eq]
  exact RawProgramShell.native_correct SharedRowBank.initialRowMode P (RawCarryBank.ticks P)
    (schedule sub P) (schedule_active sub P) (value sub P) (value_congr sub P)
    (fun w c hc => represents sub P w c hc) w

theorem resources (sub : Bool) (P : ℕ) :
    (machine sub P).k=2 ∧ (machine sub P).g+1=5 ∧ (machine sub P).q+1=(rawTicks P+1)*200 := by
  have h := RawProgramShell.fixed_resources SharedRowBank.initialRowMode P (RawCarryBank.ticks P) (schedule sub P)
  rw [show Fintype.card CoupledRowCell.Mode=50 by decide +kernel] at h
  exact h

end TransposeFollowup.RawUnitArithmetic

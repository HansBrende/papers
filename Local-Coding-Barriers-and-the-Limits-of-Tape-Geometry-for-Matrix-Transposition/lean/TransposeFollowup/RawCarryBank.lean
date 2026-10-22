import TransposeFollowup.RawRowBankInvariant

/-! One whole-bank carry scan with a zero scratch operand. The existing
arbitrary-carry row routine and bank cleanup provide every paid action.
Finite lists below describe actual tape windows, not free staging work. -/
namespace TransposeFollowup.RawCarryBank
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open CopyMachine (Sym Tape)
open CoupledRowCell (Mode State cfg)
set_option autoImplicit false

def ticks (P : ℕ) : ℕ := RawRowArithmetic.ticks P+ScheduledBankCleanup.ticks P P

def schedule (sub carry : Bool) (P : ℕ) : ℕ → NativeIO.Program (Fin 2) Mode :=
  append (RawRowArithmetic.scheduleWithCarry sub carry P)
    (ScheduledBankCleanup.schedule P P) (RawRowArithmetic.ticks P)

def run (sub carry : Bool) (P : ℕ) (w : List Bool) (c : State) : State :=
  ScheduledBankCleanup.run P P w
    (trajectory (RawRowArithmetic.scheduleWithCarry sub carry P) w c (RawRowArithmetic.ticks P))

def resultWord (sub carry : Bool) (xs : List (Sym Bool)) : List (Sym Bool) :=
  (CoupledRowScan.evaluate (RawRowArithmetic.update sub) carry xs.reverse
    (List.replicate xs.length .blank)).2.1.reverse

theorem resultWord_length (sub carry : Bool) (xs : List (Sym Bool)) :
    (resultWord sub carry xs).length=xs.length := by
  simpa only [resultWord,List.length_reverse] using
    (CoupledRowScan.evaluate_lengths (RawRowArithmetic.update sub) carry xs.reverse
      (List.replicate xs.length .blank) (by simp)).1

theorem schedule_active (sub carry : Bool) (P i : ℕ) (c : State) :
    NativeIO.Active (schedule sub carry P i) c := by
  apply append_active
  · intro j; exact RawRowArithmetic.scheduleWithCarry_active sub carry P j c
  · intro j; exact ScheduledBankCleanup.schedule_active P P j c

theorem schedule_exact (sub carry : Bool) (P : ℕ) (w : List Bool) (c : State) :
    trajectory (schedule sub carry P) w c (ticks P)=run sub carry P w c := by
  simp only [schedule,ticks,append_exact,ScheduledBankCleanup.schedule_exact,run]

theorem ticks_eq (P : ℕ) (hP : 0 < P) : ticks P=10*P := by
  rw [ticks,RawRowArithmetic.ticks_eq P hP,ScheduledBankCleanup.ticks]
  omega

theorem bank_spec (sub carry : Bool) (xs pre tail : List (Sym Bool)) (m : Mode)
    (pos : Fin 2 → ℤ) (ip : ℤ) (out w : List Bool) :
    let c := RawRowArithmetic.bankStart m [xs] pre tail pos ip out
    let d := run sub carry xs.length w c
    (∀ t, d.work.pos t=pos t) ∧
    (∀ z, cells d 0 z=AbsoluteTape.cells
      (⟨pre,resultWord sub carry xs++tail⟩ : Tape Bool).denote (pos 0) z) ∧
    (∀ z, cells d 1 z=.blank) ∧ d.inputPos=ip ∧ d.outRev=out := by
  dsimp only
  unfold run
  rw [RawRowArithmetic.bank_seed]
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
  rw [RawRowArithmetic.scheduleWithCarry_exact sub carry m xs
    (List.replicate xs.length .blank) pre [] tail [] (by simp)]
  have hl := CoupledRowScan.evaluate_lengths (RawRowArithmetic.update sub) carry xs.reverse
    (List.replicate xs.length .blank) (by simp)
  simp only [List.length_reverse] at hl
  simp only [RawRowArithmetic.finalWithCarry,RawRowArithmetic.finalWithUpdate,List.reverse_replicate,List.append_nil]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro t
    rw [ScheduledBankCleanup.run_position]
    simp [cfg,RawRowArithmetic.bankOnly]
  · intro z
    rw [ScheduledBankCleanup.run_cells]
    simpa [cells,cfg,RawRowArithmetic.bankOnly,resultWord,hl.1] using
      ZipperListCells.end_cells
        (CoupledRowScan.evaluate (RawRowArithmetic.update sub) carry xs.reverse
          (List.replicate xs.length .blank)).2.1.reverse pre tail (pos 0) z
  · apply ScheduledBankCleanup.run_clean
    intro z hz
    have hh : ¬(pos 1 ≤ z ∧ z < pos 1+
        (CoupledRowScan.evaluate (RawRowArithmetic.update sub) carry xs.reverse
          (List.replicate xs.length .blank)).2.2.reverse.length) := by
      simpa [cfg,RawRowArithmetic.bankOnly,hl.2] using hz
    simpa [cells,cfg,RawRowArithmetic.bankOnly] using ZipperListCells.front_outside
      (CoupledRowScan.evaluate (RawRowArithmetic.update sub) carry xs.reverse
        (List.replicate xs.length .blank)).2.2.reverse (pos 1) z hh
  · exact (ScheduledBankCleanup.run_io _ _ w _).1
  · exact (ScheduledBankCleanup.run_io _ _ w _).2

def word (P : ℕ) (x : ℕ → Sym Bool) : List (Sym Bool) := List.ofFn (fun i : Fin P => x i)

def value (sub carry : Bool) (P : ℕ) (x : ℕ → Sym Bool) (j : ℕ) : Sym Bool :=
  (resultWord sub carry (word P x)).getI j

theorem value_congr (sub carry : Bool) (P : ℕ) : BankWord.Congruent P (value sub carry P) := by
  intro x y hxy j _
  have hw : word P x=word P y := by
    unfold word
    congr 1
    funext i
    exact hxy i i.isLt
  rw [value,value,hw]

theorem represents (sub carry : Bool) (P : ℕ) (w : List Bool) (c : State)
    (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols P c (run sub carry P w c)
      (value sub carry P (BankWord.input BankWord.symbols c)) := by
  let xs := word P (BankWord.input BankWord.symbols c)
  have hl : xs.length=P := List.length_ofFn
  obtain ⟨pre,tail,he⟩ := RawRowArithmetic.clean_representation P 1 c hc
  have he' : c=RawRowArithmetic.bankStart c.work.core.pc [xs] pre tail
      c.work.pos c.inputPos c.outRev := by
    simpa [TapeWindow.rows,List.ofFn_succ,xs,word] using he
  have h := bank_spec sub carry xs pre tail c.work.core.pc c.work.pos c.inputPos c.outRev w
  dsimp only at h
  rw [hl,← he'] at h
  refine ⟨h.1,?_,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩
  intro j hj
  change cells (run sub carry P w c) 0 (c.work.pos 0+j)=_
  rw [h.2.1]
  exact TapeWindow.window_cell pre (resultWord sub carry xs) tail (c.work.pos 0) j
    (by rw [resultWord_length,hl]; exact hj)

end TransposeFollowup.RawCarryBank

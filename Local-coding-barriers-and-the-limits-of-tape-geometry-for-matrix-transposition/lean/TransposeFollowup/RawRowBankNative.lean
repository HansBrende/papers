import TransposeFollowup.RawRowArithmeticBank

/-! The clean bank update compiled into the original TM, including its
exact stopping time and complete absolute-tape endpoint. External raw
input loading/output emission is not included in this bank subroutine. -/
namespace TransposeFollowup.RawRowArithmetic
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open CopyMachine (Sym Tape)
open CoupledRowCell (Mode State)
set_option autoImplicit false
variable {k q : ℕ}

theorem bank_resources (sub : Bool) (W r : ℕ) :
    let e := NativeMicrocode.initialEncoding (T:=Fin 2)
      ((⟨0,by omega⟩,(sub,Sym.blank,Sym.blank)) : Fin (bankTicks W r+1) × Mode)
    let M := NativeIO.machine e (program (bankSchedule sub W r) (bankTicks W r))
    M.k=2 ∧ M.g+1=5 ∧ M.q+1=(bankTicks W r+1)*50 := by
  refine ⟨rfl,rfl,?_⟩
  have hc : Fintype.card Mode=50 := by decide +kernel
  simpa only [hc] using native_state_count (T:=Fin 2)
    (bankSchedule sub W r) (bankTicks W r) (sub,Sym.blank,Sym.blank)

theorem bank_native_complete (sub : Bool) (W r : ℕ)
    (e : NativeMicrocode.Encoding (Fin 2) (Fin (bankTicks W r+1) × Mode) k q)
    (w : List Bool) (c : State) :
    let p := program (bankSchedule sub W r) (bankTicks W r)
    Transpose.stepN (NativeIO.machine e p) w (bankTicks W r)
      ((lift ⟨0,by omega⟩ c).denote e p)=
      some ((lift ⟨bankTicks W r,by omega⟩ (bankRun sub W r w c)).denote e p) ∧
    Transpose.step (NativeIO.machine e p) w
      ((lift ⟨bankTicks W r,by omega⟩ (bankRun sub W r w c)).denote e p)=none := by
  have ht := native_run_and_halt e (bankSchedule sub W r) w c
    (fun i _ => bank_active sub W r i _)
  simpa only [bank_exact] using ht

theorem bank_native_spec (sub : Bool) (W : ℕ) (rows : List (List (Sym Bool)))
    (hw : ∀ xs ∈ rows, xs.length=W) (m : Mode) (pre suffix : List (Sym Bool))
    (e : NativeMicrocode.Encoding (Fin 2) (Fin (bankTicks W rows.length+1) × Mode) k q)
    (pos : Fin 2 → ℤ) (ip : ℤ) (out w : List Bool) :
    let p := program (bankSchedule sub W rows.length) (bankTicks W rows.length)
    ∃ d : Transpose.Config (NativeIO.machine e p),
      Transpose.stepN (NativeIO.machine e p) w (bankTicks W rows.length)
        ((lift ⟨0,by omega⟩ (bankStart m rows pre suffix pos ip out)).denote e p)=some d ∧
      Transpose.step (NativeIO.machine e p) w d=none ∧
      (∀ t : Fin 2, d.workPos (e.port t)=pos t) ∧
      (∀ z, d.work (e.port 0) z=NativeMicrocode.symbolCode (AbsoluteTape.cells
        (⟨pre,bankOutput sub W rows++suffix⟩ : Tape Bool).denote (pos 0) z)) ∧
      (∀ z, d.work (e.port 1) z=0) ∧ d.inPos=ip ∧ d.outRev=out := by
  have hn := bank_native_complete sub W rows.length e w (bankStart m rows pre suffix pos ip out)
  have hs := bank_spec sub W rows hw m pre suffix pos ip out w
  refine ⟨_,hn.1,hn.2,?_,?_,?_,hs.2.2.2.1,hs.2.2.2.2⟩
  · intro t
    simpa only [NativeIO.Config.denote,lift,Equiv.symm_apply_apply] using hs.1 t
  · intro z
    change NativeMicrocode.symbolCode (cells
      (bankRun sub W rows.length w (bankStart m rows pre suffix pos ip out))
      (e.port.symm (e.port 0)) z)=_
    rw [Equiv.symm_apply_apply,hs.2.1]
  · intro z
    change NativeMicrocode.symbolCode (cells
      (bankRun sub W rows.length w (bankStart m rows pre suffix pos ip out))
      (e.port.symm (e.port 1)) z)=0
    rw [Equiv.symm_apply_apply,hs.2.2.1]
    rfl

end TransposeFollowup.RawRowArithmetic

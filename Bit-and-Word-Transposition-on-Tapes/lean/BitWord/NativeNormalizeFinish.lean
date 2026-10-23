import BitWord.NativeNormalizeCalls

namespace BitWord.NativeNormalize
open FixedTapeCompiler CopyMachine TransposeFollowup NativeExpanderShearFrames NativeCountedLoop
set_option autoImplicit false

@[simp] theorem update_bank_zero (s a b z : Tape Bool) (d D h B : ℕ) :
    Function.update (bank s a b d D h B) (0:Port) z=bank z a b d D h B := by
  funext p; fin_cases p <;> rfl
@[simp] theorem update_bank_one (s a b z : Tape Bool) (d D h B : ℕ) :
    Function.update (bank s a b d D h B) (1:Port) z=bank s z b d D h B := by
  funext p; fin_cases p <;> rfl
@[simp] theorem update_bank_two (s a b z : Tape Bool) (d D h B : ℕ) :
    Function.update (bank s a b d D h B) (2:Port) z=bank s a z d D h B := by
  funext p; fin_cases p <;> rfl

/-- The overwritten input and both temporary banks are erased by actual calls.
The retained transformed copy is returned to the original main tape. -/
theorem finish_trace (expand : Bool) (xs mid ys : List Bool) (d D h B : ℕ) (pos : Port → ℤ) :
    ∃ t≤4*xs.length+4*mid.length+10*ys.length+30,Trace expand t
      (cfg (.erase 0 2) (bank (Counter.marked xs) (Counter.marked mid) (Counter.marked ys) d D h B) pos)
      (cfg .done (bank (Counter.marked ys) ⟨[],[]⟩ ⟨[],[]⟩ d D h B) pos) := by
  let b0 := bank (Counter.marked xs) (Counter.marked mid) (Counter.marked ys) d D h B
  let b1 := bank ⟨[],[]⟩ (Counter.marked mid) (Counter.marked ys) d D h B
  let b2 := bank (Counter.marked ys) (Counter.marked mid) (Counter.marked ys) d D h B
  let b3 := bank (Counter.marked ys) ⟨[],[]⟩ (Counter.marked ys) d D h B
  let b4 := bank (Counter.marked ys) ⟨[],[]⟩ ⟨[],[]⟩ d D h B
  obtain ⟨t0,h0,tr0⟩ : ∃ t≤4*xs.length+4,Trace expand t
      (cfg (.erase 0 2) b0 pos) (cfg (.erase 0 0) b1 pos) := by
    simpa only [b0,b1,update_bank_zero] using NativeTapeCalls.erase (program expand)
      (0:Port) (Label.erase 0) (erase_code expand 0) b0 pos xs rfl
  have j0 := jump expand (.erase 0 0) (.copy (.init (.erase 0))) b1 pos rfl
  obtain ⟨t1,h1,tr1⟩ : ∃ t≤6*ys.length+14,Trace expand t
      (cfg (.copy (.init (.erase 0))) b1 pos) (cfg (.copy (.seal .done)) b2 pos) := by
    simpa only [b1,b2,update_bank_zero] using copy_call expand ys b1 pos rfl rfl
  have j1 := jump expand (.copy (.seal .done)) (.erase 1 2) b2 pos rfl
  obtain ⟨t2,h2,tr2⟩ : ∃ t≤4*mid.length+4,Trace expand t
      (cfg (.erase 1 2) b2 pos) (cfg (.erase 1 0) b3 pos) := by
    simpa only [b2,b3,update_bank_one] using NativeTapeCalls.erase (program expand)
      (1:Port) (Label.erase 1) (erase_code expand 1) b2 pos mid rfl
  have j2 := jump expand (.erase 1 0) (.erase 2 2) b3 pos rfl
  obtain ⟨t3,h3,tr3⟩ : ∃ t≤4*ys.length+4,Trace expand t
      (cfg (.erase 2 2) b3 pos) (cfg (.erase 2 0) b4 pos) := by
    simpa only [b3,b4,update_bank_two] using NativeTapeCalls.erase (program expand)
      (2:Port) (Label.erase 2) (erase_code expand 2) b3 pos ys rfl
  have j3 := jump expand (.erase 2 0) .done b4 pos rfl
  have t01 := trace_trans (trace_trans tr0 j0) (trace_trans tr1 j1)
  have t23 := trace_trans (trace_trans tr2 j2) (trace_trans tr3 j3)
  exact ⟨_,by omega,trace_trans t01 t23⟩

end BitWord.NativeNormalize

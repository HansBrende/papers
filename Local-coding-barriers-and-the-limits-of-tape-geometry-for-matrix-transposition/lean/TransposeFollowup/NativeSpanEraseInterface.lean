import TransposeFollowup.NativeSpanErase

namespace TransposeFollowup.NativeSpanErase
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def start (atEnd : Bool) : Label:=if atEnd then .left else .scan
def inputTape (atEnd : Bool) (xs : List (Sym Bool)) : Tape Bool:=
  if atEnd then ⟨xs.reverse,[]⟩ else ⟨[],xs⟩
def inputPosition (atEnd : Bool) (xs : List (Sym Bool)) (pos : Fin 1 → ℤ) : Fin 1 → ℤ:=
  if atEnd then (fun p => pos p+xs.length) else pos
def budget (atEnd : Bool) (m : ℕ) : ℕ:=if atEnd then 3*m+3 else 5*m+4

theorem complete_trace (atEnd : Bool) (xs : List (Sym Bool)) (h : ∀ s ∈ xs,s≠.blank)
    (pos : Fin 1 → ℤ) :
    ∃ t ≤ budget atEnd xs.length,
      OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
        (cfg (start atEnd) (inputTape atEnd xs) (inputPosition atEnd xs pos)).denote
        (cfg .done ⟨[],[]⟩ pos).denote := by
  cases atEnd with
  | false => exact from_start_trace xs h pos
  | true =>
    have he : (fun p => pos p+(xs.length:ℤ)-xs.length)=pos:=by funext p;ring
    simpa only [start,inputTape,inputPosition,budget,ite_true,he] using
      from_end_trace xs h (fun p => pos p+xs.length)

noncomputable def nativeEncoding (atEnd : Bool):=NativeMicrocode.initialEncoding (T:=Fin 1) (start atEnd)
noncomputable def nativeMachine (atEnd : Bool):=NativeMicrocode.machine (nativeEncoding atEnd) program

theorem fixed_resources (atEnd : Bool) : (nativeMachine atEnd).k=1 ∧ (nativeMachine atEnd).g+1=5 ∧
    (nativeMachine atEnd).q+1=7 ∧ (nativeEncoding atEnd).label (start atEnd)=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card Label-1+1=7
  decide +kernel

theorem native_erase (atEnd : Bool) (xs : List (Sym Bool)) (h : ∀ s ∈ xs,s≠.blank)
    (pos : Fin 1 → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget atEnd xs.length,
      Transpose.stepN (nativeMachine atEnd) w t
        ((cfg (start atEnd) (inputTape atEnd xs) (inputPosition atEnd xs pos)).denote.denote
          (nativeEncoding atEnd) program ip outRev)=
        some ((cfg .done ⟨[],[]⟩ pos).denote.denote (nativeEncoding atEnd) program ip outRev) ∧
      Transpose.step (nativeMachine atEnd) w
        ((cfg .done ⟨[],[]⟩ pos).denote.denote (nativeEncoding atEnd) program ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=complete_trace atEnd xs h pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding atEnd) program w ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding atEnd) program w ip outRev _).mpr
  simp [NativeMicrocode.Active,NativeZipper.Config.denote,Microcode.Config.denote,cfg,program]

end TransposeFollowup.NativeSpanErase

import BitWord.NativeNormalizeFinish

namespace BitWord.NativeNormalize
open FixedTapeCompiler CopyMachine TransposeFollowup NativeExpanderShearFrames NativeCountedLoop
open Transpose
set_option autoImplicit false

def smallWord (d h : ℕ) (A : Matrix) := encode d h A
def middleWord (d h B : ℕ) (A : Matrix) := encode d B (widenMatrix h A)
def largeWord (d D h B : ℕ) (A : Matrix) := encode D B (padSquare d (widenMatrix h A))

theorem expand_phase (d D h B : ℕ) (hd : d≤D) (hh : 0<h) (hB : h≤B) (hD : 0<D)
    (A : Matrix) (pos : Port → ℤ) :
    ∃ t≤24*(d*d*B)+40*(D*D*B)+62,Trace true t
      (cfg (start true) (bank (Counter.marked (smallWord d h A)) ⟨[],[]⟩ ⟨[],[]⟩ d D h B) pos)
      (cfg (.erase 0 2) (bank (Counter.marked (smallWord d h A))
        (Counter.marked (middleWord d h B A)) (Counter.marked (largeWord d D h B A)) d D h B) pos) := by
  have hw : h+(B-h)=B := Nat.add_sub_of_le hB
  have hr : d*B+(D-d)*B=D*B := by rw [←Nat.add_mul,Nat.add_sub_of_le hd]
  have hc : d+(D-d)=D := Nat.add_sub_of_le hd
  have hp : 0<D*B := Nat.mul_pos hD (by omega)
  let xs := smallWord d h A
  let ys := middleWord d h B A
  let zs := largeWord d D h B A
  let b0 := bank (Counter.marked xs) ⟨[],[]⟩ ⟨[],[]⟩ d D h B
  let b1 := bank (Counter.marked xs) (Counter.marked ys) ⟨[],[]⟩ d D h B
  let b2 := bank (Counter.marked xs) (Counter.marked ys) (Counter.marked zs) d D h B
  obtain ⟨t0,h0,tr0⟩ : ∃ t≤24*(d*d*B)+20,Trace true t
      (cfg (start true) b0 pos) (cfg (.resize .done) b1 pos) := by
    have ht := resize_call true h (B-h) hh (expansionRecords d h B A)
      (expansionRecords_lengths d h B A) b0 pos
      (by simp [b0,bank,resizePorts,xs,smallWord,expansionRecords_input]) rfl rfl (by simp [b0,bank,hw])
    simpa only [expansionRecords_count,hw,expansionRecords_output d h B hB A,
      resizePorts,ite_true,Matrix.cons_val_one,Matrix.cons_val_zero,update_bank_one,
      start,ys,middleWord,b0,b1] using ht
  have j0 := jump true (.resize .done) (.square NativeSquare.start) b1 pos rfl
  obtain ⟨t1,h1,tr1⟩ : ∃ t≤40*(D*D*B)+40,Trace true t
      (cfg (.square NativeSquare.start) b1 pos) (cfg (.square .done) b2 pos) := by
    have hi := (square_expansion_layout (b:=B) hd (widenMatrix h A)).1
    have ho := (square_expansion_layout (b:=B) hd (widenMatrix h A)).2
    have ht := square_call true (d*B) ((D-d)*B) (by simpa only [hr] using hp)
      (squareRowRecords d D B (widenMatrix h A)) (squareExtraRows d D B)
      (squareRowRecords_lengths d D B (widenMatrix h A))
      (by simpa only [hr] using squareExtraRows_width d D B) b1 pos
      (by simpa only [NativeSquare.inputSquare,NativeSquare.tailInputs,hi,ys,middleWord] using (show b1 (squarePorts true 0)=Counter.marked ys from rfl))
      rfl rfl (by simp [b1,bank,hr])
      (by simp [b1,bank,squareRowRecords_count])
      (by simp [b1,bank,squareRowRecords_count,squareExtraRows_count,hc])
    simpa only [squareRowRecords_count,squareExtraRows_count,hc,hr,Nat.mul_assoc,
      NativeSquare.outputSquare,NativeSquare.tailOutputs,ho,squarePorts,ite_true,
      Matrix.cons_val_one,Matrix.cons_val_zero,update_bank_two,zs,largeWord,b1,b2] using ht
  have j1 := jump true (.square .done) (.erase 0 2) b2 pos rfl
  exact ⟨_,by omega,trace_trans (trace_trans tr0 j0) (trace_trans tr1 j1)⟩

theorem crop_phase (d D h B : ℕ) (hd : d≤D) (hh : 0<h) (hB : h≤B) (hD : 0<D)
    (A : Matrix) (pos : Port → ℤ) :
    ∃ t≤40*(D*D*B)+24*(d*d*B)+62,Trace false t
      (cfg (start false) (bank (Counter.marked (largeWord d D h B A)) ⟨[],[]⟩ ⟨[],[]⟩ d D h B) pos)
      (cfg (.erase 0 2) (bank (Counter.marked (largeWord d D h B A))
        (Counter.marked (middleWord d h B A)) (Counter.marked (smallWord d h A)) d D h B) pos) := by
  have hw : h+(B-h)=B := Nat.add_sub_of_le hB
  have hr : d*B+(D-d)*B=D*B := by rw [←Nat.add_mul,Nat.add_sub_of_le hd]
  have hc : d+(D-d)=D := Nat.add_sub_of_le hd
  have hp : 0<D*B := Nat.mul_pos hD (by omega)
  let xs := largeWord d D h B A
  let ys := middleWord d h B A
  let zs := smallWord d h A
  let b0 := bank (Counter.marked xs) ⟨[],[]⟩ ⟨[],[]⟩ d D h B
  let b1 := bank (Counter.marked xs) (Counter.marked ys) ⟨[],[]⟩ d D h B
  let b2 := bank (Counter.marked xs) (Counter.marked ys) (Counter.marked zs) d D h B
  obtain ⟨t0,h0,tr0⟩ : ∃ t≤40*(D*D*B)+40,Trace false t
      (cfg (start false) b0 pos) (cfg (.square .done) b1 pos) := by
    have hi := (square_cropping_layout (b:=B) hd (widenMatrix h A)).1
    have ho := (square_cropping_layout (b:=B) hd (widenMatrix h A)).2
    have ht := square_call false (d*B) ((D-d)*B) (by simpa only [hr] using hp)
      (squareRowRecords d D B (widenMatrix h A)) (squareExtraRows d D B)
      (squareRowRecords_lengths d D B (widenMatrix h A))
      (by simpa only [hr] using squareExtraRows_width d D B) b0 pos
      (by simpa only [NativeSquare.inputSquare,NativeSquare.tailInputs,hi,xs,largeWord] using (show b0 (squarePorts false 0)=Counter.marked xs from rfl))
      rfl rfl (by simp [b0,bank,hr])
      (by simp [b0,bank,squareRowRecords_count])
      (by simp [b0,bank,squareRowRecords_count,squareExtraRows_count,hc])
    simpa only [squareRowRecords_count,squareExtraRows_count,hc,hr,Nat.mul_assoc,
      NativeSquare.outputSquare,NativeSquare.tailOutputs,ho,squarePorts,Bool.false_eq_true,ite_false,
      Matrix.cons_val_one,Matrix.cons_val_zero,update_bank_one,start,ys,middleWord,b0,b1] using ht
  have j0 := jump false (.square .done) (.resize NativeResize.start) b1 pos rfl
  obtain ⟨t1,h1,tr1⟩ : ∃ t≤24*(d*d*B)+20,Trace false t
      (cfg (.resize NativeResize.start) b1 pos) (cfg (.resize .done) b2 pos) := by
    have ht := resize_call false h (B-h) hh (cropRecords d h B (widenMatrix h A))
      (cropRecords_lengths d h B hB (widenMatrix h A)) b1 pos
      (by simp [b1,bank,resizePorts,ys,middleWord,cropRecords_input]) rfl rfl (by simp [b1,bank,hw])
    simpa only [cropRecords_count,hw,cropRecords_output d h B hB (widenMatrix h A),
      widen_encode_original,resizePorts,Bool.false_eq_true,ite_false,Matrix.cons_val_one,Matrix.cons_val_zero,
      update_bank_two,zs,smallWord,b1,b2] using ht
  have j1 := jump false (.resize .done) (.erase 0 2) b2 pos rfl
  exact ⟨_,by omega,trace_trans (trace_trans tr0 j0) (trace_trans tr1 j1)⟩

end BitWord.NativeNormalize

namespace BitWord.NativeNormalize
open FixedTapeCompiler CopyMachine TransposeFollowup NativeExpanderShearFrames NativeCountedLoop
open Transpose
set_option autoImplicit false

def inputWord (expand : Bool) (d D h B : ℕ) (A : Matrix) : List Bool :=
  if expand then smallWord d h A else largeWord d D h B A

def outputWord (expand : Bool) (d D h B : ℕ) (A : Matrix) : List Bool :=
  if expand then largeWord d D h B A else smallWord d h A

/-- Both physical passes, their linking jumps, and all cleanup are charged.
The finite program is independent of every numerical parameter. -/
theorem complete_trace (expand : Bool) (d D h B : ℕ)
    (hd : d≤D) (hh : 0<h) (hB : h≤B) (hD : 0<D)
    (A : Matrix) (pos : Port → ℤ) :
    ∃ t≤200*(D*D*B)+200,Trace expand t
      (cfg (start expand) (bank (Counter.marked (inputWord expand d D h B A)) ⟨[],[]⟩ ⟨[],[]⟩ d D h B) pos)
      (cfg .done (bank (Counter.marked (outputWord expand d D h B A)) ⟨[],[]⟩ ⟨[],[]⟩ d D h B) pos) := by
  have hm : d*d*B≤D*D*B := Nat.mul_le_mul_right B (Nat.mul_le_mul hd hd)
  have hs : d*d*h≤D*D*B := Nat.mul_le_mul (Nat.mul_le_mul hd hd) hB
  cases expand with
  | true =>
    obtain ⟨a,ha,ta⟩ := expand_phase d D h B hd hh hB hD A pos
    obtain ⟨b,hb,tb⟩ := finish_trace true (smallWord d h A) (middleWord d h B A)
      (largeWord d D h B A) d D h B pos
    refine ⟨a+b,?_,trace_trans ta tb⟩
    simp only [smallWord,middleWord,largeWord,Tape.Impl.length_encode] at hb
    omega
  | false =>
    obtain ⟨a,ha,ta⟩ := crop_phase d D h B hd hh hB hD A pos
    obtain ⟨b,hb,tb⟩ := finish_trace false (largeWord d D h B A) (middleWord d h B A)
      (smallWord d h A) d D h B pos
    refine ⟨a+b,?_,trace_trans ta tb⟩
    simp only [smallWord,middleWord,largeWord,Tape.Impl.length_encode] at hb
    omega

noncomputable def nativeEncoding (expand : Bool) := NativeMicrocode.initialEncoding (T:=Port) (start expand)
noncomputable def nativeMachine (expand : Bool) := NativeMicrocode.machine (nativeEncoding expand) (program expand)

theorem native_normalize (expand : Bool) (d D h B : ℕ)
    (hd : d≤D) (hh : 0<h) (hB : h≤B) (hD : 0<D)
    (A : Matrix) (pos : Port → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t≤200*(D*D*B)+200,Transpose.stepN (nativeMachine expand) input t
      ((cfg (start expand) (bank (Counter.marked (inputWord expand d D h B A)) ⟨[],[]⟩ ⟨[],[]⟩ d D h B) pos).denote
        (nativeEncoding expand) (program expand) inputPos outRev)=
      some ((cfg .done (bank (Counter.marked (outputWord expand d D h B A)) ⟨[],[]⟩ ⟨[],[]⟩ d D h B) pos).denote
        (nativeEncoding expand) (program expand) inputPos outRev) ∧
      Transpose.step (nativeMachine expand) input
        ((cfg .done (bank (Counter.marked (outputWord expand d D h B A)) ⟨[],[]⟩ ⟨[],[]⟩ d D h B) pos).denote
          (nativeEncoding expand) (program expand) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace expand d D h B hd hh hB hD A pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding expand) (program expand) input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding expand) (program expand) input inputPos outRev _).mpr
  intro hc
  exact hc.1 rfl

theorem fixed_resources (expand : Bool) : (nativeMachine expand).k=9 ∧
    (nativeMachine expand).g+1=5 ∧ (nativeEncoding expand).label (start expand)=0 := by
  exact ⟨rfl,rfl,NativeMicrocode.initialEncoding_start _⟩

end BitWord.NativeNormalize

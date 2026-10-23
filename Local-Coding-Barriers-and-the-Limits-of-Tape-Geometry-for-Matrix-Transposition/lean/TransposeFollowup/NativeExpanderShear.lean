import TransposeFollowup.NativeExpanderShearCalls
import TransposeFollowup.NativeExpanderShearNumerics
import TransposeFollowup.ExpanderShearEncoding

/-! A single uniform finite-tape machine computes the rational expander shear
from its raw input. Dimension discovery, rational matching generation, mask
layout, unary row clocks, payload movement, XOR passes, and raw output are all
included in the actual execution trace. -/
namespace TransposeFollowup.NativeExpanderShearMachine
open FixedTapeCompiler CopyMachine
open NativeExpanderShearFrames ExpanderShearOpcodeBridge ExpanderShear
set_option autoImplicit false
variable {r : ℕ}

def coefficient (F : Fin (r+1) → RationalMobius) : ℕ :=
  NativeExpanderShearMetadata.coefficient F+10000*(rationalPageCount F+1)

noncomputable def outputBank {m W : ℕ} (F : Fin (r+1) → RationalMobius) (x : BoolBank m W) : List Bool :=
  rawBank (boolShear (fun j i => if (i,j)∈overlapEdges (rationalFamilyMaps F) m then 1 else 0) x)

theorem complete_trace (F : Fin (r+1) → RationalMobius) (m : ℕ) (hm : 1 ≤ m)
    (x : BoolBank m ((2*m)*Transpose.entryBits (2*m))) :
    ∃ t ≤ coefficient F*Transpose.inputLength (2*m), ∃ s pos,
      Trace F (rawBank x) t (cfg (start F) blank (fun _ => 0) 0 [])
        (cfg (.data (.emit .done)) s pos (rawBank x).length (outputBank F x).reverse) := by
  let W := (2*m)*Transpose.entryBits (2*m)
  let A := rawHalf (fun i => x (.inl i))
  let B := rawHalf (fun j => x (.inr j))
  have hA : A.length=m*W := rawHalf_length _
  have hB : B.length=A.length := by simp [A,B]
  have hw : (rawBank x).length=Transpose.inputLength (2*m) := by
    simp only [rawBank_length,Transpose.inputLength]
    ring
  have hd : 2≤2*m := by omega
  obtain ⟨xs,ms,hx,hv,hl,hy,hyv,hyl,t,ht,tm⟩ := metadata_call F (rawBank x) (2*m) hd hw
  have hvx : 0<Counter.value xs := by omega
  have hvm : Counter.value ms=m := by simpa using hyv
  have hml : ms.length=m.size := by simpa using hyl
  have hclock : (ExpanderShearClock.word xs).length=W := by simp [ExpanderShearClock.word_length,hv,W]
  obtain ⟨u,hu,tp⟩ := prepare_call F (rawBank x) xs ms m hvx hvm
  have hvalid : NativeMatchingXorPages.ValidTags A.length (sourceTags F m W) (targetTags F m W) :=
    NativeExpanderShearSemantics.valid_tags
      (fun p (i : Fin m) => rationalOutgoingOn F i p)
      (fun p (j : Fin m) => rationalIncomingOn F j p)
      (fun p => (rational_page_masks F p).1) x
  have hproject := prepared_data_projection F A B xs ms m W hclock
  obtain ⟨v,hv',td⟩ := data_call F (rawBank x) (preparedBank F (rawBank x) xs ms m)
    (preparedPos F ms m) A B (sourceTags F m W) (targetTags F m W) hB hvalid hproject
  have j1 : Trace F (rawBank x) 1
      (cfg (.metadata (.generate (.schedule .done))) (metadataBank F (rawBank x) xs ms) (metadataPos F ms) (rawBank x).length [])
      (cfg (.prep NativeExpanderShearPrepare.start) (metadataBank F (rawBank x) xs ms) (metadataPos F ms) (rawBank x).length []) :=
    NativeIO.jump_trace (program F) (rawBank x) _ _ rfl
  have j2 : Trace F (rawBank x) 1
      (cfg (.prep .done) (preparedBank F (rawBank x) xs ms m) (preparedPos F ms m) (rawBank x).length [])
      (cfg (.data (NativeMatchingXorData.start (rationalPageCount F)))
        (preparedBank F (rawBank x) xs ms m) (preparedPos F ms m) (rawBank x).length []) :=
    NativeIO.jump_trace (program F) (rawBank x) _ _ rfl
  have hout : A++NativeMatchingXorPages.output A B (sourceTags F m W) (targetTags F m W) (rationalPageCount F)=outputBank F x := by
    rw [show NativeMatchingXorPages.output A B (sourceTags F m W) (targetTags F m W) (rationalPageCount F)=
      rawHalf (fun j => boolShear (fun j i => if (i,j)∈overlapEdges (rationalFamilyMaps F) m then 1 else 0) x (.inr j)) from
      NativeExpanderShearSemantics.rational_output F x]
    simp only [outputBank,rawBank,A,List.append_left_inj]
    apply congrArg rawHalf
    funext i
    exact (boolShear_left _ x i).symm
  rw [hout] at td
  have hW : 1≤W := by
    have hb : 1≤Transpose.entryBits (2*m) := by rw [EntryBits.entryBits_eq]; omega
    dsimp [W]; nlinarith
  have hsize : xs.length≤Counter.value xs := by
    rw [hl,hv]; exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hc : ExpanderShearClock.budget xs≤1200*W := by
    simpa only [hv] using ExpanderShearClock.budget_linear xs hvx hsize
  have hms : ms.length≤ m := by rw [hml]; exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hbits : (NativeMatchingXorMasks.encode (sourceRows F m++targetRows F m)).length=4*m*rationalPageCount F := by
    rw [←encoded_tape]
    simpa only [hvm] using OpcodeGenerator.encoded_length F ms
  have hn := NativeExpanderShearNumerics.total_budget_le m W (rationalPageCount F)
    (NativeExpanderShearMetadata.coefficient F) (ExpanderShearClock.budget xs) ms.length hm hW hc hms
  rw [rawBank_length] at ht
  rw [NativeExpanderShearPrepare.budget,hbits,hclock] at hu
  rw [hA] at hv'
  refine ⟨t+(1+(u+(1+v))),?_,_,_,NativeCountedLoop.trace_trans tm
    (NativeCountedLoop.trace_trans j1 (NativeCountedLoop.trace_trans tp (NativeCountedLoop.trace_trans j2 td)))⟩
  rw [←hw,rawBank_length]
  change _≤(NativeExpanderShearMetadata.coefficient F+10000*(rationalPageCount F+1))*(2*m*W)
  change t ≤ NativeExpanderShearMetadata.coefficient F*(2*m*W) at ht
  have hvn : v ≤ rationalPageCount F*(8*m*W+8)+24*m*W+28 := by
    simpa only [Nat.mul_assoc] using hv'
  have hs := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add ht hu) hvn) 2
  calc
    t+(1+(u+(1+v))) = t+u+v+2 := by omega
    _ ≤ _ := hs
    _ ≤ _ := hn

noncomputable def nativeEncoding (F : Fin (r+1) → RationalMobius) :=
  NativeMicrocode.initialEncoding (T:=Port (rationalPageCount F)) (start F)
noncomputable def nativeMachine (F : Fin (r+1) → RationalMobius) :=
  NativeIO.machine (nativeEncoding F) (program F)

/-- Actual blank-initial-workspace execution, with correct emitted bits and a
halting terminal configuration. No final scratch-erasure premise is imposed. -/
theorem native_shear (F : Fin (r+1) → RationalMobius) (m : ℕ) (hm : 1 ≤ m)
    (x : BoolBank m ((2*m)*Transpose.entryBits (2*m))) :
    ∃ t ≤ coefficient F*Transpose.inputLength (2*m), ∃ c,
      Transpose.stepN (nativeMachine F) (rawBank x) t (Transpose.init (nativeMachine F))=some c ∧
      Transpose.step (nativeMachine F) (rawBank x) c=none ∧ c.outRev=(outputBank F x).reverse := by
  obtain ⟨t,ht,s,pos,htr⟩ := complete_trace F m hm x
  let final := cfg (Label.data (F:=F) (.emit .done)) s pos (rawBank x).length (outputBank F x).reverse
  refine ⟨t,ht,final.denote (nativeEncoding F) (program F),?_,?_,rfl⟩
  · have hi : (cfg (start F) blank (fun _ => 0) 0 []).denote (nativeEncoding F) (program F)=
        Transpose.init (nativeMachine F) :=
      NativeIO.blank_denote (nativeEncoding F) (program F) (start F) (NativeMicrocode.initialEncoding_start _)
    rw [←hi]
    exact NativeIO.trace_stepN (nativeEncoding F) (program F) (rawBank x) htr
  · apply (NativeIO.step_none_iff (nativeEncoding F) (program F) (rawBank x) final).mpr
    simp [final,NativeIO.Active,cfg,workCfg,program,NativeIOEmbedding.boundInstruction,
      NativeMatchingXorData.program,NativeMatchingXorOutput.program,FinitePortBinding.instruction]

theorem fixed_resources (F : Fin (r+1) → RationalMobius) :
    (nativeMachine F).k=Fintype.card (Port (rationalPageCount F)) ∧ (nativeMachine F).g+1=5 ∧
      (nativeEncoding F).label (start F)=0 :=
  ⟨rfl,rfl,NativeMicrocode.initialEncoding_start _⟩

end TransposeFollowup.NativeExpanderShearMachine

import BitWord.NativeCanonicalParameters

namespace BitWord.NativeCanonicalParameters
open FixedTapeCompiler CopyMachine TransposeFollowup NativeExpanderShearFrames
open NativeBankCalls CanonicalMetadata
set_option autoImplicit false

private theorem values_changed {T : Type*} [DecidableEq T] (b : FinitePortBinding T Port)
    (s : Bank) (i : T) (x : Tape Bool) :
    b.values (Function.update (fun t => s (b.ports t)) i x) s=
      Function.update s (b.ports i) x := by
  rw [←b.values_update,b.values_project]

theorem entry_call (h : ℕ) (hh : 2 ≤ h) (s : Bank) (pos : Port → ℤ)
    (hs : s .h=Counter.marked (hword h))
    (ha : s .tmpA=⟨[],[]⟩) (hb : s .tmpB=⟨[],[]⟩) (hu : s .u=⟨[],[]⟩) :
    ∃ t ≤ 50*h+87, Trace t (cfg start s pos)
      (cfg (.entry .done) (Function.update s .u (Counter.marked (uword h))) pos) := by
  obtain ⟨t,ht,htr⟩ := EntryBits.complete_trace (hword h) (by simp; omega)
    (fun p => pos (entryBinding.ports p))
  have hv : Transpose.entryBits (Counter.value (hword h))=laneBits h := by
    rw [hword_value,entryBits_eq_clog hh]; rfl
  have hi : EntryBits.initial (hword h)=fun p => s (entryBinding.ports p) := by
    funext p; fin_cases p <;> simp [EntryBits.initial,EntryBits.bank,entryBinding,hs,ha,hb,hu]
  have hf : EntryBits.final (hword h)=
      Function.update (fun p => s (entryBinding.ports p)) 3 (Counter.marked (uword h)) := by
    funext p; fin_cases p <;> simp [EntryBits.final,EntryBits.bank,entryBinding,hs,ha,hb,entryBits_eq_clog hh,uword,laneBits]
  have he := NativeBindingCalls.restoring_call entryBinding Label.entry EntryBits.program program entry_code
    EntryBits.start .done s pos _ t (by simpa only [EntryBits.cfg,workCfg,hi,hf] using htr)
  refine ⟨t,by simpa only [hword_length] using ht,?_⟩
  rw [values_changed,show entryBinding.ports 3=Port.u from rfl] at he
  simpa only [Trace,cfg,start] using he

theorem pad_call (second : Bool) (xs ys : List Bool) (s : Bank) (pos : Port → ℤ)
    (hx : s (padPorts second 0)=Counter.marked xs)
    (hy : s (padPorts second 1)=Counter.marked ys)
    (hz : s (padPorts second 2)=⟨[],[]⟩) :
    ∃ t ≤ 6*(xs.length+ys.length)+3*padding second+21,Trace t
      (cfg (.pad second (NativeCrossPad.start (padding second))) s pos)
      (cfg (.pad second (.tail (.seal .done)))
        (Function.update s (padPorts second 2) (Counter.marked (NativeCrossPad.padded (padding second) xs ys))) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeCrossPad.complete_trace (padding second) xs ys
    (fun p => pos ((padBinding second).ports p))
  have hi : (![Counter.marked xs,Counter.marked ys,⟨[],[]⟩] : Fin 3 → Tape Bool)=
      fun p => s ((padBinding second).ports p) := by
    funext p; fin_cases p <;> simp [padBinding,hx,hy,hz]
  have hf : (![Counter.marked xs,Counter.marked ys,Counter.marked (NativeCrossPad.padded (padding second) xs ys)] : Fin 3 → Tape Bool)=
      Function.update (fun p => s ((padBinding second).ports p)) 2
        (Counter.marked (NativeCrossPad.padded (padding second) xs ys)) := by
    funext p; fin_cases p <;> simp [padBinding,hx,hy]
  have he := NativeBindingCalls.restoring_call (padBinding second) (Label.pad second)
    (NativeCrossPad.program (padding second)) program (pad_code second) _ _ s pos _ t
      (by simpa only [hi,hf] using htr)
  rw [values_changed] at he
  exact ⟨t,ht,he⟩

theorem copy_call (second : Bool) (xs : List Bool) (s : Bank) (pos : Port → ℤ)
    (hx : s ((copyBinding second).ports 0)=Counter.marked xs)
    (hz : s ((copyBinding second).ports 1)=⟨[],[]⟩) :
    ∃ t ≤ 6*xs.length+14, Trace t (cfg (.copy second (.init (.erase 0))) s pos)
      (cfg (.copy second (.seal .done))
        (Function.update s ((copyBinding second).ports 1) (Counter.marked (xs.map (copyMap second)))) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace (copyMap second) xs
    (fun p => pos ((copyBinding second).ports p))
  have hi : NativeMappedCopy.bank (Counter.marked xs) ⟨[],[]⟩=
      fun p => s ((copyBinding second).ports p) := by
    funext p; fin_cases p <;> simp [NativeMappedCopy.bank,hx,hz]
  have hf : NativeMappedCopy.bank (Counter.marked xs) (Counter.marked (xs.map (copyMap second)))=
      Function.update (fun p => s ((copyBinding second).ports p)) 1 (Counter.marked (xs.map (copyMap second))) := by
    funext p; fin_cases p <;> simp [NativeMappedCopy.bank,hx]
  have he := NativeBindingCalls.restoring_call (copyBinding second) (Label.copy second)
    (NativeMappedCopy.program (copyMap second)) program (copy_code second) _ _ s pos _ t
      (by simpa only [NativeMappedCopy.cfg,workCfg,hi,hf] using htr)
  exact ⟨t,ht,by simpa only [values_changed] using he⟩

theorem arithmetic_call (o : Op) (xs ys : List Bool) (hlen : xs.length=ys.length)
    (s : Bank) (pos : Port → ℤ)
    (hx : s (operands o 0)=Counter.marked xs)
    (hy : s (operands o 1)=Counter.marked ys)
    (hz : s (operands o 2)=NativeSealBack.openWord []) :
    ∃ t ≤ 5*xs.length+7, Trace t (cfg (.arithmetic o (.scan (sub o) (carry o))) s pos)
      (cfg (.arithmetic o (.done (BinaryCarry.result (sub o) (carry o) xs ys).2))
        (Function.update s (operands o 2)
          (Counter.marked (BinaryCarry.result (sub o) (carry o) xs ys).1)) pos) := by
  obtain ⟨t,ht,htr⟩ := BinaryCarry.arithmetic_trace (sub o) (carry o) xs ys hlen
    (fun p => pos ((carryBinding o).ports p))
  have hi : BinaryCarry.bank (Counter.marked xs) (Counter.marked ys) BinaryCarry.preparedOutput=
      fun p => s ((carryBinding o).ports p) := by
    funext p; fin_cases p <;> simp [BinaryCarry.bank,carryBinding,hx,hy,hz,
      BinaryCarry.preparedOutput,NativeSealBack.openWord,symbols]
  have hf : BinaryCarry.bank (Counter.marked xs) (Counter.marked ys)
      (Counter.marked (BinaryCarry.result (sub o) (carry o) xs ys).1)=
      Function.update (fun p => s ((carryBinding o).ports p)) 2
        (Counter.marked (BinaryCarry.result (sub o) (carry o) xs ys).1) := by
    funext p; fin_cases p <;> simp [BinaryCarry.bank,carryBinding,hx,hy]
  have he := NativeBindingCalls.restoring_call (carryBinding o) (Label.arithmetic o)
    BinaryCarry.program program (arithmetic_code o) (.scan (sub o) (carry o))
    (.done (BinaryCarry.result (sub o) (carry o) xs ys).2) s pos
    (Function.update (fun p => s ((carryBinding o).ports p)) 2 (Counter.marked (BinaryCarry.result (sub o) (carry o) xs ys).1)) t
      (by simpa only [BinaryCarry.cfg,NativeZipper.Config.denote,Microcode.Config.denote,workCfg,BinaryCarry.marked,show ∀ z,BinaryCompare.marked z=Counter.marked z from fun _ => rfl,hi,hf] using htr)
  rw [values_changed] at he
  exact ⟨t,ht,he⟩

theorem half_call (a : Bool) (xs : List Bool) (s : Bank) (pos : Port → ℤ)
    (hs : s .inc=Counter.marked (a::xs)) :
    ∃ t ≤ 3, Trace t (cfg (.halve .left) s pos)
      (cfg (.halve .done) (Function.update s .inc (Counter.marked xs))
        (Function.update pos .inc (pos .inc+1))) := by
  obtain ⟨t,ht,htr⟩ := NativeExpanderShearHalf.half_trace a xs (fun _ => pos .inc)
  exact ⟨t,ht,call_single Port.inc Label.halve NativeExpanderShearHalf.program program half_code
    .left .done s pos (Counter.marked xs) (pos .inc+1) t
    (by simpa [workCfg,NativeExpanderShearHalf.cfg,NativeZipper.Config.denote,
      Microcode.Config.denote,Microcode.focus,hs] using htr)⟩

theorem batch_erase_call (words : Fin 4 → List Bool) (s : Bank) (pos : Port → ℤ)
    (hs : ∀ j,s (erasePorts j)=Counter.marked (words j)) :
    ∃ t ≤ ∑ j : Fin 4,(4*(words j).length+5), Trace t
      (cfg (.erase (NativeBatchErase.entry 4 0)) s pos)
      (cfg (.erase .done) (NativeBatchErase.stage erasePorts s 4) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeBatchErase.complete_trace erasePorts words s hs pos
  have he := NativeBindingCalls.restoring_call allBinding Label.erase (NativeBatchErase.program erasePorts)
    program erase_code _ _ s pos _ t htr
  have hv : allBinding.values (NativeBatchErase.stage erasePorts s 4) s=NativeBatchErase.stage erasePorts s 4 := by
    funext p; rfl
  rw [hv] at he
  exact ⟨t,ht,he⟩

end BitWord.NativeCanonicalParameters

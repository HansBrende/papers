import TransposeFollowup.NormalizedBatchMachine

namespace TransposeFollowup.NormalizedBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem embed_append (small pad : ℕ) (second : Bool) (pc : Microcode.MappedAppendFamily.Label)
    (source output : Tape Bool) (s : Bank) (rpos : Fin 2 → ℤ) (pos : Fin 6 → ℤ) :
    MicrocodeEmbedding.embed (appendBinding second).ports (Label.append (small:=small) (pad:=pad) second)
      (NativeMappedAppend.cfg pc source output rpos).denote (frame s pos)=
      cfg (.append second pc) (Function.update (Function.update s (fieldPort second) source) 5 output)
        ((appendBinding second).values rpos pos) := by
  unfold MicrocodeEmbedding.embed NativeMappedAppend.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus2 Microcode.focus cfg frame
  simp only [← (appendBinding second).values_eq_extend]
  congr 2
  funext p;cases second <;> fin_cases p <;> rfl

theorem append_positions (second : Bool) (pos : Fin 6 → ℤ) :
    (appendBinding second).values (fun p => pos ((appendBinding second).ports p)) pos=pos := by
  funext p;cases second <;> fin_cases p <;> rfl

theorem append_final_positions (second : Bool) (pos : Fin 6 → ℤ) (m : ℕ) :
    (appendBinding second).values (NativeMappedAppend.finalPositions (fun p => pos ((appendBinding second).ports p)) m) pos=advance pos 0 m := by
  funext p;cases second <;> fin_cases p <;> simp [appendBinding,fieldPort,FinitePortBinding.values,NativeMappedAppend.finalPositions,advance]

theorem append_call (small pad : ℕ) (second : Bool) (xs : List Bool) (pre : List (Sym Bool))
    (s : Bank) (hs : s (fieldPort second)=Counter.marked xs) (ho : s 5=⟨pre,[]⟩) (pos : Fin 6 → ℤ) :
    ∃ t ≤ 4*xs.length+5,Trace small pad t (cfg (.append second 0) s pos)
      (cfg (.append second 7) (Function.update s 5 ⟨(symbols xs).reverse++pre,[]⟩) (advance pos 0 xs.length)) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedAppend.append_trace id xs pre (fun p => pos ((appendBinding second).ports p))
  have he := MicrocodeEmbedding.trace_embed (appendBinding second).ports (Label.append (small:=small) (pad:=pad) second)
    (Microcode.MappedAppendFamily.program id) (program small pad) (frame s pos) (append_code small pad second) htr
  exact ⟨t,ht,by simpa only [embed_append,append_positions,append_final_positions,List.map_id,← hs,← ho,Function.update_eq_self] using he⟩

theorem embed_erase (small pad : ℕ) (second : Bool) (pc : NativeErase.Label) (word : Tape Bool) (s : Bank) (pos : Fin 6 → ℤ) :
    MicrocodeEmbedding.embed (eraseBinding second).ports (Label.erase (small:=small) (pad:=pad) second)
      (NativeErase.cfg pc word (fun _ => pos (fieldPort second))).denote (frame s pos)=
      cfg (.erase second pc) (Function.update s (fieldPort second) word) pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus cfg frame
  simp only [← (eraseBinding second).values_eq_extend]
  congr 2 <;> funext p <;> cases second <;> fin_cases p <;> rfl

theorem erase_call (small pad : ℕ) (second : Bool) (xs : List Bool) (s : Bank)
    (hs : s (fieldPort second)=Counter.marked xs) (pos : Fin 6 → ℤ) :
    ∃ t ≤ 4*xs.length+4,Trace small pad t (cfg (.erase second 2) s pos)
      (cfg (.erase second 0) (Function.update s (fieldPort second) ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace xs (fun _ => pos (fieldPort second))
  have he := MicrocodeEmbedding.trace_embed (eraseBinding second).ports (Label.erase (small:=small) (pad:=pad) second)
    NativeErase.program (program small pad) (frame s pos) (erase_code small pad second) htr
  exact ⟨t,ht,by simpa only [embed_erase,← hs,Function.update_eq_self] using he⟩

theorem update_first (source template input first second output word : Tape Bool) :
    Function.update (bank source template input first second output) (fieldPort false) word=bank source template input word second output := by
  funext p;fin_cases p <;> rfl
theorem update_second (source template input first second output word : Tape Bool) :
    Function.update (bank source template input first second output) (fieldPort true) word=bank source template input first word output := by
  funext p;fin_cases p <;> rfl
theorem update_output (source template input first second output word : Tape Bool) :
    Function.update (bank source template input first second output) 5 word=bank source template input first second word := by
  funext p;fin_cases p <;> rfl

theorem copy_stop_trace (small pad : ℕ) (xs : List Bool) (input : Tape Bool) (pre : List (Sym Bool)) (pos : Fin 6 → ℤ) :
    ∃ t ≤ 1,Trace small pad t
      (cfg (.read (.done false)) (bank (Counter.marked xs) ⟨[],[]⟩ input ⟨[],[]⟩ ⟨[],[]⟩ ⟨pre,[]⟩) pos)
      (cfg .done (bank (Counter.marked xs) ⟨[],[]⟩ input ⟨[],[]⟩ ⟨[],[]⟩ ⟨.stop::pre,[]⟩) (advance pos 0 1)) := by
  let z : NativeZipper.Config (Fin 6) (Label small pad) :=
    ⟨⟨.read (.done false),bank (Counter.marked xs) ⟨[],[]⟩ input ⟨[],[]⟩ ⟨[],[]⟩ ⟨pre,[]⟩⟩,pos⟩
  let z' : NativeZipper.Config (Fin 6) (Label small pad) :=
    ⟨⟨.done,bank (Counter.marked xs) ⟨[],[]⟩ input ⟨[],[]⟩ ⟨[],[]⟩ ⟨.stop::pre,[]⟩⟩,advance pos 0 1⟩
  have hr : NativeZipper.run (program small pad) 1 z=z' := by
    simp only [z,z',NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program]
    congr 2
    · funext p;fin_cases p <;> rfl
    · funext p;fin_cases p <;> simp [Microcode.single,advance,NativeMicrocode.direction,Transpose.Dir.shift]
  exact NativeZipper.trace_of_run (program small pad) hr

end TransposeFollowup.NormalizedBatch

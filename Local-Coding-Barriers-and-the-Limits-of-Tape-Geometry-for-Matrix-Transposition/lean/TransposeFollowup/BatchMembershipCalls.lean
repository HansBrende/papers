import TransposeFollowup.BatchMembershipMachine

namespace TransposeFollowup.BatchMembership
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def liftCompare (source template input : Tape Bool) (s : Fin 4 → Tape Bool) : Bank := bank source template input (s 2) (s 3) (s 0) (s 1)
theorem liftCompare_marked (source template input : Tape Bool) (a b : List Bool × List Bool) :
    liftCompare source template input (NativePairEqual.markedBank a b)=
      bank source template input (Counter.marked b.1) (Counter.marked b.2) (Counter.marked a.1) (Counter.marked a.2) := by
  funext p;fin_cases p <;> rfl

theorem embed_compare (small : ℕ) (found : Bool) (pc : NativePairEqual.Label) (s base : Fin 4 → Tape Bool)
    (source template input : Tape Bool) (rpos : Fin 4 → ℤ) (pos : Fin 7 → ℤ) :
    MicrocodeEmbedding.embed compareBinding.ports (Label.compare (small:=small) found) (NativePairEqual.cfg pc s rpos)
      (frame (liftCompare source template input base) pos)=cfg (.compare found pc) (liftCompare source template input s) (compareBinding.values rpos pos) := by
  unfold MicrocodeEmbedding.embed NativePairEqual.cfg cfg frame
  simp only [← compareBinding.values_eq_extend]
  congr 2
  funext p;fin_cases p <;> rfl
theorem compare_positions (pos : Fin 7 → ℤ) : compareBinding.values (fun p => pos (compareBinding.ports p)) pos=pos := by
  funext p;fin_cases p <;> rfl

theorem compare_call (small : ℕ) (found : Bool) (a b : List Bool × List Bool)
    (h1 : a.1.length=b.1.length) (h2 : a.2.length=b.2.length) (source template input : Tape Bool) (pos : Fin 7 → ℤ) :
    ∃ t ≤ 5*a.1.length+5*a.2.length+14,Trace small t
      (cfg (.compare found NativePairEqual.start) (bank source template input (Counter.marked b.1) (Counter.marked b.2) (Counter.marked a.1) (Counter.marked a.2)) pos)
      (cfg (.compare found (.done (NativePairEqual.samePair a b)))
        (bank source template input (Counter.marked b.1) (Counter.marked b.2) (Counter.marked a.1) (Counter.marked a.2)) pos) := by
  obtain ⟨t,ht,htr⟩:=NativePairEqual.pair_trace a b h1 h2 (fun p => pos (compareBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed compareBinding.ports (Label.compare (small:=small) found) NativePairEqual.program (program small)
    (frame (liftCompare source template input (NativePairEqual.markedBank a b)) pos) (compare_code small found) htr
  simp only [embed_compare,compare_positions] at he
  exact ⟨t,ht,by simpa only [liftCompare_marked] using he⟩

theorem embed_erase (small : ℕ) (found second : Bool) (pc : NativeErase.Label) (word : Tape Bool) (s : Bank) (pos : Fin 7 → ℤ) :
    MicrocodeEmbedding.embed (eraseBinding second).ports (Label.erase (small:=small) found second)
      (NativeErase.cfg pc word (fun _ => pos (fieldPort second))).denote (frame s pos)=
      cfg (.erase found second pc) (Function.update s (fieldPort second) word) pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus cfg frame
  simp only [← (eraseBinding second).values_eq_extend]
  congr 2 <;> funext p <;> cases second <;> fin_cases p <;> rfl
theorem erase_call (small : ℕ) (found second : Bool) (xs : List Bool) (s : Bank)
    (hs : s (fieldPort second)=Counter.marked xs) (pos : Fin 7 → ℤ) :
    ∃ t ≤ 4*xs.length+4,Trace small t (cfg (.erase found second 2) s pos)
      (cfg (.erase found second 0) (Function.update s (fieldPort second) ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeErase.erase_trace xs (fun _ => pos (fieldPort second))
  have he:=MicrocodeEmbedding.trace_embed (eraseBinding second).ports (Label.erase (small:=small) found second) NativeErase.program (program small)
    (frame s pos) (erase_code small found second) htr
  exact ⟨t,ht,by simpa only [embed_erase,← hs,Function.update_eq_self] using he⟩

theorem update_first (source template input first second a b word : Tape Bool) :
    Function.update (bank source template input first second a b) (fieldPort false) word=bank source template input word second a b := by
  funext p;fin_cases p <;> rfl
theorem update_second (source template input first second a b word : Tape Bool) :
    Function.update (bank source template input first second a b) (fieldPort true) word=bank source template input first word a b := by
  funext p;fin_cases p <;> rfl

theorem jump_trace (small : ℕ) (pc next : Label small) (s : Bank) (pos : Fin 7 → ℤ)
    (h : program small pc=.jump next) : Trace small 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

end TransposeFollowup.BatchMembership

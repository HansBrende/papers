import BitWord.NativeRulers

namespace BitWord.NativeRulers
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeExpanderShearFrames NativeCountedLoop

def unaryWord (s : Bool) (xs hs : List Bool) := if s then hs else xs
def powerWord (s : Bool) (hs ws : List Bool) := if s then ws else hs
def unaryBefore (s : Bool) := if s then 1 else 0
def powerBefore (s : Bool) := if s then 4 else 2
def productCount (s : Bool) (xs hs : List Bool) := if s then 2^Counter.value hs else Counter.value xs

theorem unary_call (s : Bool) (xs hs ws : List Bool) (pos : Port → ℤ) :
    ∃ t≤13*Counter.value (unaryWord s xs hs)+14*(unaryWord s xs hs).length+40,Trace t
      (cfg (.unary s NativeUnary.start) (stage xs hs ws (unaryBefore s)) pos)
      (cfg (.unary s .done) (stage xs hs ws (unaryBefore s+1)) pos) := by
  let word := unaryWord s xs hs
  let base := stage xs hs ws (unaryBefore s)
  have hi : (fun p => base ((unaryBinding s).ports p))=![Counter.marked word,⟨[],[]⟩,⟨[],[]⟩] := by
    cases s <;> funext p <;> fin_cases p <;> rfl
  have hf : (unaryBinding s).values
      ![Counter.marked word,⟨[],[]⟩,Counter.marked (List.replicate (Counter.value word) false)] base=
      stage xs hs ws (unaryBefore s+1) := by
    cases s <;> funext p <;> cases p <;> rfl
  obtain ⟨t,ht,htr⟩ := NativeUnary.complete_trace word (fun p => pos ((unaryBinding s).ports p))
  have he := NativeBindingCalls.restoring_call (unaryBinding s) (Label.unary s) NativeUnary.program program
    (unary_code s) NativeUnary.start .done base pos _ t (by simpa only [hi] using htr)
  exact ⟨t,ht,by simpa only [hf] using he⟩

theorem power_call (s : Bool) (xs hs ws : List Bool) (pos : Port → ℤ) :
    ∃ t≤NativePowerTwo.budget (powerWord s hs ws),Trace t
      (cfg (.power s NativePowerTwo.start) (stage xs hs ws (powerBefore s)) pos)
      (cfg (.power s .done) (stage xs hs ws (powerBefore s+1)) pos) := by
  let word := powerWord s hs ws
  let base := stage xs hs ws (powerBefore s)
  have hi : (fun p => base ((powerBinding s).ports p))=NativePowerTwo.initial word := by
    cases s <;> funext p <;> cases p <;> rfl
  have hf : (powerBinding s).values (NativePowerTwo.final word) base=stage xs hs ws (powerBefore s+1) := by
    cases s <;> funext p <;> cases p <;> rfl
  obtain ⟨t,ht,htr⟩ := NativePowerTwo.complete_trace word (fun p => pos ((powerBinding s).ports p))
  have he := NativeBindingCalls.restoring_call (powerBinding s) (Label.power s) NativePowerTwo.program program
    (power_code s) NativePowerTwo.start .done base pos (NativePowerTwo.final word) t
      (by rw [hi]; exact htr)
  exact ⟨t,ht,by simpa only [hf] using he⟩

theorem mapped_cfg (pc : NativeMappedCopy.Label) (a b : Tape Bool) (p : Fin 2 → ℤ) :
    NativeMappedCopy.cfg pc a b p=workCfg pc ![a,b] p := by
  unfold NativeMappedCopy.cfg workCfg
  congr 2; funext i; fin_cases i <;> rfl

theorem map_call (s : Bool) (xs hs ws : List Bool) (pos : Port → ℤ) :
    ∃ t≤6*2^Counter.value (powerWord s hs ws)+14,Trace t
      (cfg (.map s (.init (.erase 0))) (stage xs hs ws (powerBefore s+1)) pos)
      (cfg (.map s (.seal .done)) (stage xs hs ws (powerBefore s+2)) pos) := by
  let word := NativePowerTwo.ruler (powerWord s hs ws)
  let base := stage xs hs ws (powerBefore s+1)
  have hi : (fun p => base ((mapBinding s).ports p))=![Counter.marked word,⟨[],[]⟩] := by
    cases s <;> funext p <;> fin_cases p <;> rfl
  have hf : (mapBinding s).values ![Counter.marked word,Counter.marked (word.map (fun _ => false))] base=
      stage xs hs ws (powerBefore s+2) := by
    cases s <;> funext p <;> cases p <;>
      simp [mapBinding,NativeBankCalls.pairBinding,FinitePortBinding.values,base,word,powerWord,powerBefore,
        stage,birth,contents,powerTarget,rulerTarget,NativePowerTwo.ruler,List.map_replicate]
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace (fun _ => false) word (fun p => pos ((mapBinding s).ports p))
  rw [mapped_cfg,mapped_cfg] at htr
  have he := NativeBindingCalls.restoring_call (mapBinding s) (Label.map s)
    (NativeMappedCopy.program (fun _ => false)) program (map_code s) (.init (.erase 0)) (.seal .done)
    base pos _ t (by simpa only [hi] using htr)
  refine ⟨t,?_,by simpa only [hf] using he⟩
  simpa [word,NativePowerTwo.ruler] using ht

theorem product_call (s : Bool) (xs hs ws : List Bool) (pos : Port → ℤ) :
    ∃ t≤6*productCount s xs hs*2^Counter.value ws+9*productCount s xs hs+16,Trace t
      (cfg (.product s NativeExpanderShearTagPage.start) (stage xs hs ws (if s then 7 else 6)) pos)
      (cfg (.product s .done) (stage xs hs ws (if s then 8 else 7)) pos) := by
  let flags := List.replicate (productCount s xs hs) false
  let clock := List.replicate (2^Counter.value ws) false
  let base := stage xs hs ws (if s then 7 else 6)
  let out := NativeMatchingXorTagStream.expanded clock.length flags
  have hout : out=List.replicate (productCount s xs hs*2^Counter.value ws) false := by
    simp [out,clock,flags,NativeMatchingXorTagStream.expanded,List.flatMap_replicate]
  have hi : (fun p => base ((productBinding s).ports p))=![Counter.marked flags,Counter.marked clock,⟨[],[]⟩] := by
    cases s <;> funext p <;> fin_cases p <;> rfl
  have hf : (productBinding s).values ![Counter.marked flags,Counter.marked clock,Counter.marked out] base=
      stage xs hs ws (if s then 8 else 7) := by
    rw [hout]
    cases s <;> funext p <;> cases p <;> rfl
  obtain ⟨t,ht,htr⟩ := NativeExpanderShearTagPage.complete_trace flags clock
    (fun p => pos ((productBinding s).ports p))
  have he := NativeBindingCalls.restoring_call (productBinding s) (Label.product s)
    NativeExpanderShearTagPage.program program (product_code s) NativeExpanderShearTagPage.start .done
    base pos ![Counter.marked flags,Counter.marked clock,Counter.marked out] t
      (by rw [hi]; exact htr)
  exact ⟨t,by simpa only [flags,clock,List.length_replicate] using ht,by simpa only [hf] using he⟩

end BitWord.NativeRulers

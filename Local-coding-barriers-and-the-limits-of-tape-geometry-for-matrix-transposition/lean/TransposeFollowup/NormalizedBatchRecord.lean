import TransposeFollowup.NormalizedBatchCalls

namespace TransposeFollowup.NormalizedBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def recordBits (pad : ℕ) (p : List Bool × List Bool) : List Bool :=
  NativePaddedField.padded pad p.1++NativePaddedField.padded pad p.2
def recordBudget (small pad : ℕ) (xs : List Bool) := 80*xs.length+37*small+22*pad+84

theorem record_trace (small pad : ℕ) (xs first second : List Bool) (hp : 0<2*xs.length+small)
    (hf : first.length=2*xs.length+small) (hs : second.length=2*xs.length+small)
    (pre suffix out : List (Sym Bool)) (pos : Fin 6 → ℤ) :
    ∃ t ≤ recordBudget small pad xs,Trace small pad t
      (cfg (start small pad) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,symbols (first++second)++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨out,[]⟩) pos)
      (cfg (start small pad) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨(symbols (first++second)).reverse++pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩
        ⟨(symbols (recordBits pad (first,second))).reverse++out,[]⟩)
        (advance pos (2*(2*xs.length+small)) (2*(2*xs.length+small+pad)))) := by
  let A:=NativePaddedField.padded pad first
  let B:=NativePaddedField.padded pad second
  let source:=Counter.marked xs
  let input : Tape Bool := ⟨(symbols (first++second)).reverse++pre,suffix⟩
  let outA := (symbols A).reverse++out
  let outB := (symbols B).reverse++outA
  let p1 := advance pos (2*(2*xs.length+small)) 0
  let p2 := advance p1 0 A.length
  let p3 := advance p2 0 B.length
  have hA : A.length=2*xs.length+small+pad := by simp [A,NativePaddedField.padded_length,hf]
  have hB : B.length=2*xs.length+small+pad := by simp [B,NativePaddedField.padded_length,hs]
  obtain ⟨a,ha,ta⟩ := read_pair_call small pad xs first second hp hf hs pre suffix ⟨out,[]⟩ pos
  have j1 := jump_trace small pad (.read (.done true)) (.append false 0)
    (bank source ⟨[],[]⟩ input (Counter.marked A) (Counter.marked B) ⟨out,[]⟩) p1 rfl
  obtain ⟨b,hb,tb⟩ := append_call small pad false A out
    (bank source ⟨[],[]⟩ input (Counter.marked A) (Counter.marked B) ⟨out,[]⟩) rfl rfl p1
  rw [update_output] at tb
  have j2 := jump_trace small pad (.append false 7) (.append true 0)
    (bank source ⟨[],[]⟩ input (Counter.marked A) (Counter.marked B) ⟨outA,[]⟩) p2 rfl
  obtain ⟨c,hc,tc⟩ := append_call small pad true B outA
    (bank source ⟨[],[]⟩ input (Counter.marked A) (Counter.marked B) ⟨outA,[]⟩) rfl rfl p2
  rw [update_output] at tc
  have j3 := jump_trace small pad (.append true 7) (.erase false 2)
    (bank source ⟨[],[]⟩ input (Counter.marked A) (Counter.marked B) ⟨outB,[]⟩) p3 rfl
  obtain ⟨d,hd,td⟩ := erase_call small pad false A
    (bank source ⟨[],[]⟩ input (Counter.marked A) (Counter.marked B) ⟨outB,[]⟩) rfl p3
  rw [update_first] at td
  have j4 := jump_trace small pad (.erase false 0) (.erase true 2)
    (bank source ⟨[],[]⟩ input ⟨[],[]⟩ (Counter.marked B) ⟨outB,[]⟩) p3 rfl
  obtain ⟨e,he,te⟩ := erase_call small pad true B
    (bank source ⟨[],[]⟩ input ⟨[],[]⟩ (Counter.marked B) ⟨outB,[]⟩) rfl p3
  rw [update_second] at te
  have j5 := jump_trace small pad (.erase true 0) (start small pad)
    (bank source ⟨[],[]⟩ input ⟨[],[]⟩ ⟨[],[]⟩ ⟨outB,[]⟩) p3 rfl
  have ht := NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans
    (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans
    (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta j1) tb) j2) tc) j3) td) j4) te) j5
  refine ⟨a+1+b+1+c+1+d+1+e+1,?_,?_⟩
  · dsimp only [PreparedPair.pairBudget] at ha
    dsimp only [recordBudget]
    omega
  · simpa only [p3,p2,p1,advance_add,Nat.zero_add,Nat.add_zero,hA,hB,← two_mul,Nat.mul_zero,
      source,input,outB,outA,A,B,recordBits,symbols,List.map_append,List.reverse_append,List.append_assoc] using ht

theorem stop_trace (small pad : ℕ) (xs : List Bool) (pre suffix out : List (Sym Bool)) (pos : Fin 6 → ℤ) :
    ∃ t ≤ PreparedPair.stopBudget small xs+1,Trace small pad t
      (cfg (start small pad) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,.stop::suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨out,[]⟩) pos)
      (cfg .done (bank (Counter.marked xs) ⟨[],[]⟩ ⟨.stop::pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨.stop::out,[]⟩) (advance pos 1 1)) := by
  obtain ⟨a,ha,ta⟩ := read_stop_call small pad xs pre suffix ⟨out,[]⟩ pos
  obtain ⟨b,hb,tb⟩ := copy_stop_trace small pad xs ⟨.stop::pre,suffix⟩ out (advance pos 1 0)
  refine ⟨a+b,by omega,?_⟩
  simpa only [advance_add,Nat.zero_add,Nat.add_zero] using NativeCountedLoop.trace_trans ta tb

end TransposeFollowup.NormalizedBatch

import TransposeFollowup.BatchMembershipCalls

namespace TransposeFollowup.BatchMembership
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def queryBank (xs : List Bool) (a : List Bool × List Bool) (input : Tape Bool) : Bank :=
  bank (Counter.marked xs) ⟨[],[]⟩ input ⟨[],[]⟩ ⟨[],[]⟩ (Counter.marked a.1) (Counter.marked a.2)
def recordBudget (small : ℕ) (xs : List Bool) := 84*xs.length+39*small+87

theorem record_trace (small : ℕ) (found : Bool) (xs : List Bool) (a : List Bool × List Bool)
    (ha1 : a.1.length=2*xs.length+small) (ha2 : a.2.length=2*xs.length+small)
    (first second : List Bool) (hp : 0<2*xs.length+small)
    (hf : first.length=2*xs.length+small) (hs : second.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ recordBudget small xs,Trace small t
      (cfg (start small found) (queryBank xs a ⟨pre,symbols (first++second)++suffix⟩) pos)
      (cfg (start small (found || NativePairEqual.samePair a (first,second)))
        (queryBank xs a ⟨(symbols (first++second)).reverse++pre,suffix⟩) (advance pos (2*(2*xs.length+small)))) := by
  let source:=Counter.marked xs
  let input : Tape Bool := ⟨(symbols (first++second)).reverse++pre,suffix⟩
  let A:=Counter.marked a.1
  let B:=Counter.marked a.2
  let adv:=advance pos (2*(2*xs.length+small))
  let found':=found || NativePairEqual.samePair a (first,second)
  obtain ⟨x,hx,tx⟩:=read_pair_call small found xs first second hp hf hs pre suffix A B pos
  have j1:=jump_trace small (.read found (.done true)) (.compare found NativePairEqual.start)
    (bank source ⟨[],[]⟩ input (Counter.marked first) (Counter.marked second) A B) adv rfl
  obtain ⟨y,hy,ty⟩:=compare_call small found a (first,second) (by simp only;omega) (by simp only;omega) source ⟨[],[]⟩ input adv
  have j2:=jump_trace small (.compare found (.done (NativePairEqual.samePair a (first,second)))) (.erase found' false 2)
    (bank source ⟨[],[]⟩ input (Counter.marked first) (Counter.marked second) A B) adv rfl
  obtain ⟨z,hz,tz⟩:=erase_call small found' false first
    (bank source ⟨[],[]⟩ input (Counter.marked first) (Counter.marked second) A B) rfl adv
  rw [update_first] at tz
  have j3:=jump_trace small (.erase found' false 0) (.erase found' true 2)
    (bank source ⟨[],[]⟩ input ⟨[],[]⟩ (Counter.marked second) A B) adv rfl
  obtain ⟨v,hv,tv⟩:=erase_call small found' true second
    (bank source ⟨[],[]⟩ input ⟨[],[]⟩ (Counter.marked second) A B) rfl adv
  rw [update_second] at tv
  have j4:=jump_trace small (.erase found' true 0) (start small found') (queryBank xs a input) adv rfl
  refine ⟨x+1+y+1+z+1+v+1,?_,?_⟩
  · dsimp only [PreparedPair.pairBudget] at hx
    dsimp only [recordBudget]
    omega
  · exact NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans
      (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tx j1) ty) j2) tz) j3) tv) j4

theorem stop_trace (small : ℕ) (found : Bool) (xs : List Bool) (a : List Bool × List Bool)
    (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ PreparedPair.stopBudget small xs+1,Trace small t
      (cfg (start small found) (queryBank xs a ⟨pre,.stop::suffix⟩) pos)
      (cfg (.done found) (queryBank xs a ⟨.stop::pre,suffix⟩) (advance pos 1)) := by
  obtain ⟨t,ht,htr⟩:=read_stop_call small found xs pre suffix (Counter.marked a.1) (Counter.marked a.2) pos
  have tj:=jump_trace small (.read found (.done false)) (.done found) (queryBank xs a ⟨.stop::pre,suffix⟩) (advance pos 1) rfl
  exact ⟨t+1,by omega,NativeCountedLoop.trace_trans htr tj⟩

end TransposeFollowup.BatchMembership

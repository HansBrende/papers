import BitWord.NativeGateCalls
import BitWord.NativeSmallDescriptors

namespace BitWord.NativeGate
open FixedTapeCompiler TransposeFollowup CopyMachine
open NativeExpanderShearFrames NativeBankCalls NativeCountedLoop
set_option autoImplicit false
noncomputable section

def Legal (N : ℕ) : Option Gate → Prop | none => True | some g => g.Legal N
def moved {N : ℕ} (g : Option Gate) (hg : Legal N g) (b : Address N → Bool) : Address N → Bool :=
  match g with | none => b | some g => moveBank (Gate.equiv N g hg) b
def budget (M : Transpose.TM) (C N : ℕ) (xs : List Bool) :=
  (NativeOracleBatch.suffixConstant M C+300)*2^N+24*xs.length+100

theorem suffix_budget (M : Transpose.TM) (C N k : ℕ) (xs : List Bool)
    (hx : Counter.value xs=k) (hk : 2*k≤N) :
    NativeSuffixPowered.budget M C N k xs+6 ≤ budget M C N xs := by
  have hp : 4^k≤2^N := by
    rw [show 4=2^2 by norm_num,←pow_mul]
    exact Nat.pow_le_pow_right (by decide) hk
  have hn : N < 2^N := Nat.lt_two_pow_self
  have he : 1≤2^N := Nat.succ_le_of_lt (by positivity)
  simp only [NativeSuffixPowered.budget,NativePowerTwo.budget,NativeDoubleWord.value_double,hx,
    List.length_cons,budget]
  have hp' : 2^(2*k)=4^k := by rw [show 4=2^2 by norm_num,pow_mul]
  rw [hp']
  nlinarith

theorem complete_trace (M : Transpose.TM) (C : ℕ) (hM : DyadicBitOracle M C)
    {N : ℕ} (hN : 0<N) (g : Option Gate) (hg : Legal N g) (b : Address N → Bool)
    (xs fs : List Bool) (hx : Counter.value xs=NativeSmallDescriptors.parameterValue g)
    (hfs : fs.length=2^(N-1)) (sp tp kp pp : ℤ) (extra : Fin 4 → ℤ) :
    ∃ t≤budget M C N xs,Trace M t
      (cfg M (start M) (bank M (flattenBank b) xs (NativeSmallDescriptors.opcodeWord g) fs)
        (positions M sp tp kp pp extra))
      (cfg M .done (bank M (flattenBank (moved g hg b)) xs (NativeSmallDescriptors.opcodeWord g) fs)
        (positions M sp tp kp pp extra)) := by
  let pos := positions M sp tp kp pp extra
  have he : 1≤2^N := Nat.succ_le_of_lt (by positivity)
  cases g with
  | none =>
    obtain ⟨t,ht,htr⟩ := read_call M (flattenBank b) xs fs false false pos
    exact ⟨t,by dsimp [budget]; nlinarith,by simpa only [NativeSmallDescriptors.opcodeWord,selected,moved] using htr⟩
  | some g =>
    cases g with
    | suffix k =>
      obtain ⟨t0,h0,tr0⟩ := read_call M (flattenBank b) xs fs true true pos
      obtain ⟨t1,h1,tr1⟩ := suffix_call M C hM hg b xs [true,true] fs hx sp tp kp pp extra
      have j1 := jump M (.suffix .done) .done
        (bank M (flattenBank (moveBank (Gate.equiv N (.suffix k) hg) b)) xs [true,true] fs) pos rfl
      have htr := trace_trans (trace_trans tr0 tr1) j1
      refine ⟨_,?_,htr⟩
      have hb := suffix_budget M C N k xs hx hg
      omega
    | right =>
      obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
      simp only [Nat.succ_eq_add_one] at *
      obtain ⟨t0,h0,tr0⟩ := read_call M (flattenBank b) xs fs true false pos
      obtain ⟨t1,h1,tr1⟩ := split_call M (flattenBank b) xs [true,false] fs pos
      have ho : NativeSplit.output (flattenBank b)=flattenBank (moveBank (Gate.equiv (n+1) .right hg) b) := by
        simpa only [NativeSplit.output,NativeSplit.evenBits,NativeSplit.oddBits] using (flattenBank_right b).symm
      rw [ho] at tr1
      have j1 := jump M (.split .done) .done
        (bank M (flattenBank (moveBank (Gate.equiv (n+1) .right hg) b)) xs [true,false] fs) pos rfl
      have htr := trace_trans (trace_trans tr0 tr1) j1
      refine ⟨_,?_,htr⟩
      simp only [flattenBank_length,Nat.succ_eq_add_one] at h1
      dsimp [budget]
      nlinarith
    | left =>
      obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
      simp only [Nat.succ_eq_add_one] at *
      let a := flattenBank (fun x : Address n => b (Fin.cons false x))
      let c := flattenBank (fun x : Address n => b (Fin.cons true x))
      have ha : a.length=2^n := flattenBank_length _
      have hc : c.length=2^n := flattenBank_length _
      have hraw : flattenBank b=a++c := flattenBank_cons b
      have hout : NativeInterleave.output a c=flattenBank (moveBank (Gate.equiv (n+1) .left hg) b) := by
        exact (flattenBank_left b).symm
      obtain ⟨t0,h0,tr0⟩ := read_call M (flattenBank b) xs fs false true pos
      obtain ⟨t1,h1,tr1⟩ := merge_call M a c fs xs [false,true] (ha.trans hc.symm)
        (by simpa only [Nat.add_sub_cancel,ha] using hfs) pos
      rw [←hraw,hout] at tr1
      have j1 := jump M (.merge .done) .done
        (bank M (flattenBank (moveBank (Gate.equiv (n+1) .left hg) b)) xs [false,true] fs) pos rfl
      have htr := trace_trans (trace_trans tr0 tr1) j1
      refine ⟨_,?_,htr⟩
      rw [ha] at h1
      dsimp [budget]
      rw [pow_succ]
      nlinarith

end
end BitWord.NativeGate

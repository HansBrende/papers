import BitWord.NativeOracleBatchRun
import BitWord.AddressSuffix

/-! The sole oracle premise is an actual uniform raw machine for dyadic bit
squares. No linearity, obliviousness, schedule or reset premise is required. -/
namespace BitWord
open FixedTapeCompiler CopyMachine TransposeFollowup
set_option autoImplicit false

 def DyadicBitOracle (M : Transpose.TM) (C : ℕ) : Prop :=
   ∀ (k : ℕ) (A : Transpose.Matrix),
     Transpose.ComputesWithin M (Transpose.encode (2^k) 1 A)
       (Transpose.encode (2^k) 1 (Transpose.transpose A)) (C*(4^k))

 theorem DyadicBitOracle.on_list {M : Transpose.TM} {C : ℕ}
     (hM : DyadicBitOracle M C) (k : ℕ) (xs : List Bool) (hxs : xs.length=4^k) :
     Transpose.ComputesWithin M xs (bitTranspose k xs) (C*(4^k)) := by
   obtain ⟨A,hA,hB⟩ := bitTranspose_spec k xs hxs
   simpa only [hA,hB] using hM k A

 theorem bitTranspose_length (k : ℕ) (xs : List Bool) : (bitTranspose k xs).length=4^k := by
   unfold bitTranspose
   rw [flattenBank_length]
   simp only [Nat.add_zero]
   rw [show 4=2^2 by norm_num, ← pow_mul]

namespace NativeOracleBatch
noncomputable section

def suffixConstant (M : Transpose.TM) (C : ℕ) : ℕ :=
  NativeOracleReset.overhead M*(C+1)+86

/-- A genuine suffix-address transpose realized by batched calls to the one
fixed raw bit machine. This intermediate contract receives its unary ruler;
the native ruler generator supplies it in the complete reduction. -/
theorem suffix_trace (M : Transpose.TM) (C : ℕ) (hM : DyadicBitOracle M C)
    {N k : ℕ} (hk : 2*k≤N) (bank : Address N → Bool) (sp tp kp : ℤ) :
    ∃ t≤ suffixConstant M C*(2^N), Trace M t
      (cfg M (start M) (blockBank M (Counter.marked (flattenBank bank)) ⟨[],[]⟩
        (List.replicate (4^k) true)) (blockPos M sp tp kp))
      (cfg M .done (blockBank M (Counter.marked (flattenBank bank))
        (Counter.marked (flattenBank (moveBank (Gate.equiv N (.suffix k) hk) bank)))
        (List.replicate (4^k) true)) (blockPos M sp tp kp)) := by
  obtain ⟨blocks,hinput,hlen,houtput⟩ := suffix_block_decomposition hk bank
  let fs := List.replicate (4^k) true
  have hfs : fs.length=4^k := List.length_replicate
  have hb : ∀ xs∈blocks,xs.length=fs.length ∧ (bitTranspose k xs).length=fs.length ∧
      Transpose.ComputesWithin M xs (bitTranspose k xs) (C*(4^k)) := by
    intro xs hx
    exact ⟨(hlen xs hx).trans hfs.symm,(bitTranspose_length k xs).trans hfs.symm,
      hM.on_list k xs (hlen xs hx)⟩
  obtain ⟨t,ht,htr⟩ := complete_trace M (bitTranspose k) fs (by rw [hfs]; positivity)
    (C*(4^k)) blocks hb sp tp kp
  have hv : blocks.length*(4^k)=2^N := by
    have hl := flattened_length fs blocks (by intro xs hx; exact (hb xs hx).1)
    rw [hfs,hinput,flattenBank_length] at hl
    exact hl.symm
  have hlin := batchBudget_linear M C blocks.length (4^k) (C*(4^k)) (Nat.succ_le_of_lt (by positivity)) (le_refl _)
  have hn : 1≤2^N := Nat.succ_le_of_lt (by positivity)
  refine ⟨t,?_,?_⟩
  · rw [hfs] at ht
    have hh := ht.trans hlin
    rw [hv] at hh
    dsimp [suffixConstant]
    nlinarith
  · simpa only [hinput,← List.flatMap_def,← houtput] using htr

end
end NativeOracleBatch
end BitWord

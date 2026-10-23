import BitWord.NativeOracleBatch

namespace BitWord.NativeOracleBatch
open FixedTapeCompiler TransposeFollowup CopyMachine
open NativeExpanderShearFrames NativeCountedLoop
set_option autoImplicit false
noncomputable section

/-- Loop correctness is derived from the actual EOF test and block caller.
The function and time bound below specify the original oracle, not the loop. -/
theorem loop_trace (M : Transpose.TM) (f : List Bool → List Bool) (fs : List Bool)
    (hfs : 0<fs.length) (T : ℕ) (blocks : List (List Bool))
    (hb : ∀ xs∈blocks,xs.length=fs.length ∧ (f xs).length=fs.length ∧
      Transpose.ComputesWithin M xs (f xs) T)
    (sl : List (Sym Bool)) (acc : List Bool) (sp tp kp : ℤ) :
    ∃ t≤blocks.length*(NativeOracleBlock.blockBudget M fs.length fs.length T+2)+1,
      Trace M t
        (cfg M .check (blockBank M ⟨sl,symbols blocks.flatten++[.stop]⟩
          (NativeSealBack.openWord acc) fs) (blockPos M sp tp kp))
        (cfg M (.seal .seal) (blockBank M ⟨(symbols blocks.flatten).reverse++sl,[.stop]⟩
          (NativeSealBack.openWord (acc++(blocks.map f).flatten)) fs)
          (blockPos M (sp+blocks.flatten.length) (tp+(blocks.map f).flatten.length) kp)) := by
  induction blocks generalizing sl acc sp tp with
  | nil =>
    refine ⟨1,by simp,?_⟩
    have hh := check_call M (blockBank M ⟨sl,[.stop]⟩ (NativeSealBack.openWord acc) fs)
      (blockPos M sp tp kp) sl [] rfl
    simpa [symbols] using hh
  | cons xs blocks ih =>
    obtain ⟨hx,hfx,hcomp⟩ := hb xs (by simp)
    have hrest : ∀ ys∈blocks,ys.length=fs.length ∧ (f ys).length=fs.length ∧
        Transpose.ComputesWithin M ys (f ys) T := by
      intro ys hy; exact hb ys (by simp [hy])
    have hne : xs++blocks.flatten≠[] := by
      intro he
      have hz : xs=[] := (List.append_eq_nil_iff.mp he).1
      have hp : 0<xs.length := by omega
      simpa [hz] using hp
    have rd := check_call M
      (blockBank M ⟨sl,symbols (xs++blocks.flatten)++[.stop]⟩ (NativeSealBack.openWord acc) fs)
      (blockPos M sp tp kp) sl (xs++blocks.flatten) rfl
    rw [if_neg hne] at rd
    obtain ⟨t0,h0,tr0⟩ := block_call M xs (f xs) fs acc sl
      (symbols blocks.flatten++[.stop]) sp tp kp T hx.symm hcomp
    have j0 := jump M (.call .done) .check
      (blockBank M ⟨(symbols xs).reverse++sl,symbols blocks.flatten++[.stop]⟩
        (NativeSealBack.openWord (acc++f xs)) fs)
      (blockPos M (sp+xs.length) (tp+(f xs).length) kp) rfl
    obtain ⟨t1,h1,tr1⟩ := ih hrest ((symbols xs).reverse++sl) (acc++f xs)
      (sp+xs.length) (tp+(f xs).length)
    have rd' : Trace M 1
        (cfg M .check (blockBank M ⟨sl,symbols (xs::blocks).flatten++[.stop]⟩
          (NativeSealBack.openWord acc) fs) (blockPos M sp tp kp))
        (cfg M (.call (NativeOracleBlock.start M))
          (blockBank M ⟨sl,symbols xs++(symbols blocks.flatten++[.stop])⟩
            (NativeSealBack.openWord acc) fs) (blockPos M sp tp kp)) := by
      simpa [symbols,List.map_append,List.append_assoc] using rd
    have a0 := trace_trans rd' tr0
    have a1 := trace_trans a0 j0
    have a2 := trace_trans a1 tr1
    refine ⟨1+t0+1+t1,?_,?_⟩
    · simp only [List.length_cons] at *
      rw [hx,hfx] at h0
      nlinarith
    · simpa [symbols,List.map_append,List.reverse_append,List.append_assoc,
        Nat.cast_add,add_assoc] using a2

 theorem flattened_length (fs : List Bool) (blocks : List (List Bool))
    (hb : ∀ xs∈blocks,xs.length=fs.length) : blocks.flatten.length=blocks.length*fs.length := by
  induction blocks with
  | nil => simp
  | cons xs blocks ih =>
    have hx := hb xs (by simp)
    have ht : ∀ ys∈blocks,ys.length=fs.length := by intro ys hy; exact hb ys (by simp [hy])
    simp [hx,ih ht,Nat.add_mul,Nat.add_comm]

end
end BitWord.NativeOracleBatch

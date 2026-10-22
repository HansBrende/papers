import TransposeFollowup.NormalizedBatchRecord

namespace TransposeFollowup.NormalizedBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def inputBits (rs : List (List Bool × List Bool)) := rs.flatMap (fun p => p.1++p.2)
def outputBits (pad : ℕ) (rs : List (List Bool × List Bool)) := rs.flatMap (recordBits pad)
def inputBatch (rs : List (List Bool × List Bool)) : List (Sym Bool) := symbols (inputBits rs)++[.stop]
def outputBatch (pad : ℕ) (rs : List (List Bool × List Bool)) : List (Sym Bool) := symbols (outputBits pad rs)++[.stop]
def batchBudget (small pad : ℕ) (xs : List Bool) (rs : List (List Bool × List Bool)) :=
  rs.length*recordBudget small pad xs+PreparedPair.stopBudget small xs+1

theorem records_trace (small pad : ℕ) (xs : List Bool) (hp : 0<2*xs.length+small)
    (rs : List (List Bool × List Bool))
    (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (pre suffix out : List (Sym Bool)) (pos : Fin 6 → ℤ) :
    ∃ t ≤ rs.length*recordBudget small pad xs,Trace small pad t
      (cfg (start small pad) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,symbols (inputBits rs)++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨out,[]⟩) pos)
      (cfg (start small pad) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨(symbols (inputBits rs)).reverse++pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩
        ⟨(symbols (outputBits pad rs)).reverse++out,[]⟩) (advance pos (inputBits rs).length (outputBits pad rs).length)) := by
  induction rs generalizing pre out pos with
  | nil =>
    refine ⟨0,by simp,?_⟩
    simp only [inputBits,outputBits,List.flatMap_nil,symbols,List.map_nil,List.nil_append,List.reverse_nil,List.length_nil,advance_zero]
    exact .refl _
  | cons p rs ih =>
    have hpw := hw p (by simp)
    have hrw : ∀ q ∈ rs,q.1.length=2*xs.length+small ∧ q.2.length=2*xs.length+small := by
      intro q hq;exact hw q (by simp [hq])
    have hiLen : (p.1++p.2).length=2*(2*xs.length+small) := by simp [hpw.1,hpw.2,two_mul]
    have hoLen : (recordBits pad p).length=2*(2*xs.length+small+pad) := by
      simp [recordBits,NativePaddedField.padded_length,hpw.1,hpw.2,two_mul]
    obtain ⟨a,ha,ta⟩ := record_trace small pad xs p.1 p.2 hp hpw.1 hpw.2 pre (symbols (inputBits rs)++suffix) out pos
    rw [← hiLen,← hoLen] at ta
    obtain ⟨b,hb,tb⟩ := ih hrw ((symbols (p.1++p.2)).reverse++pre) ((symbols (recordBits pad p)).reverse++out)
      (advance pos (p.1++p.2).length (recordBits pad p).length)
    refine ⟨a+b,?_,?_⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · simpa only [inputBits,outputBits,List.flatMap_cons,symbols,List.map_append,List.reverse_append,List.append_assoc,List.length_append,advance_add,Nat.add_assoc]
        using NativeCountedLoop.trace_trans ta tb

theorem batch_trace (small pad : ℕ) (xs : List Bool) (hp : 0<2*xs.length+small)
    (rs : List (List Bool × List Bool))
    (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (pre suffix out : List (Sym Bool)) (pos : Fin 6 → ℤ) :
    ∃ t ≤ batchBudget small pad xs rs,Trace small pad t
      (cfg (start small pad) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,inputBatch rs++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨out,[]⟩) pos)
      (cfg .done (bank (Counter.marked xs) ⟨[],[]⟩ ⟨(inputBatch rs).reverse++pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩
        ⟨(outputBatch pad rs).reverse++out,[]⟩) (advance pos (inputBatch rs).length (outputBatch pad rs).length)) := by
  obtain ⟨a,ha,ta⟩ := records_trace small pad xs hp rs hw pre (.stop::suffix) out pos
  obtain ⟨b,hb,tb⟩ := stop_trace small pad xs ((symbols (inputBits rs)).reverse++pre) suffix
    ((symbols (outputBits pad rs)).reverse++out) (advance pos (inputBits rs).length (outputBits pad rs).length)
  refine ⟨a+b,by unfold batchBudget;omega,?_⟩
  simpa only [inputBatch,outputBatch,List.append_assoc,List.cons_append,List.nil_append,List.reverse_append,List.reverse_cons,List.reverse_nil,
    List.length_append,List.length_cons,List.length_nil,symbols,List.length_map,advance_add] using NativeCountedLoop.trace_trans ta tb

theorem common_budget (small large : ℕ) (h : small≤large) (xs : List Bool) (rs : List (List Bool × List Bool)) :
    batchBudget small (large-small) xs rs ≤ (rs.length+1)*(80*xs.length+37*large+84) := by
  have hr : recordBudget small (large-small) xs ≤ 80*xs.length+37*large+84 := by unfold recordBudget;omega
  have hs : PreparedPair.stopBudget small xs+1 ≤ 80*xs.length+37*large+84 := by unfold PreparedPair.stopBudget;omega
  unfold batchBudget
  calc
    _ ≤ rs.length*(80*xs.length+37*large+84)+(80*xs.length+37*large+84) :=
      by have hm:=Nat.mul_le_mul_left rs.length hr;omega
    _ = _ := by ring

end TransposeFollowup.NormalizedBatch

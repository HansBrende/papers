import TransposeFollowup.BatchMembershipRecord
import TransposeFollowup.NormalizedBatchLoop

namespace TransposeFollowup.BatchMembership
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def batchBudget (small : ℕ) (xs : List Bool) (rs : List (List Bool × List Bool)) :=
  rs.length*recordBudget small xs+PreparedPair.stopBudget small xs+1

theorem records_trace (small : ℕ) (found : Bool) (xs : List Bool) (a : List Bool × List Bool)
    (ha1 : a.1.length=2*xs.length+small) (ha2 : a.2.length=2*xs.length+small) (hp : 0<2*xs.length+small)
    (rs : List (List Bool × List Bool)) (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ rs.length*recordBudget small xs,Trace small t
      (cfg (start small found) (queryBank xs a ⟨pre,symbols (NormalizedBatch.inputBits rs)++suffix⟩) pos)
      (cfg (start small (found || rs.any (NativePairEqual.samePair a)))
        (queryBank xs a ⟨(symbols (NormalizedBatch.inputBits rs)).reverse++pre,suffix⟩) (advance pos (NormalizedBatch.inputBits rs).length)) := by
  induction rs generalizing found pre pos with
  | nil =>
    refine ⟨0,by simp,?_⟩
    simp only [NormalizedBatch.inputBits,List.flatMap_nil,symbols,List.map_nil,List.nil_append,List.reverse_nil,List.length_nil,
      List.any_nil,Bool.or_false,advance_zero]
    exact .refl _
  | cons p rs ih =>
    have hpw:=hw p (by simp)
    have hrw : ∀ q ∈ rs,q.1.length=2*xs.length+small ∧ q.2.length=2*xs.length+small := by
      intro q hq;exact hw q (by simp [hq])
    have hlen : (p.1++p.2).length=2*(2*xs.length+small) := by simp [hpw.1,hpw.2,two_mul]
    obtain ⟨x,hx,tx⟩:=record_trace small found xs a ha1 ha2 p.1 p.2 hp hpw.1 hpw.2 pre (symbols (NormalizedBatch.inputBits rs)++suffix) pos
    rw [← hlen] at tx
    obtain ⟨y,hy,ty⟩:=ih (found || NativePairEqual.samePair a p) hrw ((symbols (p.1++p.2)).reverse++pre) (advance pos (p.1++p.2).length)
    refine ⟨x+y,?_,?_⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · simpa only [NormalizedBatch.inputBits,List.flatMap_cons,symbols,List.map_append,List.reverse_append,List.append_assoc,
        List.length_append,advance_add,Nat.add_assoc,List.any_cons,Bool.or_assoc] using NativeCountedLoop.trace_trans tx ty

theorem batch_trace (small : ℕ) (found : Bool) (xs : List Bool) (a : List Bool × List Bool)
    (ha1 : a.1.length=2*xs.length+small) (ha2 : a.2.length=2*xs.length+small) (hp : 0<2*xs.length+small)
    (rs : List (List Bool × List Bool)) (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ batchBudget small xs rs,Trace small t
      (cfg (start small found) (queryBank xs a ⟨pre,NormalizedBatch.inputBatch rs++suffix⟩) pos)
      (cfg (.done (found || rs.any (NativePairEqual.samePair a)))
        (queryBank xs a ⟨(NormalizedBatch.inputBatch rs).reverse++pre,suffix⟩) (advance pos (NormalizedBatch.inputBatch rs).length)) := by
  obtain ⟨x,hx,tx⟩:=records_trace small found xs a ha1 ha2 hp rs hw pre (.stop::suffix) pos
  obtain ⟨y,hy,ty⟩:=stop_trace small (found || rs.any (NativePairEqual.samePair a)) xs a
    ((symbols (NormalizedBatch.inputBits rs)).reverse++pre) suffix (advance pos (NormalizedBatch.inputBits rs).length)
  refine ⟨x+y,by unfold batchBudget;omega,?_⟩
  simpa only [NormalizedBatch.inputBatch,List.append_assoc,List.cons_append,List.nil_append,List.reverse_append,List.reverse_cons,List.reverse_nil,
    List.length_append,List.length_cons,List.length_nil,symbols,List.length_map,advance_add] using NativeCountedLoop.trace_trans tx ty

theorem batch_budget_le (small : ℕ) (xs : List Bool) (rs : List (List Bool × List Bool)) :
    batchBudget small xs rs≤(rs.length+1)*recordBudget small xs := by
  unfold batchBudget
  have h : PreparedPair.stopBudget small xs+1≤recordBudget small xs := by unfold PreparedPair.stopBudget recordBudget;omega
  rw [Nat.add_mul,Nat.one_mul]
  omega

end TransposeFollowup.BatchMembership

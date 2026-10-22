import TransposeFollowup.PrefixMembershipMachine

namespace TransposeFollowup.PrefixMembership
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {K : ℕ}

def segments {α : Type*} (V : Fin K → List α) : ℕ → ℕ → List α
  | _,0 => []
  | k,q+1 => if h : k<K then V ⟨k,h⟩++segments V (k+1) q else []

theorem segments_ofFn {α : Type*} (V : Fin K → List α) (q k : ℕ) (hk : k+q≤K) :
    segments V k q=(List.ofFn (fun j : Fin q => V ⟨k+j.val,by omega⟩)).flatten := by
  induction q generalizing k with
  | zero => simp [segments]
  | succ q ih =>
    have hkK : k<K := by omega
    simp only [segments,hkK,↓reduceDIte,List.ofFn_succ,List.flatten_cons]
    rw [ih (k+1) (by omega)]
    congr 1
    congr 1
    apply congrArg List.ofFn
    funext j
    congr 2
    simp only [Fin.val_succ]
    omega

def stream (batches : Fin K → List (List Bool × List Bool)) (k q : ℕ) :=
  segments (fun i => NormalizedBatch.inputBatch (batches i)) k q
def scanBudget (small : ℕ) (xs : List Bool) (batches : Fin K → List (List Bool × List Bool)) (k q : ℕ) :=
  ((segments batches k q).length+q)*BatchMembership.recordBudget small xs+q

theorem rest_trace (small : ℕ) (xs : List Bool) (a : List Bool × List Bool)
    (ha1 : a.1.length=2*xs.length+small) (ha2 : a.2.length=2*xs.length+small) (hp : 0<2*xs.length+small)
    (batches : Fin K → List (List Bool × List Bool))
    (hw : ∀ i,∀ p ∈ batches i, p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (q k : ℕ) (hk : k+q=K) (found : Bool) (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ scanBudget small xs batches k q,Trace small K t
      (cfg (entry small K k found) (BatchMembership.queryBank xs a ⟨pre,stream batches k q++suffix⟩) pos)
      (cfg (.rewind (found || (segments batches k q).any (NativePairEqual.samePair a)) .left)
        (BatchMembership.queryBank xs a ⟨(stream batches k q).reverse++pre,suffix⟩)
        (BatchMembership.advance pos (stream batches k q).length)) := by
  induction q generalizing k found pre pos with
  | zero =>
    have he : k=K := by omega
    subst k
    refine ⟨0,by simp [scanBudget,segments],?_⟩
    simp only [entry,lt_self_iff_false,↓reduceDIte,stream,segments,List.nil_append,List.reverse_nil,List.length_nil,
      List.any_nil,Bool.or_false,BatchMembership.advance_zero]
    exact .refl _
  | succ q ih =>
    have hkK : k<K := by omega
    let i : Fin K:=⟨k,hkK⟩
    obtain ⟨x,hx,tx⟩:=phase_trace small i found xs a ha1 ha2 hp (batches i) (hw i) pre (stream batches (k+1) q++suffix) pos
    obtain ⟨y,hy,ty⟩:=ih (k+1) (by omega) (found || (batches i).any (NativePairEqual.samePair a))
      ((NormalizedBatch.inputBatch (batches i)).reverse++pre) (BatchMembership.advance pos (NormalizedBatch.inputBatch (batches i)).length)
    refine ⟨x+y,?_,?_⟩
    · have hb:=BatchMembership.batch_budget_le small xs (batches i)
      simp only [scanBudget,segments,hkK,↓reduceDIte,List.length_append] at hy ⊢
      have he : (batches ⟨k,hkK⟩).length+(segments batches (k+1) q).length+(q+1)=
          ((batches i).length+1)+((segments batches (k+1) q).length+q) := by dsimp [i];omega
      rw [he,Nat.add_mul]
      omega
    · simpa only [stream,segments,hkK,↓reduceDIte,List.append_assoc,List.reverse_append,List.length_append,
        BatchMembership.advance_add,List.any_append,Bool.or_assoc]
        using NativeCountedLoop.trace_trans tx ty

theorem stream_nonblank (batches : Fin K → List (List Bool × List Bool)) (q k : ℕ) :
    ∀ s ∈ stream batches k q,s≠.blank := by
  induction q generalizing k with
  | zero => simp [stream,segments]
  | succ q ih =>
    unfold stream segments
    split
    · intro s hs
      rcases List.mem_append.mp hs with hs|hs
      · simp only [NormalizedBatch.inputBatch,List.mem_append,List.mem_singleton] at hs
        rcases hs with hs|hs
        · obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hs
          simp
        · subst s;simp
      · exact ih (k+1) s hs
    · simp

theorem complete_trace (small : ℕ) (xs : List Bool) (a : List Bool × List Bool)
    (ha1 : a.1.length=2*xs.length+small) (ha2 : a.2.length=2*xs.length+small) (hp : 0<2*xs.length+small)
    (batches : Fin K → List (List Bool × List Bool))
    (hw : ∀ i,∀ p ∈ batches i, p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ 3*scanBudget small xs batches 0 K+3,Trace small K t
      (cfg (start small K) (BatchMembership.queryBank xs a ⟨[],stream batches 0 K++suffix⟩) pos)
      (cfg (.rewind ((segments batches 0 K).any (NativePairEqual.samePair a)) .done)
        (BatchMembership.queryBank xs a ⟨[],stream batches 0 K++suffix⟩) pos) := by
  obtain ⟨x,hx,tx⟩:=rest_trace small xs a ha1 ha2 hp batches hw K 0 (by omega) false [] suffix pos
  simp only [Bool.false_or,List.append_nil] at tx
  have hb:=NativePrefixRewind.work_trace_bounds (program small K) tx (2 : Fin 7)
  have hlen : (stream batches 0 K).length≤x := by
    simp only [cfg,BatchMembership.advance,ite_true] at hb
    omega
  obtain ⟨y,hy,ty⟩:=rewind_call small K ((segments batches 0 K).any (NativePairEqual.samePair a)) xs a
    (stream batches 0 K) suffix (stream_nonblank batches K 0) pos
  exact ⟨x+y,by omega,NativeCountedLoop.trace_trans tx ty⟩

end TransposeFollowup.PrefixMembership

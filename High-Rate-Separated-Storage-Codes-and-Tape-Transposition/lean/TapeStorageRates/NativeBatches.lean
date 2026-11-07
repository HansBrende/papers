import TapeStorageRates.NativeRun

/-! Actual fine motion of a complete core and of the final drain. These
statements concern the frozen trace of the compiled native machine itself. -/

namespace TapeStorageRates.Native

open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth

private theorem Follows.chain {k : ℕ} {τ : Trace k} {t u : ℕ} {a b : List (Motion k)}
    (ha : Follows τ t a) (hb : Follows τ u b) (h : u = t+a.length) :
    Follows τ t (a++b) := ha.append (h ▸ hb)

theorem actual_core_from {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (o : Option (Config (machine M hs))) (t : ℕ)
    (h : (labelFrom M hs w o t).1 = .left ⟨0,hs⟩) :
    ∃ r : Registers M s,
      labelFrom M hs w o (t+(10*s+1)) =
        (if r.stopped then Phase.drain ⟨0,hs⟩ else Phase.left ⟨0,hs⟩,r) ∧
      Follows (traceFrom (machine M hs) w o) t (coreMoves s r.desc) := by
  let z : Fin s := ⟨0,hs⟩
  let z3 : Fin (3*s) := ⟨0,by omega⟩
  let t1 := t+s
  let t2 := t1+3*s
  let t3 := t2+1
  let t4 := t3+3*s
  let t5 := t4+s
  let t6 := t5+s
  obtain ⟨⟨l1,-⟩,m0⟩ := runPhase_from hs hs w o t .left (.read z3) (fun _ => True)
    (fun _ => straight M.k .left) ⟨h,trivial⟩ (by
      intro i r _ x a
      exact ⟨_,rfl,rfl,trivial,rfl⟩)
  obtain ⟨⟨l2,-⟩,m1⟩ := runPhase_from hs z3.isLt w o t1 .read .table (fun _ => True)
    (fun i => straight M.k (if i.val+1<3*s then .right else .stay)) ⟨l1,trivial⟩ (by
      intro i r _ x a
      exact ⟨_,rfl,rfl,trivial,rfl⟩)
  let r := updateTable hs (labelFrom M hs w o t2).2
  have e2 : labelFrom M hs w o t2 = (.table,(labelFrom M hs w o t2).2) := Prod.ext l2 rfl
  have he := run_drive_from (o := o) (M := M) (hs := hs) (w := w) (t := t2)
    (z := uniform (.write z3) r .stay (workAt (machine M hs) w o t2)) (by rw [e2]; rfl)
  have m2 := follows_single he.2
  obtain ⟨l4,m3⟩ := runPhase_from hs z3.isLt w o t3 .write (.home z) (· = r)
    (fun i => straight M.k (if i.val+1<3*s then .left else .stay))
    ⟨congrArg Prod.fst he.1,congrArg Prod.snd he.1⟩ (by
      intro i r' hr x a
      subst r'
      exact ⟨_,rfl,rfl,rfl,rfl⟩)
  obtain ⟨l5,m4⟩ := runPhase_from hs hs w o t4 .home (.carry z) (· = r)
    (fun _ => straight M.k .right) l4 (by
      intro i r' hr x a
      subst r'
      exact ⟨_,rfl,rfl,rfl,rfl⟩)
  obtain ⟨l6,m5⟩ := runPhase_from hs hs w o t5 .carry (.emit z) (· = r)
    (fun _ => (direction r.desc.1.1, fun j => direction (r.desc.1.2 j), false)) l5 (by
      intro i r' hr x a
      subst r'
      exact ⟨_,rfl,rfl,rfl,rfl⟩)
  obtain ⟨l7,m6⟩ := runPhase_from hs hs w o t6 .emit (if r.stopped then .drain z else .left z)
    (· = r) (fun _ => straight M.k .stay r.desc.2) l6 (by
      intro i r' hr x a
      subst r'
      refine ⟨_,rfl,rfl,rfl,?_⟩
      cases hb : r.desc.2 <;> simp [instrMotion, uniform, straight])
  refine ⟨r, ?_, ?_⟩
  · have ht : t+(10*s+1)=t6+s := by dsimp [t6,t5,t4,t3,t2,t1]; omega
    rw [ht]
    exact Prod.ext l7.1 l7.2
  · have f5 := m5.chain m6 (by simp [t6])
    have f4 := m4.chain f5 (by simp [t5])
    have f3 := m3.chain f4 (by simp [t4])
    have f2 := m2.chain f3 (by simp [t3])
    have f1 := m1.chain f2 (by simp [t2])
    have f0 := m0.chain f1 (by simp [t1])
    simpa [coreMoves, instrMotion, uniform, straight] using f0

theorem actual_drain_from {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (o : Option (Config (machine M hs))) (t : ℕ)
    (r : Registers M s) (h : labelFrom M hs w o t = (.drain ⟨0,hs⟩,r)) :
    labelFrom M hs w o (t+s) = (.done,r) ∧
      Follows (traceFrom (machine M hs) w o) t
        (List.ofFn (fun i : Fin s => straight M.k .stay (decide (i.val<r.pendingLen.val)))) ∧
      traceFrom (machine M hs) w o (t+s) = none := by
  obtain ⟨e,m⟩ := runPhase_from hs hs w o t .drain .done (· = r)
    (fun i => straight M.k .stay (decide (i.val<r.pendingLen.val)))
    ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩ (by
      intro i r' hr x a
      subst r'
      refine ⟨_,rfl,rfl,rfl,?_⟩
      by_cases hi : i.val<r.pendingLen.val <;> simp [instrMotion, uniform, straight, hi])
  have e' : labelFrom M hs w o (t+s) = (.done,r) := Prod.ext e.1 e.2
  refine ⟨e', m, ?_⟩
  unfold traceFrom
  rw [transFrom_machine,show labelFrom M hs w o (t+s) = (.done,r) from e']
  rfl

end TapeStorageRates.Native

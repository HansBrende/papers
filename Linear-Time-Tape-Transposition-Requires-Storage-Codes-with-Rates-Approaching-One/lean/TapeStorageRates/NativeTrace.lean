import TapeStorageRates.NativeBatches

/-! Every halting run of the actual aligned compiler has a complete fine native
trace specified by the per-batch carries, flush decisions, and final residue. -/

namespace TapeStorageRates.Native

open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth

private theorem word_cons {k s : ℕ} (a : Descriptor k) (as : List (Descriptor k)) (r : Fin s) :
    fineWord s r (a::as) = coreMoves s a ++ fineWord s r as := by
  simp only [fineWord,List.flatMap_cons,List.append_assoc]

private theorem before_halt {k : ℕ} {τ : Trace k} {t T : ℕ} {xs : List (Motion k)}
    (h : Follows τ t xs) (ht : t≤T) (hT : τ T=none) : t+xs.length≤T := by
  by_contra! hbad
  have i : T-t<xs.length := by omega
  have e := h (T-t) i
  rw [show t+(T-t)=T by omega,hT] at e
  contradiction

private theorem haltingSuffixFrom (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool)
    (o : Option (Config (machine M hs)))
    (T : ℕ) (H : (traceFrom (machine M hs) w o).HaltsAt T)
    (t : ℕ) (ht : t≤T) (start : (labelFrom M hs w o t).1 = .left ⟨0,hs⟩) :
    ∃ (as : List (Descriptor M.k)) (r : Fin s),
      t+(fineWord s r as).length = T ∧
      Follows (k := M.k) (traceFrom (machine M hs) w o) t (fineWord (k := M.k) s r as) := by
  obtain ⟨reg, pend, seen⟩ := actual_core_from hs w o t start
  have hlen := length_coreMoves hs reg.desc
  have mid : t+(10*s+1)≤T := by simpa [hlen] using before_halt seen ht H.2
  by_cases hc : reg.stopped = true
  · have hd : labelFrom M hs w o (t+(10*s+1)) = (.drain ⟨0,hs⟩,reg) := by simpa [hc] using pend
    obtain ⟨-,tail,stop⟩ := actual_drain_from hs w o _ reg hd
    let last : List (Motion M.k) :=
      List.ofFn fun i : Fin s => straight M.k .stay (decide (i.val<reg.pendingLen.val))
    have ll : last.length = s := List.length_ofFn
    have lo := before_halt (xs := last) tail mid H.2
    rw [ll] at lo
    have eqT : t+(10*s+1)+s = T := le_antisymm lo (by
      by_contra! he
      exact H.1 _ he stop)
    refine ⟨[reg.desc], reg.pendingLen, ?_, ?_⟩
    · simpa [length_fineWord, Nat.add_assoc] using eqT
    · rw [word_cons]
      apply seen.append
      simpa [fineWord, hlen] using tail
  · have hc' : reg.stopped = false := by simpa using hc
    have hl : (labelFrom M hs w o (t+(10*s+1))).1 = .left ⟨0,hs⟩ := by simp [pend,hc']
    obtain ⟨as,r,len,tail⟩ := haltingSuffixFrom M hs w o T H _ mid hl
    refine ⟨reg.desc::as,r,?_,?_⟩
    · rw [length_fineWord] at len ⊢
      simp only [List.length_cons,Nat.mul_succ]
      omega
    · rw [word_cons]
      exact seen.append (by simpa [hlen,fineWord] using tail)
termination_by T-t
decreasing_by omega

/-- No input-output correctness assumption is needed for the observable trace
factorization of the actual native machine. -/
theorem trace_factor_from_left {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool)
    (o : Option (Config (machine M hs))) (start : (labelFrom M hs w o 0).1 = .left ⟨0,hs⟩) {T : ℕ}
    (H : (traceFrom (machine M hs) w o).HaltsAt T) :
    ∃ (as : List (Descriptor M.k)) (r : Fin s),
      T = (10*s+1)*as.length+s ∧ traceFrom (machine M hs) w o = replay r as := by
  obtain ⟨as,r,len,seen⟩ := haltingSuffixFrom M hs w o T H 0 (Nat.zero_le _) start
  have len' : (fineWord s r as).length = T := by simpa using len
  refine ⟨as,r,by rw [← len',length_fineWord],?_⟩
  funext i
  by_cases hi : i<T
  · have hl : i<(fineWord s r as).length := len' ▸ hi
    simpa [replay,List.getElem?_eq_getElem hl] using seen i hl
  · have hz := (traceFrom_none_iff (machine M hs) w o T).mp H.2
    have hnone := (traceFrom_none_iff (machine M hs) w o i).mpr
      (transFrom_frozen hz (by omega))
    rw [hnone]
    exact (List.getElem?_eq_none (by omega : (fineWord s r as).length ≤ i)).symm

theorem halting_trace {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) {T : ℕ}
    (H : (trace (machine M hs) w).HaltsAt T) :
    ∃ (as : List (Descriptor M.k)) (r : Fin s),
      T = (10*s+1)*as.length+s ∧ trace (machine M hs) w = replay r as := by
  apply trace_factor_from_left hs w none _ H
  change (labelAt M hs w 0).1 = _
  simp [initialLabel]

/-- At most the claimed number of variable-output traces occur on compiled
halting runs whose native horizon permits at most R complete batches. -/
theorem halting_support {M : TM} {s : ℕ} (hs : 0<s) (R : ℕ) :
    ∃ S : Finset (Trace M.k), S.card ≤ s*(1+2*3^(M.k+1))^R ∧
      ∀ w T, (trace (machine M hs) w).HaltsAt T → T ≤ (10*s+1)*R+s →
        trace (machine M hs) w ∈ S := by
  obtain ⟨S,hS,contains⟩ := replay_support_variable (k := M.k) s R
  refine ⟨S,hS,?_⟩
  intro w T ht hR
  obtain ⟨as,r,len,e⟩ := halting_trace hs w ht
  rw [e]
  apply contains
  have := Nat.le_of_mul_le_mul_left
    (show (10*s+1)*as.length≤(10*s+1)*R by omega) (by omega)
  exact this

def appendsIn {k : ℕ} (xs : List (Motion k)) : ℕ :=
  (xs.map (fun m => m.2.2)).count true

theorem appends_core {k s : ℕ} (a : Descriptor k) :
    appendsIn (coreMoves s a) = if a.2 then s else 0 := by
  cases hb : a.2 <;> simp [appendsIn,coreMoves,straight,List.map_ofFn,hb,
    Function.comp_def,List.count_replicate]

private theorem count_prefix (s m : ℕ) (hm : m ≤ s) :
    (List.ofFn (fun i : Fin s => decide (i.val < m))).count true = m := by
  induction s generalizing m with
  | zero =>
    have := Nat.eq_zero_of_le_zero hm
    simp [this]
  | succ s ih =>
    rw [List.ofFn_succ]
    cases m with
    | zero => simp [List.count_replicate]
    | succ m =>
      have h' := ih m (by omega)
      simpa using h'

theorem appends_fineWord {k s : ℕ} (r : Fin s) (as : List (Descriptor k)) :
    appendsIn (fineWord s r as) = s*(as.countP fun a => a.2)+r.val := by
  induction as with
  | nil => simpa [appendsIn,fineWord,straight,List.map_ofFn,Function.comp_def] using count_prefix s r.val r.isLt.le
  | cons a as ih =>
    rw [word_cons,show ∀ x y : List (Motion k), appendsIn (x++y)=appendsIn x+appendsIn y by
      intro x y; simp [appendsIn],appends_core,ih]
    cases hb : a.2 <;> simp [hb,Nat.mul_succ]
    omega

abbrev outputAt (M : TM) (w : List Bool) (o : Option (Config M)) (t : ℕ) :=
  (transFrom M w o t).bind fun z => z.2.2.2

theorem runAt_output_succ {M : TM} {w : List Bool} {o : Option (Config M)} (t : ℕ) :
    (runAt M w o (t+1)).outRev.length = (runAt M w o t).outRev.length +
      (if (outputAt M w o t).isSome then 1 else 0) := by
  rw [runAt_succ,next,step_eq_lookup]
  change ((Option.map (commit (runAt M w o t)) (transFrom M w o t)).getD
    (runAt M w o t)).outRev.length = _
  cases hz : transFrom M w o t with
  | none => simp [outputAt,hz]
  | some z => cases ho : z.2.2.2 <;> simp [outputAt,commit,hz,ho]

/-- The output length of a genuine native run counts exactly its true trace flags. -/
theorem follows_output_from {M : TM} {w : List Bool} {o : Option (Config M)} {t : ℕ} {xs : List (Motion M.k)}
    (h : Follows (traceFrom M w o) t xs) :
    (runAt M w o (t+xs.length)).outRev.length = (runAt M w o t).outRev.length+appendsIn xs := by
  induction xs generalizing t with
  | nil => simp [appendsIn]
  | cons a xs ih =>
    have e : traceFrom M w o t = some a := by
      have e' := h 0 (by simp)
      change traceFrom M w o (t+0) = some a at e'
      simpa only [Nat.add_zero] using e'
    have b : (outputAt M w o t).isSome = a.2.2 := by
      rcases hz : transFrom M w o t with _ | z
      · simp [traceFrom,hz] at e
      · have he : ((z.2.1,fun j => (z.2.2.1 j).2,z.2.2.2.isSome) : Motion M.k) = a := by
          simpa [traceFrom,hz] using e
        rw [← he]
        simp [outputAt,hz]
    have rest : Follows (traceFrom M w o) (t+1) xs := by
      intro i hi
      have e' := h (i+1) (by simpa using hi)
      change traceFrom M w o (t+(i+1)) = some xs[i] at e'
      simpa only [show t+(i+1)=t+1+i by omega] using e'
    rw [show t+(a::xs).length = t+1+xs.length by simp; omega,ih rest,runAt_output_succ,b]
    cases ha : a.2.2 <;> simp [appendsIn,ha]
    omega

theorem follows_output {M : TM} {w : List Bool} {t : ℕ} {xs : List (Motion M.k)}
    (h : Follows (trace M w) t xs) :
    (run M w (t+xs.length)).outRev.length = (run M w t).outRev.length+appendsIn xs :=
  follows_output_from (o := none) h

/-- The multiplicative drain factor disappears for compiled runs of common
output length, since it fixes the residue. The horizon here is in native
simulator ticks. -/
theorem halting_support_fixed {M : TM} {s : ℕ} (hs : 0<s) (R outLen : ℕ) :
    ∃ S : Finset (Trace M.k), S.card ≤ (1+2*3^(M.k+1))^R ∧
      ∀ w T, (trace (machine M hs) w).HaltsAt T → T ≤ (10*s+1)*R+s →
        (run (machine M hs) w T).outRev.length = outLen → trace (machine M hs) w ∈ S := by
  let r : Fin s := ⟨outLen%s,Nat.mod_lt _ hs⟩
  obtain ⟨S,hS,contains⟩ := replay_support (k := M.k) r R
  refine ⟨S,hS,?_⟩
  intro w T ht hR ho
  obtain ⟨as,u,len,e⟩ := halting_trace hs w ht
  have l : (fineWord s u as).length = T := (length_fineWord u as).trans len.symm
  have hf : Follows (k := M.k) (trace (machine M hs) w) 0 (fineWord s u as) := by
    intro i hi
    simp [e,replay,List.getElem?_eq_getElem hi]
  have cnt := follows_output hf
  change (run (machine M hs) w (0+(fineWord (k := M.k) s u as).length)).outRev.length =
    0+appendsIn (fineWord (k := M.k) s u as) at cnt
  rw [Nat.zero_add,l,ho,Nat.zero_add, appends_fineWord] at cnt
  have ue : u=r := Fin.ext (by
    change u.val = outLen%s
    rw [cnt,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt u.isLt])
  rw [e,ue]
  apply contains
  exact Nat.le_of_mul_le_mul_left (show (10*s+1)*as.length≤(10*s+1)*R by omega) (by omega)

end TapeStorageRates.Native

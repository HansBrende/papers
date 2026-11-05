import TapeStorageRates.NativeSimulation
import TapeStorageRates.NativeWarmSeed

/-! Same-time, same-output refinement of any virtual suffix, after the physical
heads are designated as new anchors. These are statements about the original
stepN and step of both actual native machines. -/

namespace TapeStorageRates.Native

open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth

theorem warm_boundary (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool) (c : Config M) :
    BoundaryAt hs w (some (warmSeed M hs c)) 0 c false := by
  refine ⟨warmRegs hs c,c.inPos,c.workPos,c.outRev,?_,rfl,?_,?_,?_⟩
  · change warmSeed M hs c = _
    simp [warmSeed,Frame.native,anchored]
  · simp [warmRegs,initialRegs]
  · simp [warmRegs,initialRegs]
  · simp [warmRegs,initialRegs,offsetWord]

theorem warm_run_halts (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool)
    (c d : Config M) (n : ℕ) (h : stepN M w n c = some d) (halt : step M w d = none) :
    let U := (10*s+1)*(n/s+1)+s
    (traceFrom (machine M hs) w (some (warmSeed M hs c))).HaltsAt U ∧
      (runAt (machine M hs) w (some (warmSeed M hs c)) U).outRev=d.outRev := by
  have start := warm_boundary M hs w c
  have hz : runAt M w (some c) 0 = c := rfl
  have ed : runAt M w (some c) n = d := ((stepN_eq_some_iff ..).mp h).2
  have result := simulates_from_boundary M hs w (some c) (some (warmSeed M hs c))
    (hz ▸ start) ((haltsFrom_iff).mpr ⟨d,h,halt⟩)
  rwa [ed] at result

/-- A successful native suffix has exactly the advertised number of aligned
ticks and the same already-reversed full output. -/
theorem warm_simulates_halt (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool)
    (c d : Config M) (n : ℕ) (h : stepN M w n c = some d) (halt : step M w d = none) :
    let U := (10*s+1)*(n/s+1)+s
    ∃ f, stepN (machine M hs) w U (warmSeed M hs c)=some f ∧
      step (machine M hs) w f=none ∧ f.outRev=d.outRev := by
  obtain ⟨hT,hout⟩ := warm_run_halts M hs w c d n h halt
  obtain ⟨f,hf,stop⟩ := haltsFrom_iff.mp hT
  refine ⟨f,hf,stop,?_⟩
  rw [← ((stepN_eq_some_iff ..).mp hf).2]
  exact hout

theorem warm_halts_iff (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool) (c : Config M) :
    (∃ n f, stepN (machine M hs) w n (warmSeed M hs c)=some f ∧ step (machine M hs) w f=none) ↔
    ∃ n d, stepN M w n c=some d ∧ step M w d=none := by
  classical
  constructor
  · rintro ⟨t,f,hf,stop⟩
    have ht := haltsFrom_iff.mpr ⟨f,hf,stop⟩
    by_contra bad
    have all (i : ℕ) : transFrom M w (some c) i ≠ none := by
      intro dead
      have E : ∃ u, transFrom M w (some c) u = none := ⟨i,dead⟩
      apply bad
      refine ⟨Nat.find E,haltsFrom_iff.mp ⟨?_,(traceFrom_none_iff ..).mpr (Nat.find_spec E)⟩⟩
      intro u hu stop
      exact Nat.find_min E hu ((traceFrom_none_iff ..).mp stop)
    let orig := some (warmSeed M hs c)
    obtain ⟨r,ai,aw,out,b,-,-,-,-⟩ := full_blocks_from M hs w (some c) orig
      (warm_boundary M hs w c) (t+1) (fun i _ => all i)
    have later : t≤(10*s+1)*(t+1) := by nlinarith
    have dead := transFrom_frozen ((traceFrom_none_iff ..).mp ht.2) later
    rw [transFrom_machine,boundary_label_from b] at dead
    simp [anchored,drive] at dead
  · rintro ⟨n,d,hn,hd⟩
    obtain ⟨f,hf,stop,-⟩ := warm_simulates_halt M hs w c d n hn hd
    exact ⟨_,f,hf,stop⟩

/-- The exact full motion word after a prefix. Its drain count is determined
by the number of additional printed bits, and all its other data fit in
one carry/flush descriptor per source batch. -/
theorem warm_trace_of_halt (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool)
    (c d : Config M) (n : ℕ) (h : stepN M w n c = some d) (halt : step M w d = none) :
    ∃ (as : List (Descriptor M.k)) (r : Fin s), as.length=n/s+1 ∧
      r.val=(d.outRev.length-c.outRev.length)%s ∧
      traceFrom (machine M hs) w (some (warmSeed M hs c))=replay r as := by
  let o := some (warmSeed M hs c)
  let U := (10*s+1)*(n/s+1)+s
  obtain ⟨ht,hout⟩ := warm_run_halts M hs w c d n h halt
  have start : (labelFrom M hs w o 0).1 = .left ⟨0,hs⟩ := by
    change ((labelEquiv M hs).symm ((labelEquiv M hs) (.left ⟨0,hs⟩, warmRegs hs c))).1 = _
    rw [Equiv.symm_apply_apply]
  obtain ⟨as,r,len,seen⟩ := trace_factor_from_left hs w o start ht
  have el : as.length = n/s+1 := by
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0<10*s+1) (by omega)
  have wl : (fineWord s r as).length = U := (length_fineWord r as).trans len.symm
  have follows : Follows (k := M.k) (traceFrom (machine M hs) w o) 0 (fineWord s r as) := by
    intro i hi
    simp [seen,replay,List.getElem?_eq_getElem hi]
  have cnt := follows_output_from (o := o) follows
  change (runAt (machine M hs) w o (0+(fineWord s r as).length)).outRev.length =
    c.outRev.length+appendsIn (fineWord s r as) at cnt
  rw [Nat.zero_add,wl,hout,appends_fineWord] at cnt
  refine ⟨as,r,el,?_,seen⟩
  rw [cnt,Nat.add_sub_cancel_left,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt r.isLt]

end TapeStorageRates.Native

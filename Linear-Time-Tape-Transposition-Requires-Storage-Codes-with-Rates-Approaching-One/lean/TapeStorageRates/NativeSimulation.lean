import TapeStorageRates.NativeWrite
import TapeStorageRates.NativeEmit
import TapeStorageRates.NativeTrace

/-! The complete simulation invariant for aligned native batches. -/

namespace TapeStorageRates.Native

open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth

/-- At a boundary the actual native tapes equal the simulated work tapes.
The physical heads are the anchors and the outstanding output is in control. -/
def BoundaryAt {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (o : Option (Config (machine M hs))) (t : ℕ)
    (c : Config M) (draining : Bool) : Prop :=
  ∃ (r : Registers M s) (ai : ℤ) (aw : Fin M.k → ℤ) (out : List Bool),
    runAt (machine M hs) w o t =
      (anchored (if draining then .drain ⟨0,hs⟩ else .left ⟨0,hs⟩)
        r ai aw 0 c.work out).native hs ∧ r.q = c.state ∧
    c.inPos = ai + r.oi.val ∧ (∀ j, c.workPos j = aw j+(r.ow j).val) ∧
    c.outRev = (offsetWord r.pendingLen r.pending).reverse++out

abbrev Boundary {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) :=
  BoundaryAt (M := M) hs w none

theorem initial_boundary (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool) :
    Boundary hs w 0 (init M) false := by
  refine ⟨initialRegs M hs,0,fun _ => 0,[],?_,rfl,by rfl,fun _ => rfl,?_⟩
  · have e : (labelEquiv M hs) (Phase.left ⟨0,hs⟩,initialRegs M hs)=0 :=
      labelEquiv_initial M hs
    simp [run_zero,Frame.native,anchored,init,e]
  · simp [initialRegs,offsetWord,init]

/-- One batch of the actual compiled native machine refines the source lookup,
including the incomplete last batch and its flag. -/
theorem boundary_step_from {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (o : Option (Config (machine M hs))) (t : ℕ)
    (c : Config M) (h : BoundaryAt hs w o t c false) :
    let z := advance M (readInput w) s c
    BoundaryAt hs w o (t+(10*s+1)) z.1 z.2 := by
  obtain ⟨r,ai,aw,out,h0,hq,hi,hw,ho⟩ := h
  let cap := {r with inp := capture s (readInput w) ai, wrk := fun j => capture s (c.work j) (aw j)}
  let c0 := localConfig M s cap.q cap.oi cap.ow cap.wrk
  let v := advance M (windowRead cap.inp none) s c0
  let d := advance M (readInput w) s c
  let r' := updateTable hs cap
  have hloc : WindowAgrees s ai aw c.outRev d.1 v.1 ∧ d.2=v.2 := by
    simpa only [d,v,c0,cap,hq] using native_batch_local M s w c ai aw r.oi r.ow hi hw
  have vi := (advance_fits (I := windowRead cap.inp none)
    (localConfig_fits cap.q cap.oi cap.ow cap.wrk)).1
  have vw := (advance_fits (I := windowRead cap.inp none)
    (localConfig_fits cap.q cap.oi cap.ow cap.wrk)).2
  have status : r'.stopped=d.2 := hloc.2.symm
  have outside (j : Fin M.k) (p : ℤ) (hp : ¬ Fits s 0 (p-aw j)) :
      d.1.work j p = c.work j p := by
    apply advance_outside s s c ai aw _ _ j p hp
    · rw [hi]; have := r.oi.isLt; unfold Fits; omega
    · intro a; rw [hw]; have := (r.ow a).isLt; unfold Fits; omega
  have storage : written (3*s) aw r' c.work = d.1.work := by
    funext j p
    by_cases hp : Fits s 0 (p-aw j)
    · have hit : 2*(s : ℤ)-(3*s : ℕ) ≤ p-aw j ∧ p-aw j < 2*(s : ℤ) := by
        unfold Fits at hp; omega
      rw [written,ite_eq_left hit]
      change windowRead (capture s (v.1.work j) 0) 0 (p-aw j) = _
      rw [windowRead_capture _ _ _ _ hp,zero_add]
      have e := (hloc.1.cells j _ hp).symm
      simpa only [add_sub_cancel] using e
    · have miss : ¬ (2*(s : ℤ)-(3*s : ℕ) ≤ p-aw j ∧ p-aw j < 2*(s : ℤ)) := by
        unfold Fits at hp; omega
      rw [written,ite_eq_right miss]
      exact (outside j p hp).symm
  have print : emitted r' ++ offsetWord r'.pendingLen r'.pending =
      offsetWord r.pendingLen r.pending ++ v.1.outRev.reverse := table_output hs cap
  have p1 := run_left_from hs w o t r ai aw c.work out h0
  have p2 := run_read_from hs w o _ _ _ _ _ _ p1
  have p3 := run_table_from hs w o _ cap _ _ _ _ p2
  have p4 := run_write_from hs w o _ r' _ _ _ _ p3
  rw [storage] at p4
  have p5 := run_home_from hs w o _ r' _ _ _ _ p4
  have p6 := run_carry_from hs w o _ r' _ _ _ _ p5
  have p7 := run_emit_from hs w o _ r' _ _ _ _ p6
  let ai' := ai+(s : ℤ)*moveInt (direction r'.desc.1.1)
  let aw' := fun j => aw j+(s : ℤ)*moveInt (direction (r'.desc.1.2 j))
  refine ⟨r',ai',aw',(emitted r').reverse++out,?_,hloc.1.state.symm,?_,?_,?_⟩
  · change runAt (machine M hs) w o (t+(10*s+1)) = (anchored
      (if d.2 then .drain ⟨0,hs⟩ else .left ⟨0,hs⟩) r' ai' aw' 0 d.1.work _).native hs
    rw [← status,show t+(10*s+1)=t+s+3*s+1+3*s+s+s+s by omega]
    exact p7
  · change d.1.inPos = (ai+_)+_
    rw [hloc.1.inputPos,add_assoc]
    exact congrArg (ai+·) (carry_offset v.1.inPos vi).symm
  · intro j
    change d.1.workPos j = (aw j+_)+_
    rw [hloc.1.workPos,add_assoc]
    exact congrArg (aw j+·) (carry_offset (v.1.workPos j) (vw j)).symm
  · have e := congrArg List.reverse print
    simp only [List.reverse_append,List.reverse_reverse] at e
    change d.1.outRev = _
    rw [hloc.1.output,ho,← List.append_assoc,← e,List.append_assoc]

/-- The physical boundary after any whole number of completed source blocks. -/
theorem full_blocks_from (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool)
    (src : Option (Config M)) (o : Option (Config (machine M hs)))
    (initial : BoundaryAt hs w o 0 (runAt M w src 0) false) (j : ℕ)
    (alive : ∀ i<j*s, transFrom M w src i ≠ none) :
    BoundaryAt hs w o ((10*s+1)*j) (runAt M w src (j*s)) false := by
  induction j with
  | zero => simpa using initial
  | succ j ih =>
    have hjs : (j+1)*s = j*s+s := Nat.succ_mul _ _
    rw [hjs] at alive ⊢
    have prev := ih (fun i hi => alive i (by omega))
    have z := advance_of_stepN (stepsFrom_alive (M := M) (w := w) (o := src) (j*s) s
      (fun i hi => alive _ (by omega)))
    have b := boundary_step_from hs w o _ _ prev
    simpa only [z,Nat.mul_succ] using b

theorem full_blocks (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool) (j : ℕ)
    (alive : ∀ i<j*s, transAt M w i ≠ none) :
    Boundary hs w ((10*s+1)*j) (run M w (j*s)) false :=
  full_blocks_from M hs w none none (initial_boundary M hs w) j alive

theorem boundary_label_from {M : TM} {s : ℕ} {hs : 0<s} {w : List Bool}
    {o : Option (Config (machine M hs))} {t : ℕ} {f : Frame M s}
    (e : runAt (machine M hs) w o t = f.native hs) :
    labelFrom M hs w o t = f.pc := by
  simp only [labelFrom,e,Frame.native,Equiv.symm_apply_apply]

private theorem boundary_label {M : TM} {s : ℕ} {hs : 0<s} {w : List Bool}
    {t : ℕ} {f : Frame M s} (e : run (machine M hs) w t = f.native hs) :
    labelAt M hs w t = f.pc :=
  boundary_label_from (o := none) e

/-- Exact forward simulation at every halting input, in the frozen native model. -/
theorem simulates_from_boundary (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool)
    (src : Option (Config M)) (o : Option (Config (machine M hs)))
    (initial : BoundaryAt hs w o 0 (runAt M w src 0) false) {T : ℕ}
    (H : (traceFrom M w src).HaltsAt T) :
    let U := (10*s+1)*(T/s+1)+s
    (traceFrom (machine M hs) w o).HaltsAt U ∧
      (runAt (machine M hs) w o U).outRev = (runAt M w src T).outRev := by
  have alive (i : ℕ) (hi : i<T) : transFrom M w src i ≠ none :=
    fun h => H.1 i hi ((traceFrom_none_iff ..).mpr h)
  have dead := (traceFrom_none_iff ..).mp H.2
  let j := T/s
  let u := T%s
  have split : j*s+u=T := Nat.div_add_mod' _ _
  have hu : u<s := Nat.mod_lt _ hs
  have start := full_blocks_from M hs w src o initial j (fun i hi => alive i (by omega))
  have z := advance_of_halt (stepsFrom_alive (M := M) (w := w) (o := src) (j*s) u
    (fun i hi => alive _ (by omega))) (by rw [split,step_runAt_none_iff]; exact dead) (s-(u+1))
  rw [show u+(s-(u+1))+1=s by omega,split] at z
  let base := (10*s+1)*(j+1)
  have b : BoundaryAt hs w o base (runAt M w src T) true := by
    simpa only [base,Nat.mul_succ,z] using boundary_step_from hs w o _ _ start
  obtain ⟨r,ai,aw,out,br,-,-,-,outEq⟩ := b
  have bl : labelFrom M hs w o base = (.drain ⟨0,hs⟩,r) := boundary_label_from br
  have finished := run_drain_from hs w o base r ai aw _ out br
  obtain ⟨-,tail,hstop⟩ := actual_drain_from hs w o base r bl
  have last : traceFrom (machine M hs) w o (base+(s-1)) ≠ none := by
    have e := tail (s-1) (by rw [List.length_ofFn]; omega)
    rw [e]
    exact Option.some_ne_none _
  change (traceFrom (machine M hs) w o).HaltsAt (base+s) ∧ _
  refine ⟨⟨?_,hstop⟩,?_⟩
  · intro t ht stopped
    exact last ((traceFrom_none_iff ..).mpr (transFrom_frozen ((traceFrom_none_iff ..).mp stopped) (by omega)))
  · change (runAt (machine M hs) w o (base+s)).outRev = _
    rw [finished]
    exact outEq.symm

theorem simulates_halt (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool) {T : ℕ}
    (H : HaltsAt M w T) :
    let U := (10*s+1)*(T/s+1)+s
    HaltsAt (machine M hs) w U ∧
      (run (machine M hs) w U).outRev = (run M w T).outRev := by
  obtain ⟨endTime,output⟩ := simulates_from_boundary M hs w none none (initial_boundary M hs w)
    ((haltsAt_iff_trace _).mp H)
  exact ⟨(haltsAt_iff_trace _).mpr endTime,output⟩

/-- Conversely a nonhalting source keeps the simulator live at arbitrarily
late batch boundaries. This proves equality of the partial functions. -/
theorem halts_iff (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool) :
    (∃ t, HaltsAt (machine M hs) w t) ↔ ∃ t, HaltsAt M w t := by
  classical
  constructor
  · rintro ⟨t,ht⟩
    by_contra bad
    have all (i : ℕ) : transAt M w i ≠ none := by
      intro stop
      have existsStop : ∃ n, transAt M w n = none := ⟨i,stop⟩
      exact bad ⟨Nat.find existsStop, fun m hm => Nat.find_min existsStop hm, Nat.find_spec existsStop⟩
    obtain ⟨r,ai,aw,out,br,-,-,-,-⟩ := full_blocks M hs w (t+1) (fun i _ => all i)
    have later : t≤(10*s+1)*(t+1) := by nlinarith
    have dead := transAt_of_le_of_none ht.2 later
    rw [transAt_machine,boundary_label br] at dead
    simp [anchored,drive] at dead
  · rintro ⟨t,ht⟩
    exact ⟨_,(simulates_halt M hs w ht).1⟩

end TapeStorageRates.Native

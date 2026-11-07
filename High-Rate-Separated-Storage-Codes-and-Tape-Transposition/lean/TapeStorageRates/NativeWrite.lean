import TapeStorageRates.NativePhysical

/-! The writeback, return and retarget sweeps of the physical compiler. -/

namespace TapeStorageRates.Native

open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth

/-- After i writes, only the rightmost i cells of each window have been replaced. -/
def written {M : TM} {s : ℕ} (i : ℕ) (aw : Fin M.k → ℤ) (r : Registers M s)
    (mem : Fin M.k → ℤ → Fin (M.g+1)) (j : Fin M.k) (p : ℤ) : Fin (M.g+1) :=
  if 2*(s : ℤ)-i ≤ p-aw j ∧ p-aw j < 2*(s : ℤ) then windowRead (r.wrk j) 0 (p-aw j)
  else mem j p

theorem written_zero {M : TM} {s : ℕ} (aw) (r : Registers M s) (mem) :
    written 0 aw r mem = mem := by
  funext j p
  simp [written]

private theorem at_rev {s : ℕ} {α : Type*} (a : Cells α s) (blank : α) (i : Fin (3*s)) :
    windowRead a blank (2*(s : ℤ)-1-i.val) = a i.rev := by
  have hi := i.isLt
  have hp : -(s : ℤ) ≤ 2*(s : ℤ)-1-i.val ∧ 2*(s : ℤ)-1-i.val < 2*(s : ℤ) := by omega
  unfold windowRead
  rw [dite_eq_left hp]
  congr 1
  apply Fin.ext
  simp only [windowIndex, Fin.rev]
  omega

private theorem written_succ {M : TM} {s : ℕ} (i : Fin (3*s)) (aw) (r : Registers M s) (mem) :
    (fun j p => if p = aw j+(2*(s : ℤ)-1-i.val) then r.wrk j i.rev else
      written i.val aw r mem j p) = written (i.val+1) aw r mem := by
  funext j p
  have hi := i.isLt
  by_cases eq : p=aw j+(2*(s : ℤ)-1-i.val)
  · subst p
    rw [ite_eq_left rfl]
    have h : 2*(s : ℤ)-(i.val+1 : ℕ) ≤ (aw j+(2*(s : ℤ)-1-i.val))-aw j ∧
      (aw j+(2*(s : ℤ)-1-i.val))-aw j < 2*(s : ℤ) := by omega
    rw [written,ite_eq_left h,add_sub_cancel_left]
    exact (at_rev _ _ _).symm
  · rw [ite_eq_right eq]
    unfold written
    split_ifs <;> first | rfl | omega

theorem run_write_from {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (o : Option (Config (machine M hs))) (t : ℕ) (r : Registers M s)
    (ai : ℤ) (aw : Fin M.k → ℤ) (mem : Fin M.k → ℤ → Fin (M.g+1)) (out : List Bool)
    (h : runAt (machine M hs) w o t =
      (anchored (.write ⟨0,by omega⟩) r ai aw (2*↑s-1) mem out).native hs) :
    runAt (machine M hs) w o (t+3*s) =
      (anchored (.home ⟨0,hs⟩) r ai aw (-↑s) (written (3*s) aw r mem) out).native hs := by
  let after : Phase s := .home ⟨0,hs⟩
  let pos := fun i : ℕ => 2*(s : ℤ)-1-min (i : ℤ) (3*(s : ℤ)-1)
  let f := fun i : ℕ => anchored (phaseAt .write after i) r ai aw (pos i)
      (written i aw r mem) out
  have p0 : pos 0 = 2*(s : ℤ)-1 := by dsimp [pos]; omega
  have pe : pos (3*s) = -(s : ℤ) := by dsimp [pos]; omega
  have e := run_frames_from hs w o t (3*s) f (by
    simpa [f,phaseAt,show 0<3*s by omega,p0,written_zero] using h) (by
    intro i hi
    let j : Fin (3*s) := ⟨i,hi⟩
    have hp : phaseAt Phase.write after i = .write j := phaseAt_fin _ _ j
    have pi : pos i = 2*(s : ℤ)-1-i := by dsimp [pos]; omega
    let dir : Dir := if i+1<3*s then .left else .stay
    have pn : pos i+moveInt dir = pos (i+1) := by
      dsimp [pos,dir]; split_ifs <;> simp [moveInt] <;> omega
    change (drive hs (phaseAt .write after i,r) _ _).map _ = some _
    rw [hp]
    change some ((f i).apply (uniform (nextIndex j .write after) r dir
      (fun a => r.wrk a j.rev))) = some (f (i+1))
    apply congrArg some
    apply Frame.ext
    · exact Prod.ext (nextIndex_phaseAt ..) rfl
    · change dir.shift (ai+pos i) = ai+pos (i+1)
      rw [shift_eq_add_moveInt,add_assoc,pn]
    · funext a
      change dir.shift (aw a+pos i) = aw a+pos (i+1)
      rw [shift_eq_add_moveInt,add_assoc,pn]
    · change (fun a p => if p=aw a+pos i then r.wrk a j.rev else written i aw r mem a p) = _
      rw [pi]
      exact written_succ j aw r mem
    · rfl)
  simpa [f,phaseAt,pe,after] using e

theorem run_home_from {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (o : Option (Config (machine M hs))) (t : ℕ) (r : Registers M s)
    (ai : ℤ) (aw : Fin M.k → ℤ) (mem : Fin M.k → ℤ → Fin (M.g+1)) (out : List Bool)
    (h : runAt (machine M hs) w o t =
      (anchored (.home ⟨0,hs⟩) r ai aw (-↑s) mem out).native hs) :
    runAt (machine M hs) w o (t+s) =
      (anchored (.carry ⟨0,hs⟩) r ai aw 0 mem out).native hs := by
  let after : Phase s := .carry ⟨0,hs⟩
  let f := fun i : ℕ => anchored (phaseAt .home after i) r ai aw ((i : ℤ)-s) mem out
  have e := run_frames_from hs w o t s f (by simpa [f,phaseAt,hs] using h) (by
    intro i hi
    have hp : phaseAt Phase.home after i = .home ⟨i,hi⟩ := phaseAt_fin _ _ ⟨i,hi⟩
    change (drive hs (phaseAt .home after i,r) _ _).map _ = some _
    rw [hp]
    change some ((f i).apply (uniform (nextIndex ⟨i,hi⟩ .home after) r .right
      (fun j => mem j (aw j+(↑i-↑s))))) = _
    dsimp only [f]
    rw [anchored_uniform,nextIndex_phaseAt]
    congr 2
    simp [moveInt]
    omega)
  simpa [f,phaseAt,after] using e

theorem run_carry_from {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (o : Option (Config (machine M hs))) (t : ℕ) (r : Registers M s)
    (ai : ℤ) (aw : Fin M.k → ℤ) (mem : Fin M.k → ℤ → Fin (M.g+1)) (out : List Bool)
    (h : runAt (machine M hs) w o t =
      (anchored (.carry ⟨0,hs⟩) r ai aw 0 mem out).native hs) :
    runAt (machine M hs) w o (t+s) = (anchored (.emit ⟨0,hs⟩) r
      (ai+(s : ℤ)*moveInt (direction r.desc.1.1))
      (fun j => aw j+(s : ℤ)*moveInt (direction (r.desc.1.2 j))) 0 mem out).native hs := by
  let after : Phase s := .emit ⟨0,hs⟩
  let f := fun i : ℕ => anchored (phaseAt .carry after i) r
      (ai+(i : ℤ)*moveInt (direction r.desc.1.1))
      (fun j => aw j+(i : ℤ)*moveInt (direction (r.desc.1.2 j))) 0 mem out
  have e := run_frames_from hs w o t s f (by simpa [f,phaseAt,hs] using h) (by
    intro i hi
    have hp : phaseAt Phase.carry after i = .carry ⟨i,hi⟩ := phaseAt_fin _ _ ⟨i,hi⟩
    change (drive hs (phaseAt .carry after i,r) _ _).map _ = some _
    rw [hp]
    apply congrArg some
    apply Frame.ext
    · exact Prod.ext (nextIndex_phaseAt ..) rfl
    · simp [f,anchored,Frame.apply,shift_eq_add_moveInt,add_mul,add_assoc]
    · funext j
      simp [f,anchored,Frame.apply,shift_eq_add_moveInt,add_mul,add_assoc]
    · funext j p
      simp [f,anchored,Frame.apply]
      intro he
      rw [he]
    · rfl)
  simpa [f,phaseAt,after] using e

end TapeStorageRates.Native

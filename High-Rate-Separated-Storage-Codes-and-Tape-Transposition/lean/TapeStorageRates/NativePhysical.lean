import TapeStorageRates.NativeRun
import TapeStorageRates.NativeWarmPath

/-! Concrete configurations for traversing the seven phases of a compiled
batch. The tape coordinates and their updates have precisely the frozen
native semantics; the sole change in representation is naming finite states. -/

namespace TapeStorageRates.Native

open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth

@[ext] structure Frame (M : TM) (s : ℕ) where
  pc : Label M s
  ip : ℤ
  wp : Fin M.k → ℤ
  cells : Fin M.k → ℤ → Fin (M.g+1)
  printed : List Bool

noncomputable def Frame.native {M : TM} {s : ℕ} (hs : 0<s) (f : Frame M s) :
    Config (machine M hs) where
  state := labelEquiv M hs f.pc
  inPos := f.ip
  workPos := f.wp
  work := f.cells
  outRev := f.printed

def Frame.apply {M : TM} {s : ℕ} (f : Frame M s) (z : Instruction M s) : Frame M s where
  pc := z.1
  ip := z.2.1.shift f.ip
  wp := fun j => (z.2.2.1 j).2.shift (f.wp j)
  cells := fun j p => if p=f.wp j then (z.2.2.1 j).1 else f.cells j p
  printed := match z.2.2.2 with | none => f.printed | some b => b::f.printed

def frameStep {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (f : Frame M s) :
    Option (Frame M s) :=
  (drive hs f.pc (readInput w f.ip) (fun j => f.cells j (f.wp j))).map f.apply

theorem Frame.step_native {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (f : Frame M s) :
    step (machine M hs) w (f.native hs) = (frameStep hs w f).map (Frame.native hs) := by
  rw [step_eq_lookup]
  simp only [lookup, Frame.native, frameStep]
  simp only [Equiv.symm_apply_apply]
  cases he : drive hs f.pc (readInput w f.ip) (fun j => f.cells j (f.wp j)) with
  | none => rfl
  | some z => rfl

/-- A list of named physical configurations is an actual interval of native
run whenever its successive frozen transitions agree. -/
theorem run_frames_from {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (o : Option (Config (machine M hs))) (t n : ℕ)
    (f : ℕ → Frame M s) (initial : runAt (machine M hs) w o t = (f 0).native hs)
    (tick : ∀ i<n, frameStep hs w (f i) = some (f (i+1))) :
    runAt (machine M hs) w o (t+n) = (f n).native hs := by
  induction n with
  | zero => simpa using initial
  | succ n ih =>
    rw [← Nat.add_assoc,runAt_succ,next, ih fun i hi => tick _ (by omega),
      Frame.step_native, tick n (by omega)]
    rfl

/-- All physical heads at a common displacement from their respective anchors. -/
def anchored {M : TM} {s : ℕ} (ph : Phase s) (r : Registers M s) (ai : ℤ)
    (aw : Fin M.k → ℤ) (shift : ℤ) (work : Fin M.k → ℤ → Fin (M.g+1))
    (out : List Bool) : Frame M s :=
  ⟨(ph,r),ai+shift,fun j => aw j+shift,work,out⟩

/-- A simultaneous native tick which preserves the scanned symbols advances
all head positions by the requested unit displacement. -/
theorem anchored_uniform {M : TM} {s : ℕ} (ph ph' : Phase s) (r r' : Registers M s)
    (ai : ℤ) (aw : Fin M.k → ℤ) (d : ℤ) (mem : Fin M.k → ℤ → Fin (M.g+1))
    (out : List Bool) (dir : Dir) :
    (anchored ph r ai aw d mem out).apply
      (uniform ph' r' dir (fun j => mem j (aw j+d))) =
    anchored ph' r' ai aw (d+moveInt dir) mem out := by
  ext <;> simp [Frame.apply,anchored,uniform,shift_eq_add_moveInt,add_assoc]
  split_ifs with h <;> simp [h]

private def readPrefix {α : Type*} {n : ℕ} (i : ℕ) (old fresh : Fin n → α) :
    Fin n → α := fun j => if j.val < i then fresh j else old j

private theorem readPrefix_succ {α : Type*} {n : ℕ} (i : Fin n) (old fresh : Fin n → α) :
    Function.update (readPrefix i.val old fresh) i (fresh i) =
      readPrefix (i.val+1) old fresh := by
  funext j
  by_cases he : j=i
  · subst j
    simp [readPrefix]
  · rw [Function.update_of_ne he]
    have hne : j.val ≠ i.val := fun h => he (Fin.ext h)
    unfold readPrefix
    split_ifs <;> first | rfl | omega

private theorem readPrefix_zero {α : Type*} {n : ℕ} (old fresh : Fin n → α) :
    readPrefix 0 old fresh = old := funext fun i => by simp [readPrefix]

private theorem readPrefix_full {α : Type*} {n : ℕ} (old fresh : Fin n → α) :
    readPrefix n old fresh = fresh := funext fun i => by simp [readPrefix,i.isLt]

/-- Contents of the captured registers after i cells of the read sweep. -/
def capturePrefix {M : TM} {s : ℕ} (i : ℕ) (r : Registers M s)
    (input : Cells (Option Bool) s) (work : Fin M.k → Cells (Fin (M.g+1)) s) :
    Registers M s :=
  { r with inp := readPrefix i r.inp input, wrk := fun j => readPrefix i (r.wrk j) (work j) }

theorem capturePrefix_zero {M : TM} {s : ℕ} (r : Registers M s) (I W) :
    capturePrefix 0 r I W = r := by simp [capturePrefix,readPrefix_zero]

theorem capturePrefix_succ {M : TM} {s : ℕ} (i : Fin (3*s)) (r : Registers M s) (I W) :
    acquire (capturePrefix i.val r I W) i (I i) (fun j => W j i) =
      capturePrefix (i.val+1) r I W := by
  simp [acquire,capturePrefix,readPrefix_succ]

theorem capturePrefix_full {M : TM} {s : ℕ} (r : Registers M s) (I W) :
    capturePrefix (3*s) r I W = { r with inp := I, wrk := W } := by
  simp [capturePrefix,readPrefix_full]

theorem run_left_from {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (o : Option (Config (machine M hs))) (t : ℕ) (r : Registers M s)
    (ai : ℤ) (aw : Fin M.k → ℤ) (mem : Fin M.k → ℤ → Fin (M.g+1)) (out : List Bool)
    (h : runAt (machine M hs) w o t =
      (anchored (.left ⟨0,hs⟩) r ai aw 0 mem out).native hs) :
    runAt (machine M hs) w o (t+s) =
      (anchored (.read ⟨0,by omega⟩) r ai aw (-(s : ℤ)) mem out).native hs := by
  let after : Phase s := .read ⟨0,by omega⟩
  let f := fun i : ℕ => anchored (phaseAt .left after i) r ai aw (-(i : ℤ)) mem out
  have e := run_frames_from hs w o t s f (by simpa [f,phaseAt,hs] using h) (by
    intro i hi
    have hp : phaseAt Phase.left after i = .left ⟨i,hi⟩ := phaseAt_fin _ _ ⟨i,hi⟩
    simp only [f,frameStep,anchored, hp, drive, Option.map_some]
    change some ((anchored _ r ai aw (-↑i) mem out).apply
      (uniform (nextIndex ⟨i,hi⟩ .left after) r .left (fun j => mem j (aw j+-↑i)))) = _
    rw [anchored_uniform,nextIndex_phaseAt]
    congr 2
    simp [moveInt]
    omega)
  simpa [f,phaseAt,after] using e

/-- The actual native read sweep loads every bit of the three input blocks and
every symbol of the three work blocks, retaining the physical work tapes. -/
theorem run_read_from {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (o : Option (Config (machine M hs))) (t : ℕ) (r : Registers M s)
    (ai : ℤ) (aw : Fin M.k → ℤ) (mem : Fin M.k → ℤ → Fin (M.g+1)) (out : List Bool)
    (h : runAt (machine M hs) w o t =
      (anchored (.read ⟨0,by omega⟩) r ai aw (-↑s) mem out).native hs) :
    runAt (machine M hs) w o (t+3*s) = (anchored .table
      { r with inp := capture s (readInput w) ai, wrk := fun j => capture s (mem j) (aw j) }
      ai aw (2*↑s-1) mem out).native hs := by
  let I := capture s (readInput w) ai
  let W := fun j => capture s (mem j) (aw j)
  let pos := fun i : ℕ => min (i : ℤ) (3*(s : ℤ)-1)-s
  let f := fun i : ℕ => anchored (phaseAt .read .table i) (capturePrefix i r I W)
      ai aw (pos i) mem out
  have p0 : pos 0 = -↑s := by dsimp [pos]; omega
  have pe : pos (3*s) = 2*↑s-1 := by dsimp [pos]; omega
  have e := run_frames_from hs w o t (3*s) f (by
    simpa [f,phaseAt,show 0<3*s by omega,p0,capturePrefix_zero] using h) (by
    intro i hi
    let j : Fin (3*s) := ⟨i,hi⟩
    have hp : phaseAt Phase.read .table i = .read j := phaseAt_fin _ _ j
    have pi : pos i = (i : ℤ)-s := by dsimp [pos]; omega
    let dir : Dir := if i+1<3*s then .right else .stay
    have pn : pos i+moveInt dir = pos (i+1) := by
      dsimp [pos,dir]; split_ifs <;> simp [moveInt] <;> omega
    have hx : readInput w (ai+pos i) = I j := by simp [I,capture,pi,j]
    have hw : (fun a => mem a (aw a+pos i)) = fun a => W a j := by simp [W,capture,pi,j]
    simp only [f,frameStep,anchored,hp,drive,Option.map_some]
    change some ((anchored _ _ ai aw (pos i) mem out).apply
      (uniform (nextIndex j .read .table)
        (acquire (capturePrefix i r I W) j (readInput w (ai+pos i)) (fun a => mem a (aw a+pos i)))
        dir (fun a => mem a (aw a+pos i)))) = _
    rw [show acquire (capturePrefix i r I W) j (readInput w (ai+pos i)) (fun a => mem a (aw a+pos i)) =
      capturePrefix (i+1) r I W by rw [hx,hw]; exact capturePrefix_succ j r I W]
    rw [anchored_uniform,nextIndex_phaseAt,pn]
    rfl)
  simpa [f,phaseAt,pe,capturePrefix_full,I,W] using e

theorem run_table_from {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (o : Option (Config (machine M hs))) (t : ℕ) (r : Registers M s)
    (ai : ℤ) (aw : Fin M.k → ℤ) (mem : Fin M.k → ℤ → Fin (M.g+1)) (out : List Bool)
    (h : runAt (machine M hs) w o t =
      (anchored .table r ai aw (2*↑s-1) mem out).native hs) :
    runAt (machine M hs) w o (t+1) =
      (anchored (.write ⟨0,by omega⟩) (updateTable hs r) ai aw (2*↑s-1) mem out).native hs := by
  rw [runAt_succ,next,h,Frame.step_native]
  change (Option.map (Frame.native hs)
    (some ((anchored .table r ai aw (2*↑s-1) mem out).apply
      (uniform (.write ⟨0,by omega⟩) (updateTable hs r) .stay
        (fun j => mem j (aw j+(2*↑s-1))))))).getD _ = _
  rw [anchored_uniform]
  simp [moveInt]

end TapeStorageRates.Native

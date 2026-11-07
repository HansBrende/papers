import TapeStorageRates.NativeSchedule
import TapeStorageRates.NativeWindow
import TransposeFollowup.FiniteProgramEncodingCore
import Mathlib.Tactic.DeriveFintype

/-! The compiled transition table in the frozen native model. The physical tapes
and their alphabet are exactly those of the source machine. A finite label
contains both an index into the current sweep and its bounded local data. -/

namespace TapeStorageRates.Native

open Transpose MergeDepth

inductive Phase (s : ℕ) where
  | left (i : Fin s)
  | read (i : Fin (3*s))
  | table
  | write (i : Fin (3*s))
  | home (i : Fin s)
  | carry (i : Fin s)
  | emit (i : Fin s)
  | drain (i : Fin s)
  | done
  deriving DecidableEq, Fintype

set_option synthInstance.maxSize 4096 in
/-- All arrays in the finite control have length at most 3s. -/
structure Registers (M : TM) (s : ℕ) where
  q : Fin (M.q+1)
  oi : Fin s
  ow : Fin M.k → Fin s
  inp : Cells (Option Bool) s
  wrk : Fin M.k → Cells (Fin (M.g+1)) s
  desc : Descriptor M.k
  pendingLen : Fin s
  pending : Fin s → Bool
  toEmit : Fin s → Bool
  stopped : Bool
  deriving Fintype

abbrev Label (M : TM) (s : ℕ) := Phase s × Registers M s

def offsetWord {s : ℕ} (n : Fin s) (bits : Fin s → Bool) : List Bool :=
  List.ofFn fun i : Fin n.val => bits ⟨i.val, i.isLt.trans n.isLt⟩

def cellsOfWord (s : ℕ) (xs : List Bool) : Fin s → Bool :=
  fun i => xs[i.val]?.getD false

def carryIndex (s : ℕ) (p : ℤ) : Fin 3 := if p < 0 then 0 else if p < s then 1 else 2

def finalOffset {s : ℕ} (p : ℤ) (hp : Fits s 0 p) : Fin s :=
  ⟨(if p < 0 then p+s else if p < s then p else p-s).toNat, by
    unfold Fits at hp
    split_ifs <;> omega⟩

theorem carry_offset {s : ℕ} (p : ℤ) (hp : Fits s 0 p) :
    (s : ℤ)*moveInt (direction (carryIndex s p)) + (finalOffset p hp).val = p := by
  unfold Fits at hp
  unfold carryIndex finalOffset
  split_ifs <;> norm_num [direction, moveInt] <;> omega

def initialRegs (M : TM) {s : ℕ} (hs : 0 < s) : Registers M s where
  q := 0
  oi := ⟨0,hs⟩
  ow := fun _ => ⟨0,hs⟩
  inp := fun _ => none
  wrk := fun _ _ => 0
  desc := ((1, fun _ => 1), false)
  pendingLen := ⟨0,hs⟩
  pending := fun _ => false
  toEmit := fun _ => false
  stopped := false

def initialLabel (M : TM) {s : ℕ} (hs : 0 < s) : Label M s :=
  (.left ⟨0,hs⟩, initialRegs M hs)

def acquire {M : TM} {s : ℕ} (r : Registers M s) (i : Fin (3*s))
    (inp : Option Bool) (work : Fin M.k → Fin (M.g+1)) : Registers M s :=
  { r with inp := Function.update r.inp i inp,
           wrk := fun j => Function.update (r.wrk j) i (work j) }

/-- The stationary tick computes the whole local source evolution and schedules
at most one complete s-bit output word. -/
def updateTable {M : TM} {s : ℕ} (hs : 0 < s) (r : Registers M s) : Registers M s :=
  let c := localConfig M s r.q r.oi r.ow r.wrk
  let result := advance M (windowRead r.inp none) s c
  let h := advance_fits (I := windowRead r.inp none)
    (localConfig_fits r.q r.oi r.ow r.wrk)
  let bits := offsetWord r.pendingLen r.pending ++ result.1.outRev.reverse
  let full := decide (s ≤ bits.length)
  let rest := if full then bits.drop s else bits
  { q := result.1.state
    oi := finalOffset result.1.inPos h.1
    ow := fun j => finalOffset (result.1.workPos j) (h.2 j)
    inp := r.inp
    wrk := fun j => capture s (result.1.work j) 0
    desc := ((carryIndex s result.1.inPos, fun j => carryIndex s (result.1.workPos j)), full)
    pendingLen := ⟨bits.length % s, Nat.mod_lt _ hs⟩
    pending := cellsOfWord s rest
    toEmit := cellsOfWord s bits
    stopped := result.2 }

def nextIndex {n : ℕ} {α : Type*} (i : Fin n) (inside : Fin n → α) (after : α) : α :=
  if h : i.val+1<n then inside ⟨i.val+1,h⟩ else after

abbrev Instruction (M : TM) (s : ℕ) :=
  Label M s × Dir × (Fin M.k → Fin (M.g+1) × Dir) × Option Bool

def uniform {M : TM} {s : ℕ} (ph : Phase s) (r : Registers M s)
    (move : Dir) (work : Fin M.k → Fin (M.g+1)) (out : Option Bool := none) :
    Instruction M s := ((ph,r), move, fun j => (work j, move), out)

/-- A single genuine native transition, before encoding its finite label. -/
def drive {M : TM} {s : ℕ} (hs : 0 < s) (label : Label M s)
    (inp : Option Bool) (work : Fin M.k → Fin (M.g+1)) : Option (Instruction M s) :=
  let z : Fin s := ⟨0,hs⟩
  let z3 : Fin (3*s) := ⟨0,by omega⟩
  let r := label.2
  match label.1 with
  | .left i => some (uniform (nextIndex i .left (.read z3)) r .left work)
  | .read i => some (uniform (nextIndex i .read .table) (acquire r i inp work)
      (if i.val+1<3*s then .right else .stay) work)
  | .table => some (uniform (.write z3) (updateTable hs r) .stay work)
  | .write i => some (uniform (nextIndex i .write (.home z)) r
      (if i.val+1<3*s then .left else .stay) (fun j => r.wrk j i.rev))
  | .home i => some (uniform (nextIndex i .home (.carry z)) r .right work)
  | .carry i => some ((nextIndex i .carry (.emit z),r), direction r.desc.1.1,
      fun j => (work j, direction (r.desc.1.2 j)), none)
  | .emit i => some (uniform (nextIndex i .emit (if r.stopped then .drain z else .left z))
      r .stay work (if r.desc.2 then some (r.toEmit i) else none))
  | .drain i => some (uniform (nextIndex i .drain .done) r .stay work
      (if i.val<r.pendingLen.val then some (r.pending i) else none))
  | .done => none

noncomputable def labelEquiv (M : TM) {s : ℕ} (hs : 0<s) :
    Label M s ≃ Fin (Fintype.card (Label M s)-1+1) :=
  (TransposeFollowup.NativeMicrocode.initialEncoding (T := Fin M.k) (initialLabel M hs)).label

@[simp] theorem labelEquiv_initial (M : TM) {s : ℕ} (hs : 0<s) :
    labelEquiv M hs (initialLabel M hs) = 0 :=
  TransposeFollowup.NativeMicrocode.initialEncoding_start _

/-- The compiled finite table, with the Paper 1 tape count and alphabet. -/
noncomputable abbrev machine (M : TM) {s : ℕ} (hs : 0<s) : TM where
  k := M.k
  g := M.g
  q := Fintype.card (Label M s)-1
  δ := fun q x a => (drive hs ((labelEquiv M hs).symm q) x a).map fun z =>
    (labelEquiv M hs z.1, z.2)

@[simp] theorem machine_tapes (M : TM) {s : ℕ} (hs : 0<s) :
    (machine M hs).k = M.k := rfl

@[simp] theorem machine_alphabet (M : TM) {s : ℕ} (hs : 0<s) :
    (machine M hs).g = M.g := rfl

theorem machine_transition (M : TM) {s : ℕ} (hs : 0<s) (q : Label M s)
    (inp : Option Bool) (work : Fin M.k → Fin (M.g+1)) :
    (machine M hs).δ (labelEquiv M hs q) inp work =
      (drive hs q inp work).map (fun z => (labelEquiv M hs z.1,z.2)) := by
  simp [machine]

end TapeStorageRates.Native

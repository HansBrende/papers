import TapeStorageRates.PacketCompilerTable

/-! # Whole step records on the concrete packet schedule -/

namespace TapeStorageRates.PacketCompiler

open Transpose Transpose.Tape MergeDepth

set_option autoImplicit false

/-- At the end of acquisition slot `i` exactly the first `i` cells have arrived. -/
def collect {α : Type*} (blank : α) (f : Fin 3 → α) (i : ℕ) (j : Fin 3) : α :=
  if j.val < i then f j else blank

theorem collect_zero {α : Type*} (blank : α) (f : Fin 3 → α) : collect blank f 0 = fun _ => blank := by
  funext; simp [collect]

theorem collect_three {α : Type*} (blank : α) (f : Fin 3 → α) : collect blank f 3 = f := by
  funext i; simp [collect, i.isLt]

theorem collect_succ_eq {α : Type*} {blank : α} {f g : Fin 3 → α} (j : Fin 3)
    (h : collect blank f j.val = collect blank g j.val) (hi : f j = g j) :
    collect blank f (j.val+1) = collect blank g (j.val+1) := by
  funext i
  by_cases h₀ : i.val < j.val
  · simpa [collect, h₀, show i.val < j.val+1 by omega] using congrFun h i
  · by_cases h₁ : i.val = j.val
    · have he : i=j := Fin.ext h₁
      subst i; simpa [collect] using hi
    · simp [collect, show ¬i.val < j.val+1 by omega]

@[ext] structure Scratch (M : TM) (s r : ℕ) where
  boundary : Boundary M s r
  input : Fin 3 → InputWord s r
  work : Fin 3 → Fin M.k → WorkWord M s
  output : Option (Fin s → Bool)

noncomputable def scratch {s r : ℕ} (L : CellLayout s r) (hs : 0<s) (M : TM) (w : List Bool)
    (b i : ℕ) : Scratch M s r :=
  if i < 4 then
    ⟨boundary L hs M w b, collect (fun _ => none) (inputAt L hs M w b) i,
      collect (fun _ _ => 0) (beforeAt L hs M w b) i, none⟩
  else
    ⟨boundary L hs M w (b+1), fun _ _ => none, afterAt L hs M w b, emitted L hs M w b⟩

noncomputable def record {s r : ℕ} (L : CellLayout s r) (hs : 0<s) (M : TM) (w : List Bool)
    (t : ℕ) : StepRecord M s r :=
  let v := scratch L hs M w (t/11) (t%11)
  ⟨v.boundary, v.input, v.work, fun j => memory hs w (t+1) j (batchWalks L hs M w (some (some j)) t), v.output⟩

def StepRecord.scratch {M : TM} {s r : ℕ} (v : StepRecord M s r) : Scratch M s r :=
  ⟨v.boundary, v.inputCells, v.workCells, v.output⟩

theorem record_scratch_slot {s r : ℕ} (L : CellLayout s r) (hs : 0<s) (M : TM) (w : List Bool)
    (b i : ℕ) (hi : i<11) :
    (record L hs M w (11*b+i)).scratch = scratch L hs M w b i := by
  simp only [record, show (11*b+i)/11=b by omega, show (11*b+i)%11=i by omega, StepRecord.scratch]

theorem record_emit_slot {s r : ℕ} (L : CellLayout s r) (hs : 0<s) (M : TM) (w : List Bool) (b : ℕ) :
    (record L hs M w (11*b+10)).output = emitted L hs M w b := by
  change (record L hs M w (11*b+10)).scratch.output = _
  rw [record_scratch_slot _ _ _ _ _ _ (by decide)]; rfl

theorem scratch_read {s r : ℕ} (L : CellLayout s r) (hs : 0<s) (M : TM) {w v : List Bool}
    (b : ℕ) (i : Fin 3) (hprev : scratch L hs M w b i.val = scratch L hs M v b i.val)
    (hI : inputAt L hs M w b i = inputAt L hs M v b i)
    (hW : beforeAt L hs M w b i = beforeAt L hs M v b i) :
    scratch L hs M w b (i.val+1) = scratch L hs M v b (i.val+1) := by
  have h₁ : i.val < 4 := by have := i.isLt; omega
  have h₂ : i.val + 1 < 4 := by have := i.isLt; omega
  simp only [scratch, ite_eq_left h₁, ite_eq_left h₂, Scratch.mk.injEq, and_true] at hprev ⊢
  exact ⟨hprev.1, collect_succ_eq i hprev.2.1 hI, collect_succ_eq i hprev.2.2 hW⟩

theorem scratch_lookup {s r : ℕ} (L : CellLayout s r) (hs : 0<s) (M : TM) {w v : List Bool}
    (b : ℕ) (h₀ : centres L hs M w b = centres L hs M v b)
    (h₁ : centres L hs M w (b+1) = centres L hs M v (b+1))
    (hprev : scratch L hs M w b 3 = scratch L hs M v b 3) :
    scratch L hs M w b 4 = scratch L hs M v b 4 := by
  simp only [scratch, ite_eq_left (by decide : 3<4), collect_three, Scratch.mk.injEq, and_true] at hprev
  obtain ⟨hb,hwork,hout⟩ := table_fields L hs b h₀ h₁ hprev.1 hprev.2.1 hprev.2.2
  simp [scratch, hb, hwork, hout]

/-- Physically scanned addresses of the three read slots. -/
theorem read_address {k : ℕ} (c : ℕ → Centres k) (b : ℕ) (i : Fin 3) (f : Centres k → ℤ) :
    sweep (fun j => f (c j)) (11*b+(i.val+1)) = neighbour (f (c b)) i := by
  rw [sweep_slot _ _ _ (by have := i.isLt; omega)]
  fin_cases i <;> simp [phaseAddress, neighbour]
  omega

theorem read_work {s r : ℕ} (L : CellLayout s r) (hs : 0<s) (M : TM) (w : List Bool)
    (b : ℕ) (i : Fin 3) (j : Fin M.k) :
    memory hs w (11*b+(i.val+1)) j (batchWalks L hs M w (some (some j)) (11*b+(i.val+1))) =
      beforeAt L hs M w b i j := by
  rw [memory_slot _ _ _ _ (by have := i.isLt; omega)]
  change mixed _ _ _ (sweep (fun b => (centres L hs M w b).work j) _) _ = _
  rw [read_address (centres L hs M w) b i (fun C => C.work j)]
  fin_cases i <;> rfl

/-- The write slot commits right, centre, or left. At every other slot the recorded word is the
currently scanned one. -/
def writeLane : ℕ → Option (Fin 3)
  | 5 => some 2
  | 6 => some 1
  | 7 => some 0
  | _ => none

theorem record_write_slot {s r : ℕ} (L : CellLayout s r) (hs : 0<s) (M : TM) (w : List Bool)
    (b i : ℕ) (hi : i<11) (j : Fin M.k) :
    (record L hs M w (11*b+i)).written j =
      match writeLane i with
      | some u => afterAt L hs M w b u j
      | none => memory hs w (11*b+i) j (batchWalks L hs M w (some (some j)) (11*b+i)) := by
  change memory hs w (11*b+i+1) j (sweep (fun b => (centres L hs M w b).work j) (11*b+i)) = _
  change _ = match writeLane i with
    | some u => afterAt L hs M w b u j
    | none => memory hs w (11*b+i) j (sweep (fun b => (centres L hs M w b).work j) (11*b+i))
  rw [sweep_slot _ b i hi]
  by_cases h : i+1=11
  · rw [show i=10 by omega, show 11*b+10+1=11*(b+1)+0 by omega, memory_slot _ _ (b+1) 0 (by decide)]
    simp only [writeLane, memory_slot _ _ b 10 (by decide)]; rfl
  · rw [Nat.add_assoc, memory_slot _ _ b (i+1) (by omega)]
    interval_cases i <;> simp_all [writeLane, memory_slot, mixed, phaseAddress, afterAt, neighbour, centres, add_sub_assoc]
    exact (memory_slot hs w b 0 (by decide) j _).symm

end TapeStorageRates.PacketCompiler

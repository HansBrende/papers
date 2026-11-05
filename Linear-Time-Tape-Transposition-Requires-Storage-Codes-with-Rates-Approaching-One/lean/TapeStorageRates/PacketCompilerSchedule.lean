import TapeStorageRates.PacketCompilerCells
import TapeStorageRates.NativeSchedule
import TapeStorageRates.PacketOutput

/-! # Eleven packet ticks for each batch of an actual native run -/

namespace TapeStorageRates.PacketCompiler

open Transpose Transpose.Tape Transpose.Tape.Impl BoundedNesting MergeDepth

set_option autoImplicit false

/-- Coarse positions of all tape heads at one batch boundary. -/
@[ext] structure Centres (k : ℕ) where
  input : ℤ
  work : Fin k → ℤ
  output : ℤ

/-- Public layout functions turn the real head positions and output length into packet addresses. -/
noncomputable def centres {s r : ℕ} (L : CellLayout s r) (hs : 0 < s) (M : TM) (w : List Bool)
    (j : ℕ) : Centres M.k :=
  let c := run M w (j*s)
  ⟨L.cell hs c.inPos, fun h => (workLayout s).cell hs (c.workPos h), L.cell hs c.outRev.length⟩

theorem centres_zero {s r : ℕ} (L : CellLayout s r) (hs : 0 < s) (M : TM) (w : List Bool) :
    centres L hs M w 0 = ⟨0, fun _ => 0, 0⟩ := by
  ext h <;> simp [centres, run, init, L.cell_zero hs, (workLayout s).cell_zero hs]

theorem centres_input_walk {s r : ℕ} (L : CellLayout s r) (hs : 0 < s) (M : TM) (w : List Bool) :
    IsWalk (fun j => (centres L hs M w j).input) := by
  change IsWalk (fun j => L.cell hs (run M w (j*s)).inPos)
  refine L.sampled_walk hs (w := fun t => (run M w t).inPos) ?_
  intro t
  change |(run M w (t+1)).inPos - (run M w t).inPos| ≤ 1
  rw [inPos_eq_input, inPos_eq_input]
  exact (trace M w).abs_input_succ_sub_le t

theorem centres_work_walk {s r : ℕ} (L : CellLayout s r) (hs : 0 < s) (M : TM) (w : List Bool)
    (h : Fin M.k) : IsWalk (fun j => (centres L hs M w j).work h) := by
  change IsWalk (fun j => (workLayout s).cell hs ((run M w (j*s)).workPos h))
  refine (workLayout s).sampled_walk hs (w := fun t => (run M w t).workPos h) ?_
  intro t
  change |(run M w (t+1)).workPos h - (run M w t).workPos h| ≤ 1
  rw [workPos_eq_work, workPos_eq_work]
  exact (trace M w).work_isWalk h t

theorem centres_output_step {s r : ℕ} (L : CellLayout s r) (hs : 0 < s) (M : TM) (w : List Bool)
    (j : ℕ) : (centres L hs M w (j+1)).output = (centres L hs M w j).output ∨
      (centres L hs M w (j+1)).output = (centres L hs M w j).output + 1 := by
  obtain ⟨u, hu, he⟩ := native_output_append M w (j*s) s
  have hstep := congrArg List.length he
  simp only [List.length_reverse, List.length_append] at hstep
  have hle : (((run M w (j*s)).outRev.length : ℕ) : ℤ) ≤ (run M w (j*s+s)).outRev.length := by omega
  have hdiff : |((run M w (j*s+s)).outRev.length : ℤ) - (run M w (j*s)).outRev.length| ≤ s :=
    abs_le.2 ⟨by omega, by omega⟩
  have hmono := L.cell_mono hs hle
  have hnear := abs_le.1 (L.near_cell hs hdiff)
  simp only [centres, Nat.add_mul, one_mul]; omega

def carry (p q : ℤ) : Fin 3 := if q < p then 0 else if q = p then 1 else 2

theorem next_of_carry {p q : ℤ} (h : |q-p| ≤ 1) :
    q = p + moveInt (Native.direction (carry p q)) := by
  have H := abs_le.1 h
  unfold carry
  split_ifs <;> norm_num [Native.direction, moveInt] <;> omega

/-- The complete varying information in a padded eleven-tick batch. -/
def descriptor {k : ℕ} (u v : Centres k) : Native.Descriptor k :=
  ((carry u.input v.input, fun j => carry (u.work j) (v.work j)), decide (u.output < v.output))

def applyDescriptor {k : ℕ} (u : Centres k) (a : Native.Descriptor k) : Centres k :=
  ⟨u.input + moveInt (Native.direction a.1.1), fun j => u.work j + moveInt (Native.direction (a.1.2 j)),
    u.output + (if a.2 then 1 else 0)⟩

theorem centres_succ {s r : ℕ} (L : CellLayout s r) (hs : 0 < s) (M : TM) (w : List Bool)
    (j : ℕ) :
    let u := centres L hs M w j
    let v := centres L hs M w (j+1)
    v = applyDescriptor u (descriptor u v) := by
  ext h
  · exact next_of_carry (centres_input_walk L hs M w j)
  · exact next_of_carry (centres_work_walk L hs M w h j)
  · rcases centres_output_step L hs M w j with he | he <;> simp [applyDescriptor, descriptor, he]

/-- Exactly `R` descriptors determine every visited head position and output counter throughout
the common padded horizon. -/
theorem centres_agree {s r R : ℕ} {L : CellLayout s r} {hs : 0 < s} {M : TM} {w v : List Bool}
    (h : ∀ j < R, descriptor (centres L hs M w j) (centres L hs M w (j+1)) =
      descriptor (centres L hs M v j) (centres L hs M v (j+1))) :
    ∀ j ≤ R, centres L hs M w j = centres L hs M v j := by
  intro j hj
  induction j with
  | zero => rw [centres_zero, centres_zero]
  | succ j ih =>
    have hj' : j < R := by omega
    exact (centres_succ L hs M w j).trans ((congrArg₂ applyDescriptor (ih hj'.le) (h j hj')).trans
      (centres_succ L hs M v j).symm)

def phaseAddress (p q : ℤ) : ℕ → ℤ
  | 1 | 7 | 8 => p - 1
  | 3 | 4 | 5 => p + 1
  | 10 => q
  | _ => p

/-- Read left/centre/right, evaluate, write right/centre/left, return, retarget and append. -/
def sweep (c : ℕ → ℤ) (t : ℕ) : ℤ := phaseAddress (c (t/11)) (c (t/11+1)) (t%11)

theorem sweep_slot (c : ℕ → ℤ) (b i : ℕ) (hi : i < 11) :
    sweep c (11*b+i) = phaseAddress (c b) (c (b+1)) i := by
  unfold sweep
  rw [show (11*b+i)/11 = b by omega, show (11*b+i)%11 = i by omega]

theorem sweep_isWalk {c : ℕ → ℤ} (hc : IsWalk c) : IsWalk (sweep c) := by
  intro t
  let b := t / 11
  let i := t % 11
  have hi : i < 11 := Nat.mod_lt _ (by decide)
  have ht : 11*b+i=t := Nat.div_add_mod t 11
  rw [← ht, sweep_slot c b i hi]
  by_cases h : i+1=11
  · have H : 11*b+i+1=11*(b+1)+0 := by omega
    rw [H, sweep_slot c (b+1) 0 (by decide), show i=10 by omega]
    simp [phaseAddress]
  · rw [Nat.add_assoc, sweep_slot c b (i+1) (by omega)]
    have hbase := abs_le.1 (hc b)
    interval_cases i <;> simp [phaseAddress, hc b]
    omega

/-- All `k+2` concrete packet walks of a padded native run. -/
noncomputable def batchWalks {s r : ℕ} (L : CellLayout s r) (hs : 0 < s) (M : TM) (w : List Bool) :
    Tp M.k → ℕ → ℤ
  | none => sweep (fun j => (centres L hs M w j).input)
  | some none => fun t => (centres L hs M w (t/11)).output
  | some (some h) => sweep (fun j => (centres L hs M w j).work h)

theorem unit_batchWalks {s r : ℕ} (L : CellLayout s r) (hs : 0 < s) (M : TM) (w : List Bool) :
    ∀ i, IsWalk (batchWalks L hs M w i)
  | none => sweep_isWalk (c := fun j => (centres L hs M w j).input) (centres_input_walk L hs M w)
  | some (some j) => sweep_isWalk (c := fun b => (centres L hs M w b).work j) (centres_work_walk L hs M w j)
  | some none => fun t => by
    change |(centres L hs M w ((t+1)/11)).output - (centres L hs M w (t/11)).output| ≤ 1
    by_cases h : (t+1)/11=t/11
    · simp [h]
    · rw [show (t+1)/11=t/11+1 by omega]
      rcases centres_output_step L hs M w (t/11) with he | he <;> simp [he]

end TapeStorageRates.PacketCompiler

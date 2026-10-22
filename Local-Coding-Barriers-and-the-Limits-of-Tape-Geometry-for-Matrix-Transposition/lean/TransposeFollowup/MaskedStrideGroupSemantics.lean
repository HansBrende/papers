import TransposeFollowup.MaskedStrideGroup

/-! Exact absolute-cell semantics of the paid group executor. Earlier writes
cannot change a later slot's two operands. Padding and physical rewind write
no cells, so the last partial group preserves the unused suffix. -/
namespace TransposeFollowup.MaskedStrideGroup
open Classical FixedTapeCompiler
open CopyMachine (Sym)
open ScheduledNativeIO
open MaskedStrideCell (Mode State bit)
set_option autoImplicit false

abbrev cells (c : State) (t : Fin 2) (z : ℤ) : Sym Bool :=
  AbsoluteTape.cells (c.work.core.tapes t) (c.work.pos t) z

theorem moveBuffer_cells (d : Microcode.Move) (w : List Bool) (c : State) (t : Fin 2) (z : ℤ) :
    cells (NativeIO.step (moveBuffer d) w c) t z=cells c t z := by
  have h := NativeMicrocode.action_cells
    (⟨none,if t=1 then d else .stay⟩ : Microcode.Action) (c.work.core.tapes t) (c.work.pos t) z
  apply h.trans
  change (if z=c.work.pos t then (c.work.core.tapes t).head else cells c t z)=cells c t z
  split_ifs with hz
  · subst z
    exact (AbsoluteTape.scanned _ _).symm
  · rfl

theorem rewind_cells (w : List Bool) (c : State) (n : ℕ) (t : Fin 2) (z : ℤ) :
    cells (trajectory (fun _ => moveBuffer .left) w c n) t z=cells c t z := by
  induction n with
  | zero => rfl
  | succ n ih => exact (moveBuffer_cells .left w _ t z).trans ih

theorem slots_position_of_le (isPrefix : Bool) (mask : ℕ → Bool) (g : ℕ)
    (w : List Bool) (c : State) {n : ℕ} (hn : n ≤ g) (t : Fin 2) :
    (slots isPrefix mask g w c n).work.pos t=c.work.pos t+n := by
  have h := slots_positions isPrefix mask g w c n
  fin_cases t
  · simpa [Nat.min_eq_left hn] using h.1
  · exact h.2

theorem slots_outside (isPrefix : Bool) (mask : ℕ → Bool) (g : ℕ)
    (w : List Bool) (c : State) (n : ℕ) (t : Fin 2) (z : ℤ)
    (hz : z < c.work.pos t ∨ c.work.pos t+(min n g : ℕ) ≤ z) :
    cells (slots isPrefix mask g w c n) t z=cells c t z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hn : n < g
    · have hm : min (n+1) g=n+1 := Nat.min_eq_left (by omega)
      rw [hm] at hz
      rw [slots,ite_eq_left hn]
      change AbsoluteTape.cells _ _ _ = _
      have hne : z≠(slots isPrefix mask g w c n).work.pos t := by
        rw [slots_position_of_le isPrefix mask g w c hn.le t]
        omega
      rw [MaskedStrideCell.result_cells,ite_eq_right hne]
      apply ih
      rw [Nat.min_eq_left hn.le]
      omega
    · have hm : min (n+1) g=min n g := by omega
      rw [slots,ite_eq_right hn]
      exact (moveBuffer_cells .right w _ t z).trans (ih (by simpa only [hm] using hz))

theorem readMode_slots (isPrefix : Bool) (mask : ℕ → Bool) (g : ℕ)
    (w : List Bool) (c : State) {n : ℕ} (hn : n ≤ g) :
    MaskedStrideCell.readMode (slots isPrefix mask g w c n)=
      (bit (cells c 0 (c.work.pos 0+n)),bit (cells c 1 (c.work.pos 1+n))) := by
  have hread (t : Fin 2) : bit ((slots isPrefix mask g w c n).work.core.tapes t).head=
      bit (cells c t (c.work.pos t+n)) := by
    rw [← AbsoluteTape.scanned _ ((slots isPrefix mask g w c n).work.pos t)]
    change bit (cells (slots isPrefix mask g w c n) t ((slots isPrefix mask g w c n).work.pos t))=_
    rw [slots_position_of_le isPrefix mask g w c hn t,
      slots_outside isPrefix mask g w c n t (c.work.pos t+n)
        (Or.inr (by rw [Nat.min_eq_left hn]))]
  exact Prod.ext (hread 0) (hread 1)

def written (isPrefix : Bool) (mask : ℕ → Bool) (c : State) (j : ℕ) (t : Fin 2) : Bool :=
  let x := bit (cells c 0 (c.work.pos 0+j))
  let prev := bit (cells c 1 (c.work.pos 1+j))
  if t=0 then MaskedStrideCell.output (mask j) x prev else MaskedStrideCell.stored isPrefix (mask j) x prev

theorem slots_written (isPrefix : Bool) (mask : ℕ → Bool) (g : ℕ)
    (w : List Bool) (c : State) (n : ℕ) (t : Fin 2) (j : ℕ) (hj : j < min n g) :
    cells (slots isPrefix mask g w c n) t (c.work.pos t+j)=.data (written isPrefix mask c j t) := by
  induction n with
  | zero => simp at hj
  | succ n ih =>
    by_cases hn : n < g
    · rw [slots,ite_eq_left hn]
      change AbsoluteTape.cells _ _ _ = _
      rw [MaskedStrideCell.result_cells]
      by_cases hjn : j=n
      · subst j
        rw [ite_eq_left (slots_position_of_le isPrefix mask g w c hn.le t).symm,
          readMode_slots isPrefix mask g w c hn.le]
        rfl
      · have hne : c.work.pos t+(j : ℕ)≠(slots isPrefix mask g w c n).work.pos t := by
          rw [slots_position_of_le isPrefix mask g w c hn.le t]
          omega
        rw [ite_eq_right hne]
        exact ih (by omega)
    · rw [slots,ite_eq_right hn]
      exact (moveBuffer_cells .right w _ t _).trans (ih (by omega))

theorem result_written (isPrefix : Bool) (mask : ℕ → Bool) {S g : ℕ} (hg : g ≤ S)
    (w : List Bool) (c : State) (t : Fin 2) (j : ℕ) (hj : j < g) :
    cells (result isPrefix mask S g w c) t (c.work.pos t+j)=.data (written isPrefix mask c j t) := by
  rw [result,rewind_cells]
  exact slots_written isPrefix mask g w c S t j (by simpa only [Nat.min_eq_right hg] using hj)

theorem result_outside (isPrefix : Bool) (mask : ℕ → Bool) {S g : ℕ} (hg : g ≤ S)
    (w : List Bool) (c : State) (t : Fin 2) (z : ℤ)
    (hz : z < c.work.pos t ∨ c.work.pos t+g ≤ z) :
    cells (result isPrefix mask S g w c) t z=cells c t z := by
  rw [result,rewind_cells]
  exact slots_outside isPrefix mask g w c S t z (by simpa only [Nat.min_eq_right hg] using hz)

end TransposeFollowup.MaskedStrideGroup

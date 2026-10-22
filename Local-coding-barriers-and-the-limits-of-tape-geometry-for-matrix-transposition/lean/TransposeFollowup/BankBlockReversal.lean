import TransposeFollowup.BlockReverseTransfer

/-! Exact-symbol block reversal on two work tapes. All work is charged:
seek, reversed block transfer, scratch rewind, copy-and-clear, and head
restoration take exactly ten times the bank length. The codec may store
symbols in any finite controller with a left inverse. -/
namespace TransposeFollowup.BankBlockReversal
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open CopyMachine (Sym)
set_option autoImplicit false
variable {M : Type*}
variable (read : Sym Bool → M) (write : M → Sym Bool) (reset : M)

def prepared (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) : NativeIO.Config (Fin 2) M :=
  rewind 1 w (BlockReverseTransfer.run read write reset B n w (advance 0 w c (n*B))) (n*B)

def returned (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) : NativeIO.Config (Fin 2) M :=
  ScheduledTransfer.copied true true false read write reset (prepared read write reset B n w c) (n*B)

def result (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) : NativeIO.Config (Fin 2) M :=
  rewind 1 w (rewind 0 w (returned read write reset B n w c) (n*B)) (n*B)

def ticks (B n : ℕ) : ℕ := n*B+(n*(4*B)+(n*B+(2*(n*B)+(n*B+n*B))))

theorem ticks_eq (B n : ℕ) : ticks B n=10*(n*B) := by unfold ticks; ring

def schedule (B n : ℕ) : ℕ → NativeIO.Program (Fin 2) M :=
  append (fun _ => action 0 ⟨none,.right⟩)
    (append (BlockReverseTransfer.schedule read write reset B n)
      (append (fun _ => action 1 ⟨none,.left⟩)
        (append (ScheduledTransfer.schedule true true false read write reset)
          (append (fun _ => action 0 ⟨none,.left⟩) (fun _ => action 1 ⟨none,.left⟩) (n*B))
          (2*(n*B))) (n*B)) (n*(4*B))) (n*B)

theorem schedule_exact (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    trajectory (schedule read write reset B n) w c (ticks B n)=result read write reset B n w c := by
  simp only [schedule,ticks,append_exact,BlockReverseTransfer.schedule_exact,ScheduledTransfer.schedule_exact]
  rfl

theorem schedule_active (B n i : ℕ) (c : NativeIO.Config (Fin 2) M) :
    NativeIO.Active (schedule read write reset B n i) c := by
  unfold schedule
  apply append_active
  · intro _; exact active _ _ _
  · intro _
    apply append_active
    · intro _; exact BlockReverseTransfer.schedule_active _ _ _ _ _ _ _
    · intro _
      apply append_active
      · intro _; exact active _ _ _
      · intro _
        apply append_active
        · intro _; exact ScheduledTransfer.schedule_active _ _ _ _ _ _ _ _
        · intro _
          apply append_active <;> intro _ <;> exact active _ _ _

theorem prepared_positions (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (t : Fin 2) :
    (prepared read write reset B n w c).work.pos t=c.work.pos t := by
  have h := BlockReverseTransfer.positions read write reset B n w (advance 0 w c (n*B))
  fin_cases t <;> simp [prepared,rewind_position,h.1,h.2,advance_position]

theorem prepared_source (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (z : ℤ) :
    cells (prepared read write reset B n w c) 0 z=cells c 0 z := by
  rw [prepared,rewind_cells,BlockReverseTransfer.source_preserved,advance_cells]

theorem prepared_outside (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (z : ℤ)
    (hz : z<c.work.pos 1 ∨ c.work.pos 1+n*B≤z) :
    cells (prepared read write reset B n w c) 1 z=cells c 1 z := by
  rw [prepared,rewind_cells,BlockReverseTransfer.target_outside,advance_cells]
  simpa [advance_position] using hz

theorem prepared_blocks (hinv : Function.LeftInverse write read) (B n : ℕ) (w : List Bool)
    (c : NativeIO.Config (Fin 2) M) (k j : ℕ) (hk : k<n) (hj : j<B) :
    cells (prepared read write reset B n w c) 1 (c.work.pos 1+k*B+j)=
      cells c 0 (c.work.pos 0+(n-1-k : ℕ)*B+j) := by
  have h := BlockReverseTransfer.target_blocks read write reset hinv B n w (advance 0 w c (n*B)) k j hk hj
  simp only [advance_cells] at h
  simp [advance_position] at h
  rw [prepared,rewind_cells,h]
  congr 2
  have he : ((n-1-k : ℕ) : ℤ)=(n : ℤ)-1-k := by omega
  rw [he]
  ring

theorem prepared_io (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    (prepared read write reset B n w c).inputPos=c.inputPos ∧
    (prepared read write reset B n w c).outRev=c.outRev := by
  have h₀ := advance_io 0 w c (n*B)
  have h₁ := BlockReverseTransfer.io read write reset B n w (advance 0 w c (n*B))
  have h₂ := rewind_io 1 w (BlockReverseTransfer.run read write reset B n w (advance 0 w c (n*B))) (n*B)
  exact ⟨h₂.1.trans (h₁.1.trans h₀.1),h₂.2.trans (h₁.2.trans h₀.2)⟩

theorem result_cells (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (t : Fin 2) (z : ℤ) :
    cells (result read write reset B n w c) t z=cells (returned read write reset B n w c) t z := by
  simp only [result,rewind_cells]

theorem result_positions (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (t : Fin 2) :
    (result read write reset B n w c).work.pos t=c.work.pos t := by
  have h := ScheduledTransfer.copied_positions true true false read write reset (prepared read write reset B n w c) (n*B)
  simp only [ScheduledTransfer.source,ScheduledTransfer.target,ScheduledTransfer.offset,
    Bool.false_eq_true,ite_false,ite_true,prepared_positions] at h
  fin_cases t <;> simp [result,rewind_position,returned,h.1,h.2]

theorem result_bank_outside (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (z : ℤ)
    (hz : z<c.work.pos 0 ∨ c.work.pos 0+n*B≤z) :
    cells (result read write reset B n w c) 0 z=cells c 0 z := by
  rw [result_cells]
  have h := ScheduledTransfer.copied_target_outside true true false read write reset
    (prepared read write reset B n w c) (n*B) z (by
      simpa [ScheduledTransfer.target,prepared_positions] using hz)
  exact h.trans (prepared_source read write reset B n w c z)

theorem result_blocks (hinv : Function.LeftInverse write read) (B n : ℕ) (w : List Bool)
    (c : NativeIO.Config (Fin 2) M) (k j : ℕ) (hk : k<n) (hj : j<B) :
    cells (result read write reset B n w c) 0 (c.work.pos 0+k*B+j)=
      cells c 0 (c.work.pos 0+(n-1-k : ℕ)*B+j) := by
  have hlt : k*B+j<n*B := by
    have := Nat.mul_le_mul_right B hk
    nlinarith
  have h := ScheduledTransfer.copied_target true true false read write reset
    (prepared read write reset B n w c) (n*B) (k*B+j) hlt
  simp only [ScheduledTransfer.source,ScheduledTransfer.target,ScheduledTransfer.offset,
    Bool.false_eq_true,ite_false,ite_true,prepared_positions] at h
  have hv := h.trans (hinv _)
  rw [result_cells]
  simpa only [returned,Nat.cast_add,Nat.cast_mul,← add_assoc] using
    hv.trans (by simpa only [Nat.cast_add,Nat.cast_mul,← add_assoc] using
      prepared_blocks read write reset hinv B n w c k j hk hj)

theorem result_scratch (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (hblank : ∀ z, cells c 1 z=.blank) (z : ℤ) :
    cells (result read write reset B n w c) 1 z=.blank := by
  rw [result_cells]
  by_cases hz : c.work.pos 1≤z ∧ z<c.work.pos 1+n*B
  · let j := (z-c.work.pos 1).toNat
    have hj : j<n*B := by dsimp [j]; norm_cast at hz; omega
    have he : (prepared read write reset B n w c).work.pos 1+ScheduledTransfer.offset false j=z := by
      rw [prepared_positions]; simp only [ScheduledTransfer.offset,Bool.false_eq_true,ite_false]
      dsimp [j]; omega
    have h := ScheduledTransfer.copied_source_cleared true false read write reset
      (prepared read write reset B n w c) (n*B) j hj
    simpa only [returned,ScheduledTransfer.source,ite_true,he] using h
  · have h := ScheduledTransfer.copied_source_away true true false read write reset
      (prepared read write reset B n w c) (n*B) z (by
        intro j hj
        simp only [ScheduledTransfer.source,ScheduledTransfer.offset,ite_true,
          Bool.false_eq_true,ite_false,prepared_positions]
        have hjz : (j : ℤ)<n*B := by exact_mod_cast hj
        omega)
    exact h.trans ((prepared_outside read write reset B n w c z (by omega)).trans (hblank z))

theorem result_io (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    (result read write reset B n w c).inputPos=c.inputPos ∧
    (result read write reset B n w c).outRev=c.outRev := by
  have h₀ := prepared_io read write reset B n w c
  have h₁ := ScheduledTransfer.copied_io true true false read write reset (prepared read write reset B n w c) (n*B)
  have h₂ := rewind_io 0 w (returned read write reset B n w c) (n*B)
  have h₃ := rewind_io 1 w (rewind 0 w (returned read write reset B n w c) (n*B)) (n*B)
  exact ⟨h₃.1.trans (h₂.1.trans (h₁.1.trans h₀.1)),h₃.2.trans (h₂.2.trans (h₁.2.trans h₀.2))⟩

end TransposeFollowup.BankBlockReversal

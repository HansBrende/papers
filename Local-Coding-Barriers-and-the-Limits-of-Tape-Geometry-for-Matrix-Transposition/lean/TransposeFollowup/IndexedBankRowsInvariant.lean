import TransposeFollowup.IndexedBankRows

/-! Indexed frame semantics: row k is transformed by U k from its original
contents. The constant-row theorem is a specialization of this invariant. -/
namespace TransposeFollowup.IndexedBankRows
open Classical FixedTapeCompiler ScheduledTapeAction
open CopyMachine (Sym)
open ScheduledBankRows (Update step_frame step_value)
set_option autoImplicit false
variable {M : Type*} {W : ℕ} (U : ℕ → Update M W)

theorem rows_value (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (hc : BankWord.symbols.clean c) (k j : ℕ) (hk : k<r) (hj : j<W) :
    cells (rows U r w c) 0 (c.work.pos 0+k*W+j)=
      (U k).value (fun i => cells c 0 (c.work.pos 0+k*W+i)) j := by
  induction r with
  | zero => omega
  | succ r ih =>
    rw [rows_succ]
    by_cases hkr : k=r
    · subst k
      calc
        _ = (U r).value (BankWord.input BankWord.symbols (rows U r w c)) j := by
          have h := step_value (U r) w (rows U r w c) (rows_clean U r w c hc) j hj
          simpa only [rows_position,ite_true,Nat.cast_mul] using h
        _ = _ := (U r).congruent _ _ (by
          intro i hi
          change cells (rows U r w c) 0 ((rows U r w c).work.pos 0+i)=_
          rw [rows_position]
          simp only [ite_true,Nat.cast_mul]
          apply rows_frame
          right
          have : (0 : ℤ) ≤ i := Nat.cast_nonneg i
          omega) j hj
    · rw [step_frame]
      · exact ih (by omega)
      · left
        rw [rows_position]
        simp only [ite_true,Nat.cast_mul]
        have hm : (k+1)*W ≤ r*W := Nat.mul_le_mul_right W (by omega)
        have ht : k*W+j<r*W := by nlinarith
        have htz : (k : ℤ)*W+j<r*W := by exact_mod_cast ht
        omega

def value (x : ℕ → Sym Bool) (j : ℕ) : Sym Bool :=
  (U (j/W)).value (fun i => x ((j/W)*W+i)) (j%W)

theorem value_congr (r : ℕ) : BankWord.Congruent (r*W) (value U) := by
  intro x y h j hj
  have hW : 0<W := by nlinarith
  have hk : j/W<r := (Nat.div_lt_iff_lt_mul hW).mpr hj
  apply (U (j/W)).congruent _ _ _ _ (Nat.mod_lt j hW)
  intro i hi
  apply h
  have hm : (j/W+1)*W ≤ r*W := Nat.mul_le_mul_right W hk
  nlinarith

theorem represents (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols (r*W) c (result U r w c)
      (value U (BankWord.input BankWord.symbols c)) := by
  refine ⟨result_position U r w c,?_,?_,?_⟩
  · intro j hj
    have hW : 0<W := by nlinarith
    have hk : j/W<r := (Nat.div_lt_iff_lt_mul hW).mpr hj
    have h := rows_value U r w c hc (j/W) (j%W) hk (Nat.mod_lt j hW)
    have he : (j/W)*W+j%W=j := Nat.div_add_mod' j W
    have hez : ((j/W : ℕ) : ℤ)*W+(j%W : ℕ)=j := by exact_mod_cast he
    change cells (result U r w c) 0 (c.work.pos 0+j)=
      (U (j/W)).value (fun i => cells c 0 (c.work.pos 0+((j/W)*W+i : ℕ))) (j%W)
    rw [result_cells]
    simpa only [Nat.cast_add,Nat.cast_mul,add_assoc,hez] using h
  · intro z
    change cells (result U r w c) 1 z=.blank
    rw [result_cells]
    exact rows_clean U r w c hc z
  · have h := rewind_io 0 w (rows U r w c) (r*W)
    have hh := rows_io U r w c hc
    exact ⟨h.1.trans hh.1,h.2.trans hh.2⟩

theorem result_frame (r : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (z : ℤ)
    (hz : z<c.work.pos 0 ∨ c.work.pos 0+r*W ≤ z) :
    cells (result U r w c) 0 z=cells c 0 z := by
  rw [result_cells]
  exact rows_frame U r w c z hz

end TransposeFollowup.IndexedBankRows

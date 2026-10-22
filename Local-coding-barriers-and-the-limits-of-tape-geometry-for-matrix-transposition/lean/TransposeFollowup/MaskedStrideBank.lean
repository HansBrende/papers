import TransposeFollowup.MaskedStrideScan

/-! The block invariant gives the usual raw-index, zero-filled stride
recurrence. The finite bank consists of all full groups and one partial
group; a zero-length last group is permitted and its cost remains paid. -/
namespace TransposeFollowup.MaskedStrideScan
open Classical FixedTapeCompiler
open CopyMachine (Sym)
open MaskedStrideCell (Mode State bit)
open MaskedStrideGroup (cells)
set_option autoImplicit false

def value (isPrefix : Bool) (mask x : ℕ → Bool) (S j : ℕ) : Bool :=
  output isPrefix mask x S (j/S) (j%S)

theorem value_block (isPrefix : Bool) (mask x : ℕ → Bool) {S : ℕ} (hS : 0 < S)
    (r j : ℕ) (hj : j < S) :
    value isPrefix mask x S (r*S+j)=output isPrefix mask x S r j := by
  have hd : (r*S+j)/S=r := by
    rw [Nat.mul_comm r S,Nat.mul_add_div hS,Nat.div_eq_of_lt hj,Nat.add_zero]
  simp only [value,hd,Nat.mul_add_mod_of_lt hj]

theorem value_recurrence (isPrefix : Bool) (mask x : ℕ → Bool) {S : ℕ} (hS : 0 < S)
    (n : ℕ) :
    value isPrefix mask x S n=MaskedStrideCell.output (mask n) (x n)
      (if n < S then false else if isPrefix then value isPrefix mask x S (n-S) else x (n-S)) := by
  suffices h : ∀ r j, j < S →
      value isPrefix mask x S (r*S+j)=MaskedStrideCell.output (mask (r*S+j)) (x (r*S+j))
        (if r*S+j < S then false else
          if isPrefix then value isPrefix mask x S (r*S+j-S) else x (r*S+j-S)) by
    simpa only [Nat.div_add_mod'] using h (n/S) (n%S) (Nat.mod_lt n hS)
  intro r j hj
  cases r with
  | zero =>
    rw [value_block isPrefix mask x hS 0 j hj]
    simp only [output,buffer,Nat.zero_mul,Nat.zero_add,ite_eq_left hj]
  | succ r =>
    have hs : ¬(r+1)*S+j < S := by nlinarith
    have hsub : (r+1)*S+j-S=r*S+j := by rw [Nat.add_mul]; omega
    rw [value_block isPrefix mask x hS (r+1) j hj,ite_eq_right hs,hsub,
      value_block isPrefix mask x hS r j hj]
    rfl

def result (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) (w : List Bool) (c : State) : State :=
  MaskedStrideGroup.result isPrefix (fun j => mask (P/S*S+j)) S (P%S) w
    (groups isPrefix mask S w c (P/S))

theorem result_correct (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0 < S)
    (w : List Bool) (c : State) (hzero : ∀ j < S, bit (cells c 1 (c.work.pos 1+j))=false) :
    (result isPrefix mask P S w c).work.pos 0=c.work.pos 0+P ∧
    (result isPrefix mask P S w c).work.pos 1=c.work.pos 1 ∧
    (∀ j < P, cells (result isPrefix mask P S w c) 0 (c.work.pos 0+j)=
      .data (value isPrefix mask (input c) S j)) ∧
    (∀ z, c.work.pos 0+P ≤ z → cells (result isPrefix mask P S w c) 0 z=cells c 0 z) := by
  have h := partial_correct isPrefix mask (Nat.mod_lt P hS).le w c hzero (P/S)
  dsimp only at h
  refine ⟨?_,h.2.1,?_,?_⟩
  · simpa [result,Nat.div_add_mod'] using h.1
  · intro j hj
    have hjS := Nat.mod_lt j hS
    by_cases hq : j/S < P/S
    · simpa [result,Nat.div_add_mod',value] using h.2.2.1 (j/S) hq (j%S) hjS
    · have he : j/S=P/S := by
        have hle := Nat.div_le_div_right (Nat.le_of_lt hj) (c:=S)
        omega
      have hm : j%S < P%S := by
        have hp := Nat.div_add_mod' P S
        have hj' := Nat.div_add_mod' j S
        rw [he] at hj'
        omega
      simpa [result,← he,Nat.div_add_mod',value] using h.2.2.2.1 (j%S) hm
  · simpa [result,Nat.div_add_mod'] using h.2.2.2.2

end TransposeFollowup.MaskedStrideScan

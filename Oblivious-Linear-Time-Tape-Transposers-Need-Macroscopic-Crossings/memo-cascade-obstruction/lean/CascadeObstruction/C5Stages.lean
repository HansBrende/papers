import CascadeObstruction.C5Trace

/-! Cascade 5's physical stages, expanded into constant and two-tick blocks.
The first reset is charged to root preparation. This changes only clock
ownership: every tick of the published constructor is retained. -/

namespace CascadeObstruction.C5

open Transpose

set_option autoImplicit false

def tick (a b : Dir) : Tick := ⟨.stay, a, b, false⟩

/-- The constructor's load followed by its first reset to the origin. -/
def preparation (L : ℕ) : List Block :=
  [.straight (L - 1) ⟨.right, .right, .stay, false⟩,
   .straight 1 ⟨.right, .stay, .stay, false⟩,
   .straight (L - 1) (tick .left .stay)]

def output (L : ℕ) : List Block :=
  [.straight (L - 1) ⟨.stay, .right, .stay, true⟩,
   .straight 1 ⟨.stay, .stay, .stay, true⟩]

/-- A forward stage with M=2H. The initial reset is empty except at depth
one, where it was moved into `preparation`. Each listed reset is literal. -/
def forward (H : ℕ) : List Block :=
  [.straight (2 * H - 1) (tick .right .right),
   .straight 1 (tick .stay .stay),
   .straight 1 (tick .right .left),
   .straight (H - 2) (tick .stay .left),
   .straight (H - 1) (tick .right .right),
   .straight 1 (tick .right .stay),
   .straight (2 * H - 1) (tick .stay .left),
   .straight (H - 1) (tick .right .right),
   .straight 1 (tick .stay .stay),
   .straight H (tick .left .right),
   .straight H (tick .left .stay),
   .straight (2 * H - 1) (tick .left .left),
   .straight 1 (tick .stay .stay)]

def tooth (h : ℕ) (last : Bool) : List Block :=
  [.straight (h - 1) (tick .left .left),
   .straight (h - 1) (tick .stay .right),
   .straight (h - 1) (tick .stay .left),
   .straight 1 (if last then tick .stay .stay else tick .left .left)]

/-- All N teeth, including the last stationary event. -/
def comb (N h : ℕ) : List Block :=
  (List.replicate (N - 1) (tooth h false)).flatten ++ tooth h true

/-- A backward stage with M=2H=N*h. The identity of the two products is
an arithmetic fact at an actual depth, not an assumption about a trace. -/
def backward (H N h : ℕ) : List Block :=
  [.straight (2 * H - 1) (tick .right .right)] ++ comb N h ++
  [.pairs (2 * H - 1) (tick .right .stay) (tick .right .right),
   .pairs 1 (tick .right .stay) (tick .stay .stay),
   .straight H (tick .stay .left),
   .pairs (H - 1) (tick .left .stay) (tick .left .left),
   .pairs 1 (tick .left .stay) (tick .left .stay),
   .straight (2 * H - 1) (tick .stay .right),
   .pairs (H - 1) (tick .left .stay) (tick .left .left),
   .pairs 1 (tick .left .stay) (tick .stay .stay),
   .straight H (tick .stay .left)]

@[simp] theorem preparation_duration {L : ℕ} (hL : 1 ≤ L) :
    blocksDuration (preparation L) = 2 * L - 1 := by
  simp [preparation, blocksDuration, Block.duration]
  omega

@[simp] theorem output_duration {L : ℕ} (hL : 1 ≤ L) :
    blocksDuration (output L) = L := by
  simp [output, blocksDuration, Block.duration]
  omega

@[simp] theorem forward_duration {H : ℕ} (hH : 2 ≤ H) :
    blocksDuration (forward H) = 11 * H - 2 := by
  simp [forward, blocksDuration, Block.duration]
  omega

@[simp] theorem tooth_duration {h : ℕ} (hh : 1 ≤ h) (last : Bool) :
    blocksDuration (tooth h last) = 3 * h - 2 := by
  simp [tooth, blocksDuration, Block.duration]
  omega

theorem comb_duration {N h : ℕ} (hN : 1 ≤ N) (hh : 1 ≤ h) :
    blocksDuration (comb N h) = N * (3 * h - 2) := by
  simp only [comb, blocksDuration_append, blocksDuration_flatten_replicate,
    tooth_duration hh]
  conv_rhs => rw [show N = N - 1 + 1 by omega, Nat.add_mul]
  simp

theorem backward_duration {H N h : ℕ} (hH : 1 ≤ H) (hN : 1 ≤ N)
    (hh : 1 ≤ h) (hprod : 2 * H = N * h) :
    blocksDuration (backward H N h) = 20 * H - 2 * N - 2 := by
  simp only [backward, blocksDuration_append, comb_duration hN hh]
  simp [blocksDuration, Block.duration]
  have hthree : 2 ≤ 3 * h := by omega
  have hcomb : N * (3 * h - 2) = 6 * H - 2 * N := by
    rw [Nat.mul_sub, show N * (3 * h) = 3 * (N * h) by ring, ← hprod]
    omega
  rw [hcomb]
  have hnH : N ≤ 2 * H := by nlinarith
  omega

theorem stage_budget {H N h : ℕ} (hH : 2 ≤ H) (hN : 1 ≤ N)
    (hh : 1 ≤ h) (hprod : 2 * H = N * h) :
    blocksDuration (forward H) + blocksDuration (backward H N h) ≤ 18 * (2 * H) := by
  rw [forward_duration hH, backward_duration (by omega) hN hh hprod]
  omega

@[simp] theorem forward_blocks (H : ℕ) : (forward H).length = 13 := rfl

@[simp] theorem backward_blocks {N H h : ℕ} (hN : 1 ≤ N) :
    (backward H N h).length = 4 * N + 10 := by
  simp [backward, comb, tooth, List.length_flatten]
  omega

@[simp] theorem preparation_input {L : ℕ} (hL : 1 ≤ L) :
    totalMove (preparation L) 0 = L := by
  simp [preparation, totalMove, Block.totalMove, tick, Tick.move,
    Nat.cast_sub hL]

@[simp] theorem preparation_work (L : ℕ) (h : Fin 2) :
    totalMove (preparation L) h.succ = 0 := by
  fin_cases h <;> simp [preparation, totalMove, Block.totalMove, tick, Tick.move]

@[simp] theorem forward_move {H : ℕ} (hH : 2 ≤ H) (h : Fin 3) :
    totalMove (forward H) h = 0 := by
  have hH1 : 1 ≤ H := by omega
  have h2H : 1 ≤ 2 * H := by omega
  fin_cases h <;>
    simp [forward, totalMove, Block.totalMove, tick, Tick.move,
      Nat.cast_sub hH, Nat.cast_sub hH1, Nat.cast_sub h2H] <;> ring

theorem tooth_move {h : ℕ} (hh : 1 ≤ h) (last : Bool) (w : Fin 2) :
    totalMove (tooth h last) w.succ = -(h : ℤ) + if last then 1 else 0 := by
  cases last <;> fin_cases w <;>
    simp [tooth, totalMove, Block.totalMove, tick, Tick.move, Nat.cast_sub hh] <;> ring

theorem comb_move {N h : ℕ} (hN : 1 ≤ N) (hh : 1 ≤ h) (w : Fin 2) :
    totalMove (comb N h) w.succ = -((N * h : ℕ) : ℤ) + 1 := by
  simp only [comb, totalMove_append, totalMove_flatten_replicate,
    tooth_move hh]
  simp [Nat.cast_sub hN]
  ring

@[simp] theorem comb_input (N h : ℕ) : totalMove (comb N h) 0 = 0 := by
  simp [comb, tooth, totalMove, Block.totalMove, tick, Tick.move]

@[simp] theorem backward_move {H N h : ℕ} (hH : 1 ≤ H) (hN : 1 ≤ N)
    (hh : 1 ≤ h) (hprod : 2 * H = N * h) (w : Fin 3) :
    totalMove (backward H N h) w = 0 := by
  have h2H : 1 ≤ 2 * H := by omega
  have hp : ((N * h : ℕ) : ℤ) = 2 * H := by exact_mod_cast hprod.symm
  fin_cases w
  · simpa [backward, totalMove, Block.totalMove, tick, Tick.move] using comb_input N h
  · have hc := comb_move hN hh (0 : Fin 2)
    simp only [Fin.succ_zero_eq_one] at hc
    calc
      totalMove (backward H N h) 1 = totalMove (comb N h) 1 + 2 * H - 1 := by
        simp [backward, totalMove, Block.totalMove, tick, Tick.move,
          Nat.cast_sub hH, Nat.cast_sub h2H]
        ring
      _ = 0 := by rw [hc, hp]; ring
  · have hc := comb_move hN hh (1 : Fin 2)
    change totalMove (comb N h) 2 = _ at hc
    calc
      totalMove (backward H N h) 2 = totalMove (comb N h) 2 + 2 * H - 1 := by
        simp [backward, totalMove, Block.totalMove, tick, Tick.move,
          Nat.cast_sub hH, Nat.cast_sub h2H]
        ring
      _ = 0 := by rw [hc, hp]; ring

@[simp] theorem output_input (L : ℕ) : totalMove (output L) 0 = 0 := by
  simp [output, totalMove, Block.totalMove, Tick.move]

@[simp] theorem output_work0 (L : ℕ) : totalMove (output L) 1 = (L - 1 : ℕ) := by
  simp [output, totalMove, Block.totalMove, Tick.move]

@[simp] theorem output_work1 (L : ℕ) : totalMove (output L) 2 = 0 := by
  simp [output, totalMove, Block.totalMove, Tick.move]

end CascadeObstruction.C5

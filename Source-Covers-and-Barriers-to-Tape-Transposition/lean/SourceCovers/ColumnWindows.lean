import Transpose.Tape.CECount
import LeanMachine.FrozenBank

/-! Actual append-time windows for transpose columns. -/

namespace SourceCovers

open Classical Finset LeanMachine Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators

def columnFirst (t : ℕ → ℕ) (W j : ℕ) : ℕ := t (j * W)
def columnLast (t : ℕ → ℕ) (W j : ℕ) : ℕ := t ((j + 1) * W - 1)

theorem column_indices {d b j : ℕ} (hd : 0 < d) (hb : 0 < b) (hj : j < d) :
    j * (d * b) ≤ (j + 1) * (d * b) - 1 ∧
      (j + 1) * (d * b) - 1 < d * d * b := by
  have hW : 0 < d * b := Nat.mul_pos hd hb
  have hmul : (j + 1) * (d * b) ≤ d * d * b := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (d * b) (Nat.succ_le_of_lt hj)
  constructor
  · rw [Nat.add_mul, Nat.one_mul]
    omega
  · exact (Nat.sub_lt (Nat.mul_pos (Nat.succ_pos j) hW) zero_lt_one).trans_le hmul

theorem column_window_order {d b : ℕ} {t : ℕ → ℕ}
    (hd : 0 < d) (hb : 0 < b) (ht : StrictMonoOn t (Set.Iio (d * d * b)))
    (j : Fin d) : columnFirst t (d * b) j ≤ columnLast t (d * b) j := by
  obtain ⟨hle, hlast⟩ := column_indices hd hb j.isLt
  exact ht.monotoneOn (hle.trans_lt hlast) hlast hle

theorem column_window_last {d b n : ℕ} {t : ℕ → ℕ}
    (hd : 0 < d) (hb : 0 < b) (ht : ∀ r < d * d * b, t r ≤ n)
    (j : Fin d) : columnLast t (d * b) j ≤ n :=
  ht _ (column_indices hd hb j.isLt).2

theorem column_windows_disjoint {d b : ℕ} {t : ℕ → ℕ}
    (hd : 0 < d) (hb : 0 < b) (ht : StrictMonoOn t (Set.Iio (d * d * b))) :
    Pairwise (fun j k : Fin d => Disjoint
      (Ico (columnFirst t (d * b) j) (columnLast t (d * b) j))
      (Ico (columnFirst t (d * b) k) (columnLast t (d * b) k))) := by
  have hsep {j k : Fin d} (hjk : j < k) :
      columnLast t (d * b) j < columnFirst t (d * b) k := by
    have hW := Nat.mul_pos hd hb
    have hj := column_indices hd hb j.isLt
    have hk := column_indices hd hb k.isLt
    have hmul := Nat.mul_le_mul_right (d * b) (Nat.succ_le_of_lt hjk)
    exact ht hj.2 (hk.1.trans_lt hk.2)
      ((Nat.sub_lt (Nat.mul_pos (Nat.succ_pos j.val) hW) zero_lt_one).trans_le hmul)
  intro j k hne
  apply disjoint_left.mpr
  intro e hej hek
  have hej' := mem_Ico.mp hej
  have hek' := mem_Ico.mp hek
  rcases lt_or_gt_of_ne hne with h | h
  · have := hsep h; omega
  · have := hsep h; omega

/-- The reused native transpose position falls in its actual output column. -/
theorem transpose_column_window {d b z : ℕ} {t : ℕ → ℕ}
    (hd : 0 < d) (hb : 0 < b) (ht : StrictMonoOn t (Set.Iio (d * d * b)))
    (hz : z < d * d * b) :
    t (tpos d b z) ∈ IntervalOscillation.times
      (columnFirst t (d * b) (z / b % d)) (columnLast t (d * b) (z / b % d)) := by
  let j : Fin d := ⟨z / b % d, Nat.mod_lt _ hd⟩
  have hpos := tpos_lt hz
  have hdiv := tpos_div hz
  have hmod := Nat.mod_lt (tpos d b z) (Nat.mul_pos hd hb)
  have heq := Nat.div_add_mod (tpos d b z) (d * b)
  rw [hdiv] at heq
  rw [Nat.mul_comm (d * b)] at heq
  have hj := column_indices hd hb j.isLt
  have hlo : j.val * (d * b) ≤ tpos d b z := by dsimp [j]; omega
  have hhi : tpos d b z ≤ (j.val + 1) * (d * b) - 1 := by
    dsimp [j]
    rw [Nat.add_mul, Nat.one_mul]
    omega
  apply (IntervalOscillation.mem_times (column_window_order hd hb ht j)).mpr
  exact ⟨ht.monotoneOn (hj.1.trans_lt hj.2) hpos hlo,
    ht.monotoneOn hpos hj.2 hhi⟩

/-- The sharper maximum-oscillation freezing radii still sum to at most
the manuscript's total bank variation. -/
theorem sum_column_radius_le {d b n : ℕ} {t : ℕ → ℕ}
    {ι : Type*} [Fintype ι] (Y : ι → ℕ → ℕ)
    (hd : 0 < d) (hb : 0 < b) (ht : StrictMonoOn t (Set.Iio (d * d * b)))
    (hn : ∀ r < d * d * b, t r ≤ n) :
    (∑ j : Fin d, (FrozenBank.radius Y (columnFirst t (d * b) j)
      (columnLast t (d * b) j) : ℝ)) ≤
      ∑ i, MonotonePatches.variation (fun s => (Y i s : ℝ)) n :=
  FrozenBank.sum_radius_le_variation Y _ _ n
    (column_window_order hd hb ht) (column_window_last hd hb hn)
    (column_windows_disjoint hd hb ht)

end SourceCovers

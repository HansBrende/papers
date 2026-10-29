import SourceCovers.ColumnWindows
import SourceCovers.ResidualRecovery
import LeanMachine.CyclicSelection
import LeanMachine.GapErosion

/-! Actual frozen anchors and their circular overcovers. The raw blocks remain
linear, endpoint-clipped blocks; only the overcover is circular. -/

namespace SourceCovers

open Classical Finset LeanMachine Transpose.Tape
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

def frozenAnchors (Y : ι → ℕ → ℕ) (t : ℕ → ℕ) (W j : ℕ) : Finset ℕ :=
  residualBankValues Y (columnFirst t W j)

def columnRadius (Y : ι → ℕ → ℕ) (t : ℕ → ℕ) (W j : ℕ) : ℕ :=
  FrozenBank.radius Y (columnFirst t W j) (columnLast t W j)

def frozenOvercover (Y : ι → ℕ → ℕ) (t : ℕ → ℕ) (d b w j : ℕ) : Finset ℕ :=
  CyclicSelection.overcover (d * d * b) (frozenAnchors Y t (d * b) j)
    (w - 1 + columnRadius Y t (d * b) j)

theorem frozenAnchors_nonempty [Nonempty ι]
    (Y : ι → ℕ → ℕ) (t : ℕ → ℕ) (W j : ℕ) :
    (frozenAnchors Y t W j).Nonempty :=
  univ_nonempty.image _

/-- Point-gap area of the actual distinct frozen anchors; coincident slots
are counted only once. -/
def frozenArea [Nonempty ι] (Y : ι → ℕ → ℕ) (t : ℕ → ℕ) (d b j : ℕ) : ℝ :=
  let S := frozenAnchors Y t (d * b) j
  GapErosion.pointArea (range S.card)
    (CyclicSelection.gap (d * d * b) S (frozenAnchors_nonempty Y t (d * b) j))
    (d * d * b)

theorem frozenAnchors_subset {Y : ι → ℕ → ℕ} {t : ℕ → ℕ} {d b n j : ℕ}
    (hd : 0 < d) (hb : 0 < b) (hj : j < d)
    (hn : ∀ r < d * d * b, t r ≤ n)
    (hY : ∀ i s, s ≤ n → Y i s < d * d * b) :
    frozenAnchors Y t (d * b) j ⊆ range (d * d * b) := by
  rintro a ha
  obtain ⟨i, _, rfl⟩ := mem_image.mp ha
  exact mem_range.mpr (hY i _ (hn _
    ((column_indices hd hb hj).1.trans_lt (column_indices hd hb hj).2)))

/-- Freezing covers every coordinate of every source block at the actual
transpose append time, using the maximum slot oscillation. -/
theorem residualBlocks_subset_frozen {Y : ι → ℕ → ℕ} {t : ℕ → ℕ}
    {d b w θ z : ℕ} (hd : 0 < d) (hb : 0 < b) (hw : 0 < w)
    (ht : StrictMonoOn t (Set.Iio (d * d * b))) (hz : z < d * d * b) :
    residualBlocks Y (d * d * b) w θ (t (tpos d b z)) ⊆
      (frozenOvercover Y t d b w (z / b % d) : Set ℕ) := by
  rintro q ⟨hq, i, hi⟩
  apply CyclicSelection.mem_overcover.mpr
  refine ⟨hq, CyclicSelection.covered_of_dist_le
    (a := Y i (columnFirst t (d * b) (z / b % d))) ?_ ?_⟩
  · exact mem_image.mpr ⟨i, mem_univ _, rfl⟩
  · exact FrozenBank.block_dist_le hw (transpose_column_window hd hb ht hz) i hi

/-- Functional output recovery on a correctness set. The output associated
to raw coordinate `z` is appended at `t (tpos d b z)`. -/
def TransposeBankRecovers {H : Type*} {d b : ℕ}
    (C : Finset (Fin (d * d * b) → Bool)) (Z : C → H)
    (Y : ι → ℕ → ℕ) (t : ℕ → ℕ) (w θ : ℕ) : Prop :=
  ∀ z : Fin (d * d * b), ∀ x y : C, Z x = Z y →
    Set.EqOn x.val y.val {q | q.val ∈
      residualBlocks Y (d * d * b) w θ (t (tpos d b z.val))} →
    x.val z = y.val z

theorem frozenOvercover_recovers {H : Type*} {d b w θ : ℕ}
    {C : Finset (Fin (d * d * b) → Bool)} {Z : C → H}
    {Y : ι → ℕ → ℕ} {t : ℕ → ℕ}
    (hd : 0 < d) (hb : 0 < b) (hw : 0 < w)
    (ht : StrictMonoOn t (Set.Iio (d * d * b)))
    (hlocal : TransposeBankRecovers C Z Y t w θ)
    (z : Fin (d * d * b)) (x y : C) (hZ : Z x = Z y)
    (hraw : Set.EqOn x.val y.val
      {q | q.val ∈ frozenOvercover Y t d b w (z.val / b % d)}) :
    x.val z = y.val z := by
  apply hlocal z x y hZ
  exact hraw.mono fun _ hq => residualBlocks_subset_frozen hd hb hw ht z.isLt hq

end
end SourceCovers

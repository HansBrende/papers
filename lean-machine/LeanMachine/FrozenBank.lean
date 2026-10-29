import LeanMachine.IntervalOscillation
import LeanMachine.ShiftedGrid
import Mathlib.Data.Nat.Dist

/-! Freeze a finite bank on disjoint time windows. The maximum slot
oscillation suffices; it is bounded by the sum of all slot variations. -/

namespace LeanMachine.FrozenBank

open Classical Finset IntervalOscillation
open scoped BigOperators

noncomputable section

theorem dist_le_oscillation {Y : ℕ → ℕ} {a b s t : ℕ}
    (hs : s ∈ times a b) (ht : t ∈ times a b) :
    Nat.dist (Y s) (Y t) ≤ oscillation Y a b := by
  have := lower_le (Y := Y) hs
  have := lower_le (Y := Y) ht
  have := le_upper (Y := Y) hs
  have := le_upper (Y := Y) ht
  unfold oscillation Nat.dist
  omega

/-- One radius controls every slot, without adding simultaneous movements. -/
def radius {ι : Type*} [Fintype ι] (Y : ι → ℕ → ℕ) (a b : ℕ) : ℕ :=
  univ.sup (fun i => oscillation (Y i) a b)

theorem oscillation_le_radius {ι : Type*} [Fintype ι]
    (Y : ι → ℕ → ℕ) (a b : ℕ) (i : ι) : oscillation (Y i) a b ≤ radius Y a b := by
  exact le_sup (f := fun i => oscillation (Y i) a b) (mem_univ i)

theorem radius_le_sum {ι : Type*} [Fintype ι] (Y : ι → ℕ → ℕ) (a b : ℕ) :
    radius Y a b ≤ ∑ i, oscillation (Y i) a b := by
  apply Finset.sup_le
  intro i hi
  exact single_le_sum (f := fun i => oscillation (Y i) a b) (fun _ _ => Nat.zero_le _) hi

theorem label_dist_le {w θ z y : ℕ} (hw : 0 < w)
    (h : ShiftedGrid.label w θ z = ShiftedGrid.label w θ y) : Nat.dist z y ≤ w - 1 := by
  have h₁ := ShiftedGrid.sub_lt_of_label_eq hw h
  have h₂ := ShiftedGrid.sub_lt_of_label_eq hw h.symm
  unfold Nat.dist
  omega

/-- Every coordinate of an entire current block lies near its frozen anchor. -/
theorem block_dist_le {ι : Type*} [Fintype ι] {Y : ι → ℕ → ℕ}
    {a b t w θ z : ℕ} (hw : 0 < w) (ht : t ∈ times a b) (i : ι)
    (hz : ShiftedGrid.label w θ z = ShiftedGrid.label w θ (Y i t)) :
    Nat.dist z (Y i a) ≤ w - 1 + radius Y a b := by
  apply (Nat.dist.triangle_inequality z (Y i t) (Y i a)).trans
  apply Nat.add_le_add (label_dist_le hw hz)
  exact (dist_le_oscillation ht (mem_Icc.mpr ⟨le_rfl, le_max_left _ _⟩)).trans
    (oscillation_le_radius Y a b i)

/-- Exact overlap-profile control of the sum of the maximum slot radii. -/
theorem sum_radius_le_profile {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : ι → ℕ → ℕ) (first last : κ → ℕ) (n : ℕ)
    (hfirst : ∀ j, first j ≤ last j) (hlast : ∀ j, last j ≤ n) :
    (∑ j, (radius Y (first j) (last j) : ℝ)) ≤
      ∑ e ∈ range n, (multiplicity univ first last e : ℝ) *
        ∑ i, dist (Y i e : ℝ) (Y i (e + 1) : ℝ) := by
  calc
    _ ≤ ∑ j, ∑ i, (oscillation (Y i) (first j) (last j) : ℝ) := by
      apply sum_le_sum
      intro j _
      exact_mod_cast radius_le_sum Y (first j) (last j)
    _ = ∑ i, ∑ j, (oscillation (Y i) (first j) (last j) : ℝ) := sum_comm
    _ ≤ ∑ i, ∑ e ∈ range n, (multiplicity univ first last e : ℝ) *
        dist (Y i e : ℝ) (Y i (e + 1) : ℝ) :=
      sum_le_sum fun i _ => sum_oscillation_le_profile univ (Y i) first last n
        (fun j _ => hfirst j) (fun j _ => hlast j)
    _ = _ := by rw [sum_comm]; simp only [mul_sum]

/-- Disjoint elementary window edges are charged only once. -/
theorem sum_radius_le_variation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : ι → ℕ → ℕ) (first last : κ → ℕ) (n : ℕ)
    (hfirst : ∀ j, first j ≤ last j) (hlast : ∀ j, last j ≤ n)
    (hdisj : Pairwise
      (fun j k => Disjoint (Ico (first j) (last j)) (Ico (first k) (last k)))) :
    (∑ j, (radius Y (first j) (last j) : ℝ)) ≤
      ∑ i, MonotonePatches.variation (fun t => (Y i t : ℝ)) n := by
  have hmult (e : ℕ) : multiplicity univ first last e ≤ 1 := by
    apply card_le_one.mpr
    intro j hj k hk
    obtain ⟨hj, hj'⟩ := mem_filter.mp hj
    obtain ⟨hk, hk'⟩ := mem_filter.mp hk
    by_contra hne
    exact (disjoint_left.mp (hdisj hne)) (mem_Ico.mpr hj') (mem_Ico.mpr hk')
  calc
    _ ≤ _ := sum_radius_le_profile Y first last n hfirst hlast
    _ ≤ ∑ e ∈ range n, ∑ i, dist (Y i e : ℝ) (Y i (e + 1) : ℝ) := by
      apply sum_le_sum
      intro e _
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hmult e)
        (sum_nonneg fun _ _ => dist_nonneg)).trans_eq (one_mul _)
    _ = _ := by rw [sum_comm]; rfl

end
end LeanMachine.FrozenBank

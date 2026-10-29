import LeanMachine.MonotonePatches
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Oscillation on finite lifetimes

The extrema are actual path values. Interval variation controls their difference,
and summing this cost preserves the exact overlap profile of the lifetimes.
-/

namespace LeanMachine.IntervalOscillation

open Classical Finset
open scoped BigOperators
open MonotonePatches

/-- A closed lifetime, made total by collapsing reversed endpoints to the start. -/
def times (a b : ℕ) : Finset ℕ := Icc a (max a b)

theorem times_nonempty (a b : ℕ) : (times a b).Nonempty :=
  ⟨a, mem_Icc.mpr ⟨le_rfl, le_max_left _ _⟩⟩

def lower (Y : ℕ → ℕ) (a b : ℕ) : ℕ := (times a b).inf' (times_nonempty a b) Y

def upper (Y : ℕ → ℕ) (a b : ℕ) : ℕ := (times a b).sup' (times_nonempty a b) Y

def oscillation (Y : ℕ → ℕ) (a b : ℕ) : ℕ := upper Y a b - lower Y a b

theorem lower_attained (Y : ℕ → ℕ) (a b : ℕ) :
    ∃ t ∈ times a b, lower Y a b = Y t :=
  exists_mem_eq_inf' (times_nonempty a b) Y

theorem upper_attained (Y : ℕ → ℕ) (a b : ℕ) :
    ∃ t ∈ times a b, upper Y a b = Y t :=
  exists_mem_eq_sup' (times_nonempty a b) Y

theorem lower_le {Y : ℕ → ℕ} {a b t : ℕ} (ht : t ∈ times a b) :
    lower Y a b ≤ Y t := inf'_le Y ht

theorem le_upper {Y : ℕ → ℕ} {a b t : ℕ} (ht : t ∈ times a b) :
    Y t ≤ upper Y a b := le_sup' Y ht

theorem lower_le_upper (Y : ℕ → ℕ) (a b : ℕ) : lower Y a b ≤ upper Y a b :=
  (lower_le (times_nonempty a b).choose_spec).trans
    (le_upper (times_nonempty a b).choose_spec)

theorem mem_times {a b t : ℕ} (hab : a ≤ b) : t ∈ times a b ↔ a ≤ t ∧ t ≤ b := by
  simp only [times, max_eq_right hab, mem_Icc]

/-- The distance between any two samples is bounded by variation over the
containing time interval, regardless of their temporal order. -/
theorem dist_le_interval_variation {X : Type*} [PseudoMetricSpace X]
    (Y : ℕ → X) {a b s t : ℕ} (hs : a ≤ s ∧ s ≤ b) (ht : a ≤ t ∧ t ≤ b) :
    dist (Y s) (Y t) ≤ ∑ e ∈ Ico a b, dist (Y e) (Y (e + 1)) := by
  have hsub : Ico (min s t) (max s t) ⊆ Ico a b := by
    intro e he
    have := mem_Ico.mp he
    exact mem_Ico.mpr ⟨(le_min hs.1 ht.1).trans this.1,
      this.2.trans_le (max_le hs.2 ht.2)⟩
  have hdist : dist (Y s) (Y t) ≤
      ∑ e ∈ Ico (min s t) (max s t), dist (Y e) (Y (e + 1)) := by
    rcases le_total s t with h | h
    · simpa only [min_eq_left h, max_eq_right h] using dist_le_Ico_sum_dist Y h
    · simpa only [min_eq_right h, max_eq_left h, dist_comm (Y t)] using
        dist_le_Ico_sum_dist Y h
  exact hdist.trans (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => dist_nonneg))

theorem oscillation_le_interval_variation (Y : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b) :
    (oscillation Y a b : ℝ) ≤
      ∑ e ∈ Ico a b, dist (Y e : ℝ) (Y (e + 1) : ℝ) := by
  obtain ⟨s, hs, hmin⟩ := lower_attained Y a b
  obtain ⟨t, ht, hmax⟩ := upper_attained Y a b
  have h := dist_le_interval_variation (fun e => (Y e : ℝ))
    ((mem_times hab).mp hs) ((mem_times hab).mp ht)
  have hle : (lower Y a b : ℝ) ≤ upper Y a b := by
    exact_mod_cast lower_le_upper Y a b
  rw [← hmin, ← hmax, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle)] at h
  simpa only [oscillation, Nat.cast_sub (lower_le_upper Y a b), neg_sub] using h

/-- Number of indexed lifetimes that straddle an elementary time boundary. -/
def multiplicity {ι : Type*} (I : Finset ι) (first last : ι → ℕ) (e : ℕ) : ℕ :=
  (I.filter (fun i => first i ≤ e ∧ e < last i)).card

/-- Exact incidence accounting: no uniform overlap estimate is imposed. -/
theorem sum_oscillation_le_profile {ι : Type*} (I : Finset ι)
    (Y : ℕ → ℕ) (first last : ι → ℕ) (n : ℕ)
    (hfirst : ∀ i ∈ I, first i ≤ last i) (hlast : ∀ i ∈ I, last i ≤ n) :
    (∑ i ∈ I, (oscillation Y (first i) (last i) : ℝ)) ≤
      ∑ e ∈ range n, (multiplicity I first last e : ℝ) *
        dist (Y e : ℝ) (Y (e + 1) : ℝ) := by
  calc
    _ ≤ ∑ i ∈ I, ∑ e ∈ Ico (first i) (last i),
        dist (Y e : ℝ) (Y (e + 1) : ℝ) :=
      sum_le_sum fun i hi => oscillation_le_interval_variation Y (hfirst i hi)
    _ = _ := by
      simpa only [multiplicity, mem_Ico, nsmul_eq_mul] using
        FiniteIncidence.sum_eq_sum_multiplicity I (range n)
          (fun i => Ico (first i) (last i))
          (fun e => dist (Y e : ℝ) (Y (e + 1) : ℝ))
          (fun i hi e he => mem_range.mpr ((mem_Ico.mp he).2.trans_le (hlast i hi)))

theorem sum_oscillation_le_mul_variation {ι : Type*} (I : Finset ι)
    (Y : ℕ → ℕ) (first last : ι → ℕ) (n H : ℕ)
    (hfirst : ∀ i ∈ I, first i ≤ last i) (hlast : ∀ i ∈ I, last i ≤ n)
    (hH : ∀ e < n, multiplicity I first last e ≤ H) :
    (∑ i ∈ I, (oscillation Y (first i) (last i) : ℝ)) ≤
      H * variation (fun e => (Y e : ℝ)) n := by
  calc
    _ ≤ _ := sum_oscillation_le_profile I Y first last n hfirst hlast
    _ ≤ ∑ e ∈ range n, (H : ℝ) * dist (Y e : ℝ) (Y (e + 1) : ℝ) :=
      sum_le_sum fun e he => mul_le_mul_of_nonneg_right
        (by exact_mod_cast hH e (mem_range.mp he)) dist_nonneg
    _ = _ := by rw [← mul_sum]; rfl

end LeanMachine.IntervalOscillation

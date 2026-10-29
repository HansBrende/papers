import LeanMachine.ShiftedGrid
import LeanMachine.IntervalOscillation

/-!
# Paying for grid crossings along finite lifetimes

Exact single-slot shift counts give a capped oscillation budget. Incidence
accounting then preserves the lifetime overlap profile before any uniform bound.
-/

namespace LeanMachine.GridPayment

open Classical Finset ShiftedGrid IntervalOscillation MonotonePatches
open scoped BigOperators

variable {α ι : Type*} [Fintype ι]

/-- Lifetimes on which at least one slot changes grid label. -/
noncomputable def cut (I : Finset α) (Y : ι → ℕ → ℕ) (first last : α → ℕ)
    (w θ : ℕ) : Finset α :=
  I.filter (fun u => ∃ i, label w θ (lower (Y i) (first u) (last u)) ≠
    label w θ (upper (Y i) (first u) (last u)))

theorem cut_subset (I : Finset α) (Y : ι → ℕ → ℕ) (first last : α → ℕ)
    (w θ : ℕ) : cut I Y first last w θ ⊆ I := filter_subset _ _

/-- An unpaid lifetime keeps every slot in a single block for its entire extent. -/
theorem labels_eq_of_not_mem_cut {I : Finset α} {Y : ι → ℕ → ℕ}
    {first last : α → ℕ} {w θ t s : ℕ} {a : α}
    (ha : a ∈ I) (hcut : a ∉ cut I Y first last w θ)
    (ht : t ∈ times (first a) (last a)) (hs : s ∈ times (first a) (last a))
    (i : ι) : label w θ (Y i t) = label w θ (Y i s) := by
  have he : label w θ (lower (Y i) (first a) (last a)) =
      label w θ (upper (Y i) (first a) (last a)) := by
    by_contra hne
    exact hcut (mem_filter.mpr ⟨ha, i, hne⟩)
  have := label_mono w θ (lower_le (Y := Y i) ht)
  have := label_mono w θ (le_upper (Y := Y i) ht)
  have := label_mono w θ (lower_le (Y := Y i) hs)
  have := label_mono w θ (le_upper (Y := Y i) hs)
  omega

/-- A union bound over slots with the exact, capped single-slot counts. -/
theorem sum_cut_card_le_capped (I : Finset α) (Y : ι → ℕ → ℕ)
    (first last : α → ℕ) {w : ℕ} (hw : 0 < w) :
    (∑ θ ∈ range w, (cut I Y first last w θ).card) ≤
      ∑ u ∈ I, ∑ i, min w (oscillation (Y i) (first u) (last u)) := by
  have hswap : (∑ θ ∈ range w, (cut I Y first last w θ).card) =
      ∑ u ∈ I, ((range w).filter (fun θ => ∃ i,
        label w θ (lower (Y i) (first u) (last u)) ≠
          label w θ (upper (Y i) (first u) (last u)))).card := by
    simp only [cut, card_eq_sum_ones, sum_filter]
    rw [sum_comm]
  rw [hswap]
  apply sum_le_sum
  intro u hu
  have he : ((range w).filter (fun θ => ∃ i,
      label w θ (lower (Y i) (first u) (last u)) ≠
        label w θ (upper (Y i) (first u) (last u)))) =
      univ.biUnion (fun i : ι => separatingShifts w
        (lower (Y i) (first u) (last u)) (upper (Y i) (first u) (last u))) := by
    ext θ
    simp only [separatingShifts, mem_filter, mem_biUnion, mem_univ, true_and]
    exact ⟨fun ⟨hθ, i, hi⟩ => ⟨i, hθ, hi⟩,
      fun ⟨i, hθ, hi⟩ => ⟨hθ, i, hi⟩⟩
  rw [he]
  calc
    _ ≤ ∑ i, (separatingShifts w (lower (Y i) (first u) (last u))
        (upper (Y i) (first u) (last u))).card := card_biUnion_le
    _ = _ := by
      apply sum_congr rfl
      intro i _
      exact separatingShifts_card hw (lower_le_upper (Y i) (first u) (last u))

theorem sum_cut_card_le_oscillation (I : Finset α) (Y : ι → ℕ → ℕ)
    (first last : α → ℕ) {w : ℕ} (hw : 0 < w) :
    (∑ θ ∈ range w, (cut I Y first last w θ).card) ≤
      ∑ u ∈ I, ∑ i, oscillation (Y i) (first u) (last u) :=
  (sum_cut_card_le_capped I Y first last hw).trans
    (sum_le_sum fun _ _ => sum_le_sum fun _ _ => min_le_right _ _)

/-- Average payment retains the exact capped oscillation cost. -/
theorem average_cut_card_le_capped (I : Finset α) (Y : ι → ℕ → ℕ)
    (first last : α → ℕ) {w : ℕ} (hw : 0 < w) :
    (∑ θ ∈ range w, ((cut I Y first last w θ).card : ℝ)) / w ≤
      (∑ u ∈ I, ∑ i, (min w (oscillation (Y i) (first u) (last u)) : ℝ)) / w := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast sum_cut_card_le_capped I Y first last hw

theorem average_cut_card_le_oscillation (I : Finset α) (Y : ι → ℕ → ℕ)
    (first last : α → ℕ) {w : ℕ} (hw : 0 < w) :
    (∑ θ ∈ range w, ((cut I Y first last w θ).card : ℝ)) / w ≤
      (∑ u ∈ I, ∑ i, (oscillation (Y i) (first u) (last u) : ℝ)) / w := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast sum_cut_card_le_oscillation I Y first last hw

/-- Exact overlap-profile bound, before replacing multiplicities by a maximum. -/
theorem average_cut_card_le_profile (I : Finset α) (Y : ι → ℕ → ℕ)
    (first last : α → ℕ) {w : ℕ} (hw : 0 < w) (n : ℕ)
    (hfirst : ∀ u ∈ I, first u ≤ last u) (hlast : ∀ u ∈ I, last u ≤ n) :
    (∑ θ ∈ range w, ((cut I Y first last w θ).card : ℝ)) / w ≤
      (∑ e ∈ range n, (multiplicity I first last e : ℝ) *
        ∑ i, dist (Y i e : ℝ) (Y i (e + 1) : ℝ)) / w := by
  refine (average_cut_card_le_oscillation I Y first last hw).trans ?_
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ = ∑ i, ∑ u ∈ I, (oscillation (Y i) (first u) (last u) : ℝ) := sum_comm
    _ ≤ ∑ i, ∑ e ∈ range n, (multiplicity I first last e : ℝ) *
        dist (Y i e : ℝ) (Y i (e + 1) : ℝ) :=
      sum_le_sum fun i _ => sum_oscillation_le_profile I (Y i) first last n hfirst hlast
    _ = _ := by rw [sum_comm]; simp only [mul_sum]

/-- Uniform lifetime overlap times the total variation, divided by grid width. -/
theorem average_cut_card_le_mul_variation (I : Finset α) (Y : ι → ℕ → ℕ)
    (first last : α → ℕ) {w : ℕ} (hw : 0 < w) (n H : ℕ)
    (hfirst : ∀ u ∈ I, first u ≤ last u) (hlast : ∀ u ∈ I, last u ≤ n)
    (hH : ∀ e < n, multiplicity I first last e ≤ H) :
    (∑ θ ∈ range w, ((cut I Y first last w θ).card : ℝ)) / w ≤
      (H * ∑ i, variation (fun t => (Y i t : ℝ)) n) / w := by
  refine (average_cut_card_le_oscillation I Y first last hw).trans ?_
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ = ∑ i, ∑ u ∈ I, (oscillation (Y i) (first u) (last u) : ℝ) := sum_comm
    _ ≤ ∑ i, (H : ℝ) * variation (fun t => (Y i t : ℝ)) n :=
      sum_le_sum fun i _ => sum_oscillation_le_mul_variation
        I (Y i) first last n H hfirst hlast hH
    _ = _ := (mul_sum _ _ _).symm

/-- Some shift pays no more than any established bound on the average. -/
theorem exists_cut_card_le {I : Finset α} {Y : ι → ℕ → ℕ}
    {first last : α → ℕ} {w : ℕ} (hw : 0 < w) {B : ℝ}
    (hB : (∑ θ ∈ range w, ((cut I Y first last w θ).card : ℝ)) / w ≤ B) :
    ∃ θ < w, ((cut I Y first last w θ).card : ℝ) ≤ B := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  obtain ⟨θ, hθ, hle⟩ := exists_le_of_sum_le
    (show (range w).Nonempty from ⟨0, mem_range.mpr hw⟩)
    (show (∑ θ ∈ range w, ((cut I Y first last w θ).card : ℝ)) ≤
        ∑ _θ ∈ range w, B from by
      simpa only [sum_const, card_range, nsmul_eq_mul, mul_comm B] using
        (div_le_iff₀ hwR).mp hB)
  exact ⟨θ, mem_range.mp hθ, hle⟩

end LeanMachine.GridPayment

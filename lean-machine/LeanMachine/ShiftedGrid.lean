import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Max

/-! Exact averaging over all shifts of a grid on natural coordinates. -/

namespace LeanMachine.ShiftedGrid

open Finset

/-- Grid block containing `x`, with width `w` and shift `θ`. -/
def label (w θ x : ℕ) : ℕ := (x + θ) / w

/-- Shifts in one period that separate two coordinates. -/
def separatingShifts (w a b : ℕ) : Finset ℕ :=
  (range w).filter (fun θ => label w θ a ≠ label w θ b)

theorem label_mono (w θ : ℕ) : Monotone (label w θ) := by
  intro a b hab
  exact Nat.div_le_div_right (Nat.add_le_add_right hab θ)

theorem label_ne_iff (hw : 0 < w) (hab : a ≤ b) :
    label w θ a ≠ label w θ b ↔ w ≤ (a + θ) % w + (b - a) := by
  have he : b + θ = ((a + θ) % w + (b - a)) + (a + θ) / w * w := by
    have h := Nat.mod_add_div (a + θ) w
    rw [Nat.mul_comm w] at h
    omega
  unfold label
  rw [he, Nat.add_mul_div_right _ _ hw]
  have hz := Nat.div_eq_zero_iff (a := (a + θ) % w + (b - a)) (b := w)
  omega

/-- The separation count is exactly the diameter, capped at one period. -/
theorem separatingShifts_card (hw : 0 < w) (hab : a ≤ b) :
    (separatingShifts w a b).card = min w (b - a) := by
  have hcard : (separatingShifts w a b).card = (Ico (w - (b - a)) w).card := by
    apply card_bij (fun θ _ => (a + θ) % w)
    · intro θ hθ
      obtain ⟨hθ, hsep⟩ := mem_filter.mp hθ
      have hr := Nat.mod_lt (a + θ) hw
      have hsep' := (label_ne_iff hw hab).mp hsep
      exact mem_Ico.mpr ⟨by omega, hr⟩
    · intro θ hθ φ hφ he
      have hθ' := mem_range.mp (mem_filter.mp hθ).1
      have hφ' := mem_range.mp (mem_filter.mp hφ).1
      have := Nat.mod_injOn_Ico a w
        (mem_Ico.mpr (show a ≤ a + θ ∧ a + θ < a + w by omega))
        (mem_Ico.mpr (show a ≤ a + φ ∧ a + φ < a + w by omega)) he
      omega
    · intro r hr
      obtain ⟨hrlo, hrhi⟩ := mem_Ico.mp hr
      have hr' : r ∈ (Ico a (a + w)).image (· % w) := by
        rw [Nat.image_Ico_mod]; exact mem_range.mpr hrhi
      obtain ⟨z, hz, he⟩ := mem_image.mp hr'
      obtain ⟨hzlo, hzhi⟩ := mem_Ico.mp hz
      refine ⟨z - a, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, ?_⟩
      · apply (label_ne_iff hw hab).mpr
        have hz' : a + (z - a) = z := by omega
        rw [hz', he]
        omega
      · simpa only [Nat.add_sub_of_le hzlo] using he
  rw [hcard, Nat.card_Ico]
  omega

theorem separatingShifts_card_le (hw : 0 < w) (hab : a ≤ b) :
    (separatingShifts w a b).card ≤ b - a := by
  rw [separatingShifts_card hw hab]
  exact min_le_right _ _

/-- A monotone grid label is constant on a nonempty finite set exactly when
it agrees on the two extreme coordinates. -/
theorem constant_iff_extrema_eq {S : Finset ℕ} (hS : S.Nonempty) (w θ : ℕ) :
    (∀ x ∈ S, ∀ y ∈ S, label w θ x = label w θ y) ↔
      label w θ (S.min' hS) = label w θ (S.max' hS) := by
  constructor
  · intro h
    exact h _ (S.min'_mem hS) _ (S.max'_mem hS)
  · intro he x hx y hy
    have hlow (z) (hz : z ∈ S) := label_mono w θ (S.min'_le z hz)
    have hhigh (z) (hz : z ∈ S) := label_mono w θ (S.le_max' z hz)
    have := hlow x hx
    have := hhigh x hx
    have := hlow y hy
    have := hhigh y hy
    omega

theorem nonconstant_iff_extrema_ne {S : Finset ℕ} (hS : S.Nonempty) (w θ : ℕ) :
    (∃ x ∈ S, ∃ y ∈ S, label w θ x ≠ label w θ y) ↔
      label w θ (S.min' hS) ≠ label w θ (S.max' hS) := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩ he
    exact hxy ((constant_iff_extrema_eq hS w θ).mpr he x hx y hy)
  · intro he
    exact ⟨_, S.min'_mem hS, _, S.max'_mem hS, he⟩

/-- Shifts whose grid label is not constant on a finite set. -/
def nonconstantShifts (w : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (range w).filter (fun θ => ∃ x ∈ S, ∃ y ∈ S, label w θ x ≠ label w θ y)

/-- Exact capped-diameter count, including sets with holes or repeated extrema. -/
theorem nonconstantShifts_card (hw : 0 < w) {S : Finset ℕ} (hS : S.Nonempty) :
    (nonconstantShifts w S).card = min w (S.max' hS - S.min' hS) := by
  have he : nonconstantShifts w S = separatingShifts w (S.min' hS) (S.max' hS) := by
    ext θ
    simp only [nonconstantShifts, separatingShifts, mem_filter,
      nonconstant_iff_extrema_ne hS w θ]
  rw [he, separatingShifts_card hw (S.min'_le _ (S.max'_mem hS))]

theorem nonconstantShifts_card_le (hw : 0 < w) {S : Finset ℕ} (hS : S.Nonempty) :
    (nonconstantShifts w S).card ≤ S.max' hS - S.min' hS := by
  rw [nonconstantShifts_card hw hS]
  exact min_le_right _ _

/-- Coordinates with equal grid labels differ by less than one width. -/
theorem sub_lt_of_label_eq (hw : 0 < w) (h : label w θ a = label w θ b) :
    b - a < w := by
  by_cases hab : a ≤ b
  · have := not_iff_not.mpr (label_ne_iff (θ := θ) hw hab)
    simp only [not_not] at this
    have := this.mp h
    omega
  · omega

/-- A finite collection of distinct coordinates in one block has at most `w`
members; the initial block may be shorter because coordinates are natural. -/
theorem card_le_of_constant (hw : 0 < w) {S : Finset ℕ}
    (h : ∀ x ∈ S, ∀ y ∈ S, label w θ x = label w θ y) : S.card ≤ w := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  have hspan := sub_lt_of_label_eq hw ((constant_iff_extrema_eq hS w θ).mp h)
  have hsub : S ⊆ Icc (S.min' hS) (S.max' hS) := by
    intro x hx
    exact mem_Icc.mpr ⟨S.min'_le _ hx, S.le_max' _ hx⟩
  have hcard := card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have horder := S.min'_le _ (S.max'_mem hS)
  omega

end LeanMachine.ShiftedGrid

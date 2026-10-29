import LeanMachine.CircularSubdivision

set_option autoImplicit false

/-!
# Preserving raw-coordinate gaps under real subdivision

An increasing embedding places every original raw coordinate at the same
physical point of a finer subdivision. Its extra vertices may have arbitrary
real coordinates. The actual sorted gaps, including the seam, retain their
lengths and area; no area-preservation premise is assumed.
-/

namespace LeanMachine.CircularRefinement

open Finset CyclicSelection CircularSubdivision
open scoped BigOperators
noncomputable section

theorem image_subset_range {L N : ℕ} (φ : ℕ ↪o ℕ)
    (hφ : ∀ a < L, φ a < N) {S : Finset ℕ} (hSL : S ⊆ range L) :
    S.image φ ⊆ range N := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
  exact mem_range.mpr (hφ a (mem_range.mp (hSL ha)))

theorem point_image {L N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (φ : ℕ ↪o ℕ) {i : ℕ} (hi : i < S.card) :
    point N (S.image φ) (hS.image φ) i = φ (point L S hS i) := by
  have hcard : (S.image φ).card = S.card := card_image_of_injective S φ.injective
  have hsort : (fun j : Fin S.card => φ (S.orderEmbOfFin rfl j)) =
      (S.image φ).orderEmbOfFin hcard :=
    orderEmbOfFin_unique hcard
      (fun j => mem_image_of_mem φ (S.orderEmbOfFin_mem rfl j))
      (φ.strictMono.comp (S.orderEmbOfFin rfl).strictMono)
  have hi' : i < (S.image φ).card := by omega
  simp only [point, dite_eq_left hi', dite_eq_left hi]
  calc
    (S.image φ).orderEmbOfFin rfl ⟨i, hi'⟩ =
        (S.image φ).orderEmbOfFin hcard ⟨i, hi⟩ :=
      (orderEmbOfFin_eq_orderEmbOfFin_iff (h := rfl) (h' := hcard)).mpr rfl
    _ = _ := (congrFun hsort ⟨i, hi⟩).symm

theorem min_image {S : Finset ℕ} (hS : S.Nonempty) (φ : ℕ ↪o ℕ) :
    (S.image φ).min' (hS.image φ) = φ (S.min' hS) := by
  simpa only [point_zero] using point_image (L := 0) (N := 0) hS φ (card_pos.mpr hS)

/-- Sorted image anchors have precisely their original physical coordinates;
the final lifted anchor advances by the original circumference. -/
theorem coordinate_point_image {L N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) (φ : ℕ ↪o ℕ) {p : ℕ → ℝ}
    (hp : ∀ i, p (i + N) = p i + L)
    (hcoord : ∀ a < L, p (φ a) = (a : ℝ)) {i : ℕ} (hi : i ≤ S.card) :
    p (point N (S.image φ) (hS.image φ) i) = (point L S hS i : ℝ) := by
  by_cases hi' : i < S.card
  · rw [point_image (L := L) hS φ hi']
    exact hcoord _ (mem_range.mp (hSL (point_mem hS hi')))
  · have hieq : i = S.card := by omega
    have hcard : (S.image φ).card = S.card := card_image_of_injective S φ.injective
    rw [hieq, ← hcard, point_card, hcard, point_card, Nat.add_comm N, hp, min_image hS φ]
    rw [hcoord _ (mem_range.mp (hSL (S.min'_mem hS))), Nat.cast_add]
    ring

/-- Arbitrary extra real subdivision vertices preserve the original gap area. -/
theorem area_image_eq_pointArea {L N : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) (φ : ℕ ↪o ℕ) (hφ : ∀ a < L, φ a < N) {p : ℕ → ℝ}
    (hp : ∀ i, p (i + N) = p i + L)
    (hcoord : ∀ a < L, p (φ a) = (a : ℝ)) :
    WeightedCircularGap.area N (S.image φ) (hS.image φ) (edgeLength p) =
      GapErosion.pointArea (range S.card) (gap L S hS) L := by
  rw [area_eq_displacements hp (hS.image φ) (image_subset_range φ hφ hSL),
    card_image_of_injective S φ.injective]
  unfold GapErosion.pointArea
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [coordinate_point_image hS hSL φ hp hcoord (by have := mem_range.mp hi; omega),
    coordinate_point_image hS hSL φ hp hcoord (Nat.le_of_lt (mem_range.mp hi))]
  have hmono := point_mono hS hSL (Nat.le_succ i)
  rw [gap, Nat.cast_sub hmono]

end
end LeanMachine.CircularRefinement

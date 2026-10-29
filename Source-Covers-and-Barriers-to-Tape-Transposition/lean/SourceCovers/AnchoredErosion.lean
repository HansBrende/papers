import LeanMachine.AnchoredGapErosion
import LeanMachine.CircularSubdivision

set_option autoImplicit false

/-!
# Anchored erosion for real subdivisions and raw coordinates

The shared theorem uses a finite subdivision with arbitrary real elementary
lengths. The first adapter expresses its area in real lifted coordinates;
the second recovers the existing raw-coordinate gap area exactly.
-/

namespace SourceCovers

open Finset LeanMachine CyclicSelection WeightedCircularGap AnchoredCircularCover
open AnchoredGapErosion CircularSubdivision
open scoped BigOperators
noncomputable section

export LeanMachine.AnchoredGapErosion (penalty area_lower_bound area_lower_bound_linear)

variable {κ : Type*} {N : ℕ} {S₀ S : Finset ℕ}

/-- Real coordinate form, including the seam through the periodic lift. -/
theorem anchored_displacement_area_lower_bound
    (hS₀ : S₀.Nonempty) (hS₀N : S₀ ⊆ range N)
    (hS : S.Nonempty) (hSN : S ⊆ range N)
    (I : Finset κ) (start len : κ → ℕ)
    (hstart : ∀ i ∈ I, start i < N) (hlen : ∀ i ∈ I, len i ≤ N)
    (hanchor : ∀ i ∈ I, ∃ q ∈ S₀, q ∈ arc N (start i) (len i + 1))
    (hcover : S ⊆ S₀ ∪ coveredVertices N I start len)
    {L : ℝ} (hL : 0 < L) {p : ℕ → ℝ}
    (hp : ∀ i, p (i + N) = p i + L)
    (hmono : ∀ i < N, p i ≤ p (i + 1)) {E : ℝ}
    (hE : coveredLength N (edgeLength p) I start len ≤ E) :
    (∑ i ∈ range S₀.card,
        (p (point N S₀ hS₀ (i + 1)) - p (point N S₀ hS₀ i)) ^ 2) / (2 * L ^ 2) -
      penalty (min (E / L) 1) ≤
    (∑ i ∈ range S.card,
        (p (point N S hS (i + 1)) - p (point N S hS i)) ^ 2) / (2 * L ^ 2) := by
  have htotal : circumference N (edgeLength p) = L := total_length hp
  have h := area_lower_bound (w := edgeLength p)
    hS₀ hS₀N hS hSN I start len hstart hlen hanchor hcover
    (fun i hi => sub_nonneg.mpr (hmono i hi)) (by rwa [htotal]) hE
  rwa [area_eq_displacements hp hS₀ hS₀N, area_eq_displacements hp hS hSN, htotal] at h

/-- Integer raw coordinates are the unit-length specialization, with exactly
the gap-area definition used by the fractional-cover and freezing theorems. -/
theorem anchored_point_area_lower_bound
    (hS₀ : S₀.Nonempty) (hS₀N : S₀ ⊆ range N)
    (hS : S.Nonempty) (hSN : S ⊆ range N)
    (I : Finset κ) (start len : κ → ℕ)
    (hstart : ∀ i ∈ I, start i < N) (hlen : ∀ i ∈ I, len i ≤ N)
    (hanchor : ∀ i ∈ I, ∃ q ∈ S₀, q ∈ arc N (start i) (len i + 1))
    (hcover : S ⊆ S₀ ∪ coveredVertices N I start len) {E : ℝ}
    (hE : ((coveredEdges N I start len).card : ℝ) ≤ E) :
    GapErosion.pointArea (range S₀.card) (gap N S₀ hS₀) N -
      penalty (min (E / (N : ℝ)) 1) ≤
    GapErosion.pointArea (range S.card) (gap N S hS) N := by
  have htotal : circumference N (fun _ => (1 : ℝ)) = N := by simp [circumference]
  have hpaid : coveredLength N (fun _ => (1 : ℝ)) I start len ≤ E := by
    simpa [coveredLength] using hE
  have h := area_lower_bound (w := fun _ => (1 : ℝ))
    hS₀ hS₀N hS hSN I start len hstart hlen hanchor hcover
    (fun _ _ => zero_le_one) (by rw [htotal]; exact_mod_cast cycle_pos hS₀ hS₀N) hpaid
  rwa [area_one hS₀ hS₀N, area_one hS hSN, htotal] at h

end
end SourceCovers

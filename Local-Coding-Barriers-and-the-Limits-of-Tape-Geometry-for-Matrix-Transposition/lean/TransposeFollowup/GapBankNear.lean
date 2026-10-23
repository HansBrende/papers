import TransposeFollowup.GapBankBuckets

/-! Counting near coordinates by the row ball of each stored coordinate.
The ball hypothesis is separate from the interval arithmetic, so the latter
is shared by any graph-based grouping. -/

namespace TransposeFollowup.RowBuckets

open Classical
open scoped BigOperators
set_option autoImplicit false

variable {d M : ℕ} (B : RowBuckets d M)

def nearColumns (sigma : ℕ) (rows : Fin d → Finset (Fin d)) (r : Fin d) : Finset (Fin d) :=
  (rows r).biUnion (fun i => B.paddedFiber sigma (B.bucket i))

@[simp] theorem mem_nearColumns (sigma : ℕ) (rows : Fin d → Finset (Fin d))
    (r c : Fin d) : c ∈ B.nearColumns sigma rows r ↔
      ∃ i ∈ rows r, ∃ j ∈ columnWindow sigma c, B.bucket j = B.bucket i := by
  simp [nearColumns]

theorem nearColumns_card (sigma L nu : ℕ) (rows : Fin d → Finset (Fin d))
    (hrows : ∀ r, (rows r).card ≤ nu)
    (hpad : ∀ a, (B.paddedFiber sigma a).card ≤ L + 2 * sigma) (r : Fin d) :
    (B.nearColumns sigma rows r).card ≤ nu * (L + 2 * sigma) := by
  calc (B.nearColumns sigma rows r).card
      ≤ ∑ i ∈ rows r, (B.paddedFiber sigma (B.bucket i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ rows r, (L + 2 * sigma) := Finset.sum_le_sum (fun i _ => hpad (B.bucket i))
    _ = (rows r).card * (L + 2 * sigma) := by simp
    _ ≤ nu * (L + 2 * sigma) := Nat.mul_le_mul_right _ (hrows r)

def nearCoordinates (b sigma : ℕ) (rows : Fin d → Finset (Fin d)) : Finset (MatrixBit d b) :=
  Finset.univ.biUnion (fun r =>
    ((B.nearColumns sigma rows r).product Finset.univ).image (fun ct => (r,ct)))

@[simp] theorem mem_nearCoordinates (b sigma : ℕ) (rows : Fin d → Finset (Fin d))
    (v : MatrixBit d b) : v ∈ B.nearCoordinates b sigma rows ↔
      ∃ i ∈ rows v.1, ∃ j ∈ columnWindow sigma v.2.1, B.bucket j = B.bucket i := by
  rcases v with ⟨r,c,t⟩
  simp [nearCoordinates]

theorem nearCoordinates_card (b sigma L nu : ℕ) (rows : Fin d → Finset (Fin d))
    (hrows : ∀ r, (rows r).card ≤ nu)
    (hpad : ∀ a, (B.paddedFiber sigma a).card ≤ L + 2 * sigma) :
    (B.nearCoordinates b sigma rows).card ≤ d * b * nu * (L + 2 * sigma) := by
  calc (B.nearCoordinates b sigma rows).card
      ≤ ∑ r : Fin d, (((B.nearColumns sigma rows r).product (Finset.univ : Finset (Fin b))).image
        (fun ct => (r,ct))).card := Finset.card_biUnion_le
    _ ≤ ∑ r : Fin d, ((B.nearColumns sigma rows r).card * b) := by
      apply Finset.sum_le_sum
      intro r _
      simpa using (Finset.card_image_le (s := (B.nearColumns sigma rows r).product
        (Finset.univ : Finset (Fin b))) (f := fun ct => (r,ct)))
    _ ≤ ∑ _r : Fin d, nu * (L + 2 * sigma) * b := by
      apply Finset.sum_le_sum
      intro r _
      exact Nat.mul_le_mul_right b (B.nearColumns_card sigma L nu rows hrows hpad r)
    _ = d * b * nu * (L + 2 * sigma) := by simp; ring

end TransposeFollowup.RowBuckets

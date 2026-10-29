import LeanMachine.CyclicGapTails
import LeanMachine.CircularRefinement

/-! Exact scaling of actual sorted circular gaps and their normalized area. -/

namespace LeanMachine.CyclicSelection

open Finset
open scoped BigOperators Classical
noncomputable section

def scaleEmbedding (a : ℕ) (ha : 0 < a) : ℕ ↪o ℕ :=
  OrderEmbedding.ofStrictMono (fun x => a * x) (fun _ _ h => Nat.mul_lt_mul_of_pos_left h ha)

theorem point_scaled {N a : ℕ} (ha : 0 < a) {S : Finset ℕ} (hS : S.Nonempty)
    (i : ℕ) : point (a * N) (S.image (a * ·)) (hS.image (a * ·)) i =
      a * point N S hS i := by
  let φ := scaleEmbedding a ha
  have hcard : (S.image (a * ·)).card = S.card := card_image_of_injective S φ.injective
  by_cases hi : i < S.card
  · exact CircularRefinement.point_image hS φ hi
  · have hi' : ¬i < (S.image (a * ·)).card := by rwa [hcard]
    simp only [point, dite_eq_right hi, dite_eq_right hi']
    rw [show (S.image (a * ·)).min' (hS.image (a * ·)) = a * S.min' hS from
      CircularRefinement.min_image hS φ]
    ring

theorem gap_scaled {N a : ℕ} (ha : 0 < a) {S : Finset ℕ} (hS : S.Nonempty)
    (i : ℕ) : gap (a * N) (S.image (a * ·)) (hS.image (a * ·)) i =
      a * gap N S hS i := by
  simp only [gap, point_scaled ha hS, Nat.mul_sub_left_distrib]

theorem pointGapArea_scaled {N a : ℕ} (ha : 0 < a) (S : Finset ℕ) :
    pointGapArea (a * N) (S.image (a * ·)) = pointGapArea N S := by
  by_cases hS : S.Nonempty
  · have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    have hcard : (S.image (a * ·)).card = S.card :=
      card_image_of_injective S (scaleEmbedding a ha).injective
    rw [pointGapArea_eq (hS.image (a * ·)), pointGapArea_eq hS]
    simp only [GapErosion.pointArea, hcard, gap_scaled ha hS, Nat.cast_mul,
      mul_pow, ← mul_sum]
    field_simp
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    simp [he, pointGapArea, squareGapSum]

end
end LeanMachine.CyclicSelection

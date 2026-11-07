import TapeStorageRates.Conditioning
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finiteness

/-! # Storage fibres on the original source alphabet

An injective alphabet embedding followed by a square matrix with nonzero
diagonal is an index encoder for its off-diagonal support. Counting values
in the matrix's range pays its rank, without choosing a row basis.
-/

namespace TapeStorageRates

open Finset DirectedRecovery MotionDepthCodes

set_option autoImplicit false
noncomputable section

variable {V K A : Type*} [Fintype V] [DecidableEq V] [Field K]

open Classical in
/-- The permitted helpers are exactly the nonzero off-diagonal entries. -/
def matrixHelpers (H : Matrix V V K) (v : V) : Finset V :=
  univ.filter fun u => u ≠ v ∧ H v u ≠ 0

/-- The full check vector; its image size depends on rank, not its displayed length. -/
def matrixSyndrome (H : Matrix V V K) (e : A → K) (x : V → A) : V → K :=
  H.mulVec (e ∘ x)

/-- Nonzero diagonal, rather than diagonal one, suffices. The source
alphabet need only embed injectively in the field. -/
theorem matrixSyndrome_isIndexCode (H : Matrix V V K) (e : A → K)
    (he : Function.Injective e) (hd : ∀ v, H v v ≠ 0) :
    IsIndexCode (matrixHelpers H) (matrixSyndrome H e) := by
  classical
  intro x y hxy v hhelp
  apply he
  have hoff : ∑ u ∈ univ.erase v, H v u * e (x u) =
      ∑ u ∈ univ.erase v, H v u * e (y u) := by
    apply sum_congr rfl
    intro u hu
    by_cases hzero : H v u = 0
    · simp [hzero]
    · rw [hhelp u (mem_filter.mpr ⟨mem_univ _, (mem_erase.mp hu).1, hzero⟩)]
  have hrow := congrFun hxy v
  change (∑ u, H v u * e (x u)) = ∑ u, H v u * e (y u) at hrow
  rw [← sum_erase_add _ _ (mem_univ v), ← sum_erase_add _ _ (mem_univ v), hoff] at hrow
  exact mul_left_cancel₀ (hd v) (add_left_cancel hrow)

/-- Every syndrome fibre is a storage code on precisely the same coordinates
and permitted helper relation. -/
theorem matrixSyndrome_fibre_storage [Fintype A] (H : Matrix V V K) (e : A → K)
    (he : Function.Injective e) (hd : ∀ v, H v v ≠ 0) (y : V → K) :
    IsStorageCode (matrixHelpers H) (indexFiber (matrixSyndrome H e) y) :=
  isStorageCode_indexFiber (matrixSyndrome_isIndexCode H e he hd) y

open Classical in
/-- Only values in the linear range occur, even on an arbitrary source subset. -/
theorem matrixSyndrome_image_card_le [Fintype K]
    (H : Matrix V V K) (e : A → K) (S : Finset (V → A)) :
    (S.image (matrixSyndrome H e)).card ≤ Fintype.card K ^ H.rank := by
  classical
  let f : (V → A) → LinearMap.range H.mulVecLin :=
    fun x => ⟨matrixSyndrome H e x, ⟨e ∘ x, rfl⟩⟩
  have himage : S.image (matrixSyndrome H e) = (S.image f).image Subtype.val := by
    rw [image_image]
    rfl
  rw [himage]
  calc
    _ ≤ (S.image f).card := card_image_le
    _ ≤ Fintype.card (LinearMap.range H.mulVecLin) := card_le_univ _
    _ = Fintype.card K ^ H.rank := Module.card_eq_pow_finrank

/-- Pigeonholing the rank-sized label alphabet gives a genuine nonempty
storage fibre. The integer inequality avoids rounding or positivity losses. -/
theorem matrixSyndrome_exists_large_fibre [Fintype K] [Fintype A] [Nonempty A]
    (H : Matrix V V K) (e : A → K) (he : Function.Injective e)
    (hd : ∀ v, H v v ≠ 0) :
    ∃ y, (indexFiber (matrixSyndrome H e) y).Nonempty ∧
      IsStorageCode (matrixHelpers H) (indexFiber (matrixSyndrome H e) y) ∧
      Fintype.card A ^ Fintype.card V ≤
        Fintype.card K ^ H.rank * (indexFiber (matrixSyndrome H e) y).card := by
  classical
  obtain ⟨y, hy, hcard⟩ := exists_large_observation_fibre
    (S := (univ : Finset (V → A))) univ_nonempty (matrixSyndrome H e)
  obtain ⟨x, _, hx⟩ := mem_image.mp hy
  refine ⟨y, ⟨x, (mem_indexFiber _ _ _).mpr hx⟩,
    matrixSyndrome_fibre_storage H e he hd y, ?_⟩
  have hlarge : Fintype.card A ^ Fintype.card V ≤
      (univ.image (matrixSyndrome H e)).card *
        (indexFiber (matrixSyndrome H e) y).card := by
    have hF : (univ.filter (fun x : V → A => matrixSyndrome H e x = y)).card =
        (indexFiber (matrixSyndrome H e) y).card := by
      congr 1
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_indexFiber]
    rw [hF] at hcard
    simpa only [card_univ, Fintype.card_fun] using hcard
  exact hlarge.trans
    (Nat.mul_le_mul_right _ (matrixSyndrome_image_card_le H e univ))

end
end TapeStorageRates

import TransposeFollowup.PacketCollisionCube
import TransposeFollowup.RecodedPackets

/-! The unchanged exact distance inequality for arbitrary fixed Boolean
functions of at most two independently recoded coordinates. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

namespace RecodedPacketCode

variable {n b B : ℕ} (C : RecodedPacketCode n b B)

theorem small_component_count_le_near (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) (ell : ℕ) :
    (C.system.smallComponents ell).card ≤ (RecodedXorCode.nearBits (b := b) G ell).card := by
  classical
  let U := C.system.smallComponents ell
  have hU : U ⊆ C.system.deficient := Finset.filter_subset _ _
  apply C.system.choiceInput_image_bound U hU
    (fun z => matrixBits (C.transformedEquiv.symm z))
    (fun _ _ h => C.transformedEquiv.symm.injective (matrixBits_injective n b h))
  intro S hS K v hv
  have hSd : S ∈ C.system.deficient := hU hS
  have hSc := ((C.system.mem_deficient S).mp hSd).1
  have hsize : S.card ≤ ell := (Finset.mem_filter.mp hS).2
  apply C.same_broadcast_outside_square hc
    (z := C.system.choiceInput U hU (insert S K)) (z' := C.system.choiceInput U hU K)
    (fun w hw => C.system.choiceInput_insert_outside U hU K hS hw)
    (C.system.choiceInput_broadcast U hU (insert S K) K)
  by_contra h
  push Not at h
  exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    C.component_rows_near G hG hSc ell hsize h.1 h.2⟩)

/-- All-input distance theorem with every occurrence counted, including
empty-support, unary, constant-valued and repeated packets. Nearness uses
walk length strictly below ell, and disconnected pairs never count. -/
theorem broadcast_lower_bound_scaled (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) (ell : ℕ) :
    (ell + 1) * (n * n * b) ≤ (ell + 1) * B + n * n * b +
      ell * (RecodedXorCode.nearBits (b := b) G ell).card := by
  have hcoord := C.system.coordinate_count_le_broadcast_add_deficient
  have hsize := C.system.deficient_size_bound ell
  have hsmall := C.small_component_count_le_near hc G hG ell
  simp only [MatrixBit, Fintype.card_prod, Fintype.card_fin, ← Nat.mul_assoc] at hcoord hsize
  have hmul := Nat.mul_le_mul_left (ell + 1) hcoord
  have hmulSmall := Nat.mul_le_mul_left ell hsmall
  nlinarith

theorem broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) (ell : ℕ) :
    (B : ℝ) ≥ (n * n * b : ℕ) -
      (((n * n * b : ℕ) : ℝ) + ell * (RecodedXorCode.nearBits (b := b) G ell).card) / (ell + 1) := by
  have hs : ((ell : ℝ) + 1) * (n * n * b : ℕ) ≤
      ((ell : ℝ) + 1) * B + (n * n * b : ℕ) +
        ell * (RecodedXorCode.nearBits (b := b) G ell).card := by
    exact_mod_cast C.broadcast_lower_bound_scaled hc G hG ell
  have hd : 0 < (ell : ℝ) + 1 := by positivity
  have hdiv : ((n * n * b : ℕ) : ℝ) - B ≤
      (((n * n * b : ℕ) : ℝ) + ell * (RecodedXorCode.nearBits (b := b) G ell).card) / (ell + 1) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  linarith

end RecodedPacketCode
end TransposeFollowup

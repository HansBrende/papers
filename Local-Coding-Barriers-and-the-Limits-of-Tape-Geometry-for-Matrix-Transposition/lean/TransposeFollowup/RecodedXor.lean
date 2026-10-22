import TransposeFollowup.BitFlips
import TransposeFollowup.MatrixView

/-! The exact static recoded-XOR interface. Each row has exactly nb independent
transformed bits under an arbitrary bijection. All inputs must be decoded from
the receiver's own raw row and the complete fixed broadcast. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

def rowRecodingEquiv {n b : ℕ} (A : (i : Fin n) → Row n b ≃ Row n b) :
    FiniteMatrix n b ≃ (MatrixBit n b → Bool) where
  toFun x := fun v => A v.1 (x v.1) v.2.1 v.2.2
  invFun z := fun i => (A i).symm (fun j t => z (i, (j, t)))
  left_inv x := by funext i; exact (A i).symm_apply_apply (x i)
  right_inv z := by
    funext v
    exact congrFun (congrFun ((A v.1).apply_symm_apply (fun j t => z (v.1, (j, t)))) v.2.1) v.2.2

structure RecodedXorCode (n b B : ℕ) where
  recode : (i : Fin n) → Row n b ≃ Row n b
  system : XorSystem (MatrixBit n b) B
  decode : Fin n → Row n b → (Fin B → Bool) → Row n b

namespace RecodedXorCode

variable {n b B : ℕ} (C : RecodedXorCode n b B)

def transformedEquiv : FiniteMatrix n b ≃ (MatrixBit n b → Bool) := rowRecodingEquiv C.recode

def broadcast (x : FiniteMatrix n b) : Fin B → Bool := C.system.broadcast (C.transformedEquiv x)

def Correct : Prop := ∀ x j, C.decode j (x j) (C.broadcast x) = transposed x j

/-- Only XOR packet endpoints are constrained. Same-row endpoints, including
self-XORs, are permitted independently of the loopless row-support graph. -/
def LocalTo (G : SimpleGraph (Fin n)) : Prop :=
  ∀ k v w, C.system.packet k = .pair v w → v.1 = w.1 ∨ G.Adj v.1 w.1

noncomputable def flip (S : Finset (MatrixBit n b)) (x : FiniteMatrix n b) : FiniteMatrix n b :=
  C.transformedEquiv.symm (toggleBits S (C.transformedEquiv x))

noncomputable def rowsOf (S : Finset (MatrixBit n b)) : Finset (Fin n) := S.image Prod.fst

theorem flip_row_unchanged (S : Finset (MatrixBit n b)) (x : FiniteMatrix n b)
    (i : Fin n) (hi : i ∉ rowsOf S) : C.flip S x i = x i := by
  have hbits (j : Fin n) (t : Fin b) : (i, (j, t)) ∉ S := by
    intro h
    exact hi (Finset.mem_image_of_mem Prod.fst h)
  have he : (fun j t => toggleBits S (C.transformedEquiv x) (i, (j, t))) =
      (C.recode i) (x i) := by
    funext j t
    simp [toggleBits, hbits j t, transformedEquiv, rowRecodingEquiv]
  change (C.recode i).symm _ = x i
  rw [he]
  exact (C.recode i).symm_apply_apply (x i)

theorem flip_broadcast {S : Finset (MatrixBit n b)} (hS : S ∈ C.system.unanchored)
    (x : FiniteMatrix n b) : C.broadcast (C.flip S x) = C.broadcast x := by
  change C.system.broadcast (C.transformedEquiv (C.transformedEquiv.symm _)) = _
  rw [C.transformedEquiv.apply_symm_apply]
  exact C.system.broadcast_toggle_component hS _

theorem column_eq_of_same_view (hc : C.Correct) {x y : FiniteMatrix n b}
    (hm : C.broadcast x = C.broadcast y) (j : Fin n) (hr : x j = y j) :
    transposed x j = transposed y j := by
  rw [← hc x j, ← hc y j, hm, hr]

/-- An unanchored component flip can change raw coordinates only in the square
of its represented row set. This holds at every basepoint even when the row
bijections are nonlinear; no raw linear-kernel claim is used. -/
theorem flip_outside_square (hc : C.Correct) {S : Finset (MatrixBit n b)}
    (hS : S ∈ C.system.unanchored) (x : FiniteMatrix n b) (v : MatrixBit n b)
    (hv : v.1 ∉ rowsOf S ∨ v.2.1 ∉ rowsOf S) :
    matrixBits (C.flip S x) v = matrixBits x v := by
  rcases hv with hi | hj
  · exact congrFun (congrFun (C.flip_row_unchanged S x v.1 hi) v.2.1) v.2.2
  · have hcol := C.column_eq_of_same_view hc (C.flip_broadcast hS x) v.2.1
      (C.flip_row_unchanged S x v.2.1 hj)
    have he := congrFun (congrFun hcol v.1) v.2.2
    simpa only [transposed_apply, matrixBits] using he

@[simp] theorem flip_empty (x : FiniteMatrix n b) : C.flip ∅ x = x := by
  simp [flip]

theorem flip_union (S T : Finset (MatrixBit n b)) (h : Disjoint S T)
    (x : FiniteMatrix n b) : C.flip (S ∪ T) x = C.flip S (C.flip T x) := by
  simp only [flip, C.transformedEquiv.apply_symm_apply]
  exact congrArg C.transformedEquiv.symm (toggleBits_union S T h (C.transformedEquiv x))

theorem flip_set_injective (x : FiniteMatrix n b) : Function.Injective (fun S => C.flip S x) := by
  intro S T h
  apply toggleBits_set_injective (C.transformedEquiv x)
  exact C.transformedEquiv.symm.injective h

end RecodedXorCode
end TransposeFollowup

import TransposeFollowup.ProtocolRectangle

/-! The leaf inequality for an actual nonlinear adaptive original-row code.
This is the local input to the remaining expected-cost aggregation. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

def internalFreeBits {n b : ℕ} {κ : Type*} [DecidableEq κ]
    (S : Finset (Fin n)) (component : Fin n → κ) : Finset (MatrixBit n b) :=
  internalCoordinates (bitOwner S component) (bitDemander S component) \ separatorBits S

/-- Full leaf inequality. The law on the correct subfamily may be arbitrary;
the virtual fiber need not have the correct helper or decode on other inputs.
The separator assignment and support partition are fixed only at this leaf. -/
theorem RowCode.separator_leaf_entropy {n b : ℕ} {H Ω κ : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype κ] [DecidableEq κ]
    (C : RowCode n b H) (F : Set (FiniteMatrix n b)) (hc : C.CorrectOn F)
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → FiniteMatrix n b) (hF : ∀ x, X x ∈ F)
    (z : H) (m : List Bool) (S : Finset (Fin n)) (component : Fin n → κ)
    (base : FiniteMatrix n b) (hb : (C.protocol z).run base = m)
    (hs : (C.protocol z).Along (PublicProtocol.Separated S component) m)
    (hz : ∀ x, C.helper (X x) = z) (hm : ∀ x, C.transcript (X x) = m)
    (hfix : ∀ x i, i ∈ S → X x i = base i) :
    2 * observationEntropy p (fun x => matrixBits (X x)) ≤
      Real.log ((protocolFiberBits (C.protocol z) m S base).card : ℝ) +
        ((internalFreeBits (b := b) S component).card : ℝ) * Real.log 2 := by
  classical
  have hXR : ∀ x, matrixBits (X x) ∈ protocolFiberBits (C.protocol z) m S base := by
    intro x
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, hfix x⟩
    simpa only [bitsMatrix_matrixBits, RowCode.transcript, hz x] using hm x
  have hdec := C.group_decoding F hc X hF
    (fun x y => (hz x).trans (hz y).symm) (fun x y => (hm x).trans (hm y).symm) S component
  have h := rectangle_decoding_entropy p hp hp1 (fun x => matrixBits (X x))
    (bitOwner S component) (bitDemander S component)
    (protocolFiberBits (C.protocol z) m S base)
    (protocolFiberBits_rectangle (C.protocol z) m S component base hb hs) hXR hdec
  have hconst : ∀ x y i, i ∈ separatorBits (b := b) S →
      matrixBits (X x) i = matrixBits (X y) i := by
    intro x y i hi
    have his := (Finset.mem_filter.mp hi).2
    exact congrFun (congrFun ((hfix x i.1 his).trans (hfix y i.1 his).symm) i.2.1) i.2.2
  rw [coordinateEntropy_remove_fixed p hp _ _ (separatorBits S) hconst] at h
  exact h.trans (add_le_add le_rfl (coordinateEntropy_le_card p hp hp1 _ _))

/-- Counting form for a uniformly chosen, injectively represented correct
leaf family. All entropy and rectangularity premises are derived above. -/
theorem RowCode.separator_leaf_log_card {n b : ℕ} {H Ω κ : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype κ] [DecidableEq κ]
    (C : RowCode n b H) (F : Set (FiniteMatrix n b)) (hc : C.CorrectOn F)
    (X : Ω → FiniteMatrix n b) (hX : Function.Injective X) (hF : ∀ x, X x ∈ F)
    (z : H) (m : List Bool) (S : Finset (Fin n)) (component : Fin n → κ)
    (base : FiniteMatrix n b) (hb : (C.protocol z).run base = m)
    (hs : (C.protocol z).Along (PublicProtocol.Separated S component) m)
    (hz : ∀ x, C.helper (X x) = z) (hm : ∀ x, C.transcript (X x) = m)
    (hfix : ∀ x i, i ∈ S → X x i = base i) :
    2 * Real.log (Fintype.card Ω : ℝ) ≤
      Real.log ((protocolFiberBits (C.protocol z) m S base).card : ℝ) +
        ((internalFreeBits (b := b) S component).card : ℝ) * Real.log 2 := by
  have h := C.separator_leaf_entropy F hc (uniformWeight Ω)
    (uniformWeight_nonneg Ω) (sum_uniformWeight Ω) X hF z m S component base hb hs hz hm hfix
  rw [observationEntropy_injective _ (uniformWeight_nonneg Ω) (fun x => matrixBits (X x))
    ((matrixBits_injective n b).comp hX), entropy_uniformWeight] at h
  exact h

end TransposeFollowup

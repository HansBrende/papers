import TransposeFollowup.SeparatorLeaf

/-! Exact conversion of the leaf loss to `b * sum |component|^2`. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

def componentRows {n : ℕ} {κ : Type*} [DecidableEq κ]
    (S : Finset (Fin n)) (component : Fin n → κ) (a : κ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i ∉ S ∧ component i = a)

theorem mem_internalFreeBits {n b : ℕ} {κ : Type*} [DecidableEq κ]
    (S : Finset (Fin n)) (component : Fin n → κ) (i : MatrixBit n b) :
    i ∈ internalFreeBits S component ↔
      i.1 ∉ S ∧ i.2.1 ∉ S ∧ component i.1 = component i.2.1 := by
  simp only [internalFreeBits, Finset.mem_sdiff, internalCoordinates, separatorBits,
    Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hr : i.1 ∈ S <;> by_cases hc : i.2.1 ∈ S <;>
    simp [bitOwner, bitDemander, rowGroup, hr, hc]

def internalFreeBitsEquiv {n b : ℕ} {κ : Type*} [DecidableEq κ]
    (S : Finset (Fin n)) (component : Fin n → κ) :
    (internalFreeBits (b := b) S component) ≃
      Σ a : κ, (componentRows S component a) × ((componentRows S component a) × Fin b) where
  toFun x := by
    have hx := (mem_internalFreeBits S component x.val).mp x.property
    refine ⟨component x.val.1, ⟨x.val.1, ?_⟩, ⟨x.val.2.1, ?_⟩, x.val.2.2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.1, rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2.1, hx.2.2.symm⟩
  invFun y := by
    have hr := (Finset.mem_filter.mp y.2.1.property).2
    have hc := (Finset.mem_filter.mp y.2.2.1.property).2
    refine ⟨(y.2.1.val, (y.2.2.1.val, y.2.2.2)), ?_⟩
    exact (mem_internalFreeBits S component _).mpr ⟨hr.1, hc.1, hr.2.trans hc.2.symm⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv y := by
    rcases y with ⟨a, ⟨i, hi⟩, ⟨j, hj⟩, t⟩
    have hia := (Finset.mem_filter.mp hi).2.2
    dsimp only
    subst a
    rfl

theorem card_internalFreeBits {n b : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : Finset (Fin n)) (component : Fin n → κ) :
    (internalFreeBits (b := b) S component).card =
      b * ∑ a, (componentRows S component a).card ^ 2 := by
  have h := Fintype.card_congr (internalFreeBitsEquiv (b := b) S component)
  simp only [Fintype.card_coe, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_fin] at h
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The exact leaf bound in the manuscript's component-size form. Empty
separators and empty component blocks are included. Logarithms are natural;
division by `log 2` gives the statement in bits. -/
theorem RowCode.separator_leaf_bound {n b : ℕ} {H Ω κ : Type*}
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
        (b * ∑ a, (componentRows S component a).card ^ 2 : ℕ) * Real.log 2 := by
  simpa only [card_internalFreeBits] using
    C.separator_leaf_log_card F hc X hX hF z m S component base hb hs hz hm hfix

end TransposeFollowup

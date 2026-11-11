import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

/-! An actual surjective semilinear-covariant decoder with unequal fibres.
The exact counts are proved over every finite field; the F₈ example follows
without enumerating field elements or assuming their distribution. -/

namespace SharedDecoders

open Classical

variable {E : Type*} [Field E]

def ratioDecoder (x : E × E × E) : E := x.2.1 / x.1

theorem ratioDecoder_surjective : Function.Surjective (ratioDecoder (E := E)) := by
  intro z
  exact ⟨(1, z, 0), by simp [ratioDecoder]⟩

/-- Every common nonzero multiplier cancels, including on the zero branch. -/
theorem ratioDecoder_semilinear (φ : E ≃+* E) (μ : E) (hμ : μ ≠ 0)
    (x : E × E × E) :
    ratioDecoder (μ * φ x.1, μ * φ x.2.1, μ * φ x.2.2) = φ (ratioDecoder x) := by
  simp only [ratioDecoder, mul_div_mul_left _ _ hμ, map_div₀]

noncomputable def ratioNonzeroFiberEquiv (z : E) (hz : z ≠ 0) :
    {x : E × E × E // ratioDecoder x = z} ≃ ({a : E // a ≠ 0} × E) where
  toFun x := (⟨x.1.1, by
    intro h
    have he := x.2
    simp only [ratioDecoder, h, div_zero] at he
    exact hz he.symm⟩, x.1.2.2)
  invFun y := ⟨(y.1.1, z * y.1.1, y.2), by simp [ratioDecoder, y.1.2]⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply Prod.ext
    swap
    · rfl
    exact ((div_eq_iff (by
      intro h
      have he := x.2
      simp only [ratioDecoder, h, div_zero] at he
      exact hz he.symm)).mp x.2).symm
  right_inv _ := rfl

noncomputable def ratioZeroFiberEquiv :
    {x : E × E × E // ratioDecoder x = 0} ≃ ((E ⊕ {a : E // a ≠ 0}) × E) where
  toFun x := (if h : x.1.1 = 0 then Sum.inl x.1.2.1 else Sum.inr ⟨x.1.1, h⟩,
    x.1.2.2)
  invFun y := match y.1 with
    | Sum.inl a => ⟨(0, a, y.2), by simp [ratioDecoder]⟩
    | Sum.inr a => ⟨(a.1, 0, y.2), by simp [ratioDecoder]⟩
  left_inv x := by
    apply Subtype.ext
    dsimp
    split_ifs with h
    · exact Prod.ext h.symm (Prod.ext rfl rfl)
    · have hx : x.1.2.1 = 0 := (div_eq_zero_iff.mp x.2).resolve_right h
      exact Prod.ext rfl (Prod.ext hx.symm rfl)
  right_inv y := by
    rcases y with ⟨a, c⟩
    rcases a with a | a
    · simp
    · simp [a.2]

theorem ratio_nonzero_fiber_card [Fintype E] (z : E) (hz : z ≠ 0) :
    Fintype.card {x : E × E × E // ratioDecoder x = z} =
      (Fintype.card E - 1) * Fintype.card E := by
  rw [Fintype.card_congr (ratioNonzeroFiberEquiv z hz), Fintype.card_prod,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq]

theorem ratio_zero_fiber_card [Fintype E] :
    Fintype.card {x : E × E × E // ratioDecoder x = 0} =
      Fintype.card E ^ 2 + (Fintype.card E - 1) * Fintype.card E := by
  rw [Fintype.card_congr (ratioZeroFiberEquiv (E := E)), Fintype.card_prod,
    Fintype.card_sum, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  ring

theorem ratio_eight_fiber_cards [Fintype E] (hE : Fintype.card E = 8) :
    (∀ z : E, z ≠ 0 → Fintype.card {x : E × E × E // ratioDecoder x = z} = 56) ∧
      Fintype.card {x : E × E × E // ratioDecoder x = 0} = 120 := by
  constructor
  · intro z hz
    rw [ratio_nonzero_fiber_card z hz, hE]
  · rw [ratio_zero_fiber_card, hE]
    norm_num

end SharedDecoders

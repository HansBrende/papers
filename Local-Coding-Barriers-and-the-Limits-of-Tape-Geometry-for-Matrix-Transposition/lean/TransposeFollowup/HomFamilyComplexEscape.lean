import TransposeFollowup.RationalComplexEscape

/-! Transfer the rational-family escape theorem through any group
homomorphism, retaining actual membership in the same real A^4. -/
namespace TransposeFollowup.RationalFreePair
open Classical Matrix Set RealMobius
open scoped Pointwise commutatorElement
set_option autoImplicit false
local notation "CM" => Matrix (Fin 2) (Fin 2) ℂ

theorem hom_family_complex_escape {Γ : Type*} [_root_.Group Γ]
    (f : Γ →* RealMobius.Group) {D : ℕ} (hD : 0 < D)
    {A : Set RealMobius.Group} (hA1 : 1 ∈ A) (hAb : A ⊆ matrixEntryBox 2)
    (F : Finset Γ) (hF1 : 1 ∈ F) (hden : ∀ v ∈ F, f v ∈ denominatorCarrier D)
    (u : RealMobius.Group) (hF : ∀ v ∈ F, u⁻¹ * f v * u ∈ A ^ 2)
    {a x y : Γ} (ha : a ∈ F) (hx : x ∈ F) (hy : y ∈ F)
    (hne : f ⁅⁅a, x⁆, ⁅a, y⁆⁆ ≠ 1) :
    ∀ P : CMˣ, ∃ h ∈ A ^ 4,
      min (1 / (32 * (18 : ℝ) ^ 4))
          ((1 / (D : ℝ) ^ 17) / ((2 : ℝ) ^ 44 * 18 ^ 21)) ≤
        ‖SL2Escape.complexConjugation P (Matrix.SpecialLinearGroup.map Complex.ofRealHom h) 0 1 *
          SL2Escape.complexConjugation P (Matrix.SpecialLinearGroup.map Complex.ofRealHom h) 1 0‖ := by
  let E := F.image f
  have hE1 : (1 : RealMobius.Group) ∈ E := Finset.mem_image.mpr ⟨1, hF1, map_one f⟩
  have hEd : ∀ q ∈ E, q ∈ denominatorCarrier D := by
    intro q hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
    exact hden v hv
  have hEu : ∀ q ∈ E, u⁻¹ * q * u ∈ A ^ 2 := by
    intro q hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
    exact hF v hv
  have hE (v : Γ) (hv : v ∈ F) : f v ∈ E := Finset.mem_image.mpr ⟨v, hv, rfl⟩
  exact rational_family_complex_escape hD hA1 hAb E hE1 hEd u hEu
    (hE a ha) (hE x hx) (hE y hy) (by simpa only [map_commutatorElement] using hne)

end TransposeFollowup.RationalFreePair

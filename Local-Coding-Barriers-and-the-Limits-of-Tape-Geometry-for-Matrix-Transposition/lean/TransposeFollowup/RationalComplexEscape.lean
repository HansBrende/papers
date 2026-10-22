import TransposeFollowup.SL2ComplexConjugation
import TransposeFollowup.RationalTraceCertificate
import TransposeFollowup.MobiusWalkEntrySupport

/-! Actual A^4 escape after every invertible complex change of basis,
from a finite common-denominator family whose common real conjugates lie
in A^2. Only the stated entry box is used for the trace bound. -/
namespace TransposeFollowup.RationalFreePair
open Classical Matrix Set SL2Escape RealMobius
open scoped Pointwise commutatorElement
set_option autoImplicit false
local notation "RG" => RealMobius.Group
local notation "CG" => Matrix.SpecialLinearGroup (Fin 2) ℂ
local notation "RM" => Matrix (Fin 2) (Fin 2) ℝ
local notation "CM" => Matrix (Fin 2) (Fin 2) ℂ

theorem rational_family_complex_escape {D : ℕ} (hD : 0 < D)
    {A : Set RG} (hA1 : 1 ∈ A) (hAb : A ⊆ matrixEntryBox 2)
    (F : Finset RG) (hF1 : 1 ∈ F) (hden : ∀ g ∈ F, g ∈ denominatorCarrier D)
    (u : RG) (hF : ∀ g ∈ F, u⁻¹ * g * u ∈ A ^ 2)
    {a x y : RG} (ha : a ∈ F) (hx : x ∈ F) (hy : y ∈ F)
    (hne : ⁅⁅a, x⁆, ⁅a, y⁆⁆ ≠ 1) :
    ∀ P : CMˣ, ∃ h ∈ A ^ 4,
      min (1 / (32 * (18 : ℝ) ^ 4))
          ((1 / (D : ℝ) ^ 17) / ((2 : ℝ) ^ 44 * 18 ^ 21)) ≤
        ‖complexConjugation P (Matrix.SpecialLinearGroup.map Complex.ofRealHom h) 0 1 *
          complexConjugation P (Matrix.SpecialLinearGroup.map Complex.ofRealHom h) 1 0‖ := by
  intro P
  let c : RG →* CG := Matrix.SpecialLinearGroup.map Complex.ofRealHom
  let f : RG →* CG := (complexConjugation P).comp (c.comp (MulAut.conj u⁻¹).toMonoidHom)
  have hform (v : RG) : f v = complexConjugation P (c (u⁻¹ * v * u)) := by
    change complexConjugation P (c (u⁻¹ * v * (u⁻¹)⁻¹)) = _
    rw [inv_inv]
  let S := F.image f
  have hmem (v : RG) (hv : v ∈ F) : f v ∈ S := Finset.mem_image.mpr ⟨v, hv, rfl⟩
  have hftrace (v : RG) : Matrix.trace (f v : CM) = Complex.ofReal (Matrix.trace (v : RM)) := by
    rw [hform, complexConjugation_trace, complexify_trace]
    congr 1
    simpa only [inv_inv] using sl2_trace_conjugate u⁻¹ v
  have htr : ∀ v ∈ S, ‖Matrix.trace (v : CM)‖ ≤ 16 := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    have hb : u⁻¹ * w * u ∈ matrixEntryBox 8 := by
      obtain ⟨p, hp, q, hq, he⟩ := Set.mem_mul.mp (by simpa only [pow_two] using hF w hw)
      rw [← he]
      simpa only [show (2 : ℝ) * 2 * 2 = 8 by norm_num] using matrixEntryBox_mul (hAb hp) (hAb hq)
    rw [hform, complexConjugation_trace, complexify_trace, Complex.norm_real, Real.norm_eq_abs]
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    have hh := abs_add_le ((u⁻¹ * w * u) 0 0) ((u⁻¹ * w * u) 1 1)
    linarith [hb 0 0, hb 1 1]
  obtain ⟨g, hg, hgap, _⟩ := rational_bicommutator_trace_certificate hD
    (hden a ha) (hden x hx) (hden y hy) hne
  have hgF : g ∈ F := by rcases hg with rfl | rfl | rfl | rfl <;> assumption
  have hgapC : 1 / (D : ℝ) ^ 17 ≤
      ‖Matrix.trace ((⁅⁅f a, f x⁆, ⁅f a, f y⁆⁆ * f g : CG) : CM) - Matrix.trace (f g : CM)‖ := by
    have he : Matrix.trace ((⁅⁅f a, f x⁆, ⁅f a, f y⁆⁆ * f g : CG) : CM) =
        Complex.ofReal (Matrix.trace ((⁅⁅a, x⁆, ⁅a, y⁆⁆ * g : RG) : RM)) := by
      simpa only [map_mul, map_commutatorElement] using hftrace (⁅⁅a, x⁆, ⁅a, y⁆⁆ * g)
    rw [he, hftrace, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hgap
  obtain ⟨v, hv, hescape⟩ := offDiagonal_escape_of_trace_gap S (by norm_num : (0 : ℝ) ≤ 16)
    (by positivity : 0 < 1 / (D : ℝ) ^ 17) htr (hmem a ha) (hmem x hx) (hmem y hy) (hmem g hgF) hgapC
  have h12 : (1 : RG) ∈ A ^ 2 := by
    simpa only [pow_two, mul_one] using Set.mul_mem_mul hA1 hA1
  have h24 : A ^ 2 ⊆ A ^ 4 := by
    intro w hw
    simpa only [mul_one, ← pow_add, show (2 : ℕ) + 2 = 4 from rfl] using Set.mul_mem_mul hw h12
  rcases hv with hv | ⟨p, hp, q, hq, he⟩
  · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    refine ⟨u⁻¹ * w * u, h24 (hF w hw), ?_⟩
    simpa only [hform, c, show (16 : ℝ) + 2 = 18 by norm_num] using hescape
  · obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    subst v
    have hh : u⁻¹ * (p' * q') * u ∈ A ^ 4 := by
      have he : u⁻¹ * (p' * q') * u = (u⁻¹ * p' * u) * (u⁻¹ * q' * u) := by group
      rw [he]
      simpa only [← pow_add, show (2 : ℕ) + 2 = 4 from rfl] using Set.mul_mem_mul (hF p' hp') (hF q' hq')
    refine ⟨u⁻¹ * (p' * q') * u, hh, ?_⟩
    change min _ _ ≤ ‖complexConjugation P (c (u⁻¹ * (p' * q') * u)) 0 1 *
      complexConjugation P (c (u⁻¹ * (p' * q') * u)) 1 0‖
    rw [← hform, map_mul]
    simpa only [show (16 : ℝ) + 2 = 18 by norm_num] using hescape

end TransposeFollowup.RationalFreePair

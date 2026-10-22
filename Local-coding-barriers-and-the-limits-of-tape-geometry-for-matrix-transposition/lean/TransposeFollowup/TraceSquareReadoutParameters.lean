import TransposeFollowup.ActualScalarReadoutCoefficients
import TransposeFollowup.TraceSquarePowerBounds

/-! Constants for the actual trace-square readout are chosen before the
native and scalar scales. Both coefficients retain a quantitative lower
bound; the larger one may be placed on the enlarged scalar factor. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Matrix.Norms.Frobenius Pointwise
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem normalized_trace_square_coefficients {D d ρ : ℝ}
    (hd : d ≠ 0) (hbound : |d| ≤ 32) (hρ : 0 ≤ ρ)
    (hfirst : ρ ≤ |D|) (hsecond : ρ ≤ |D-4*d|) :
    let u := 3*D/(8*d)
    let v := 3*(4*d-D)/(8*d)
    3*ρ/256 ≤ |u| ∧ 3*ρ/256 ≤ |v| ∧
      u+v = 3/2 ∧ 3/4 ≤ max |u| |v| := by
  intro u v
  have hden : 0 < 8*|d| := mul_pos (by norm_num) (abs_pos.mpr hd)
  have hlower (x : ℝ) (hx : ρ ≤ |x|) : 3*ρ/256 ≤ |3*x/(8*d)| := by
    rw [abs_div, abs_mul, abs_mul]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3),
      abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    apply (le_div_iff₀ hden).mpr
    calc
      (3*ρ/256)*(8*|d|) ≤ (3*ρ/256)*(8*32) := by gcongr
      _ = 3*ρ := by ring
      _ ≤ 3*|x| := mul_le_mul_of_nonneg_left hx (by norm_num)
  have hsum : u+v = 3/2 := by
    dsimp only [u, v]
    field_simp
    ring
  refine ⟨hlower D hfirst, hlower (4*d-D) (by simpa only [abs_sub_comm] using hsecond),
    hsum, ?_⟩
  have htri := abs_add_le u v
  rw [hsum] at htri
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3/2)] at htri
  linarith only [htri, le_max_left |u| |v|, le_max_right |u| |v|]

/-- One choice of positive constants works for every admissible scale,
frame and actual source generator. `δs` pays both normalized coefficients
and the final inverse-localization spacing. The determinant gap itself
is also retained for the later transfer to actual words. -/
theorem exists_actual_trace_square_readout_parameters :
    ∃ ρc c t₀ s₁ : ℝ,
      0 < ρc ∧ c = 3*ρc/256 ∧ 0 < c ∧ 1 ≤ t₀ ∧ 1 ≤ c*t₀ ∧
      0 < s₁ ∧ s₁ = 3072*t₀/(1/32) ∧
      ∀ {η θ Θ a δ α : ℝ} {A : Set G} {p q z : G},
        0 < η → η ≤ 1 → 0 ≤ θ → 0 < δ → δ ≤ 2*η^(1-3*Θ) →
        1 ∈ A → A⁻¹=A → 0 < α → α ≤ 1 → A ⊆ mobiusIdentityBall α →
        4*(5 : ℝ)^102*α ≤ 1 → p ∈ A^34 → q ∈ A^34 → p*q ∈ A^34 →
        η^θ ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det| →
        z ∈ mobiusIdentityBall (1/2) → η^θ/32 ≤ dist (z : RMat) 1 →
        ((z : RMat)-(Matrix.trace (z : RMat)/2) • (1 : RMat)).det ≠ 0 →
        let b := (z : RMat)-(Matrix.trace (z : RMat)/2) • (1 : RMat)
        let δs := t₀*δ*η^(-(12*θ))
        let σ₁ := s₁*η^(1-(3*Θ+13*θ+a))
        let Kinv := 3072/((η^θ/32)*η^a)
        0 < δs ∧ δ ≤ δs ∧ 0 < σ₁ ∧ Kinv*δs ≤ 2*σ₁ ∧
        ∃ g ∈ A^204,
          let D := (b*(g : RMat)-(g : RMat)*b).det
          let u := 3*D/(8*b.det)
          let v := 3*(4*b.det-D)/(8*b.det)
          ρc*η^(12*θ) ≤ |D| ∧ ρc*η^(12*θ) ≤ |D-4*b.det| ∧
          c*η^(12*θ) ≤ |u| ∧ c*η^(12*θ) ≤ |v| ∧
          u+v = 3/2 ∧ 3/4 ≤ max |u| |v| ∧ δ ≤ |u| *δs ∧ δ ≤ |v| *δs := by
  let H := (4 : ℝ)^34
  let B := 128*((4 : ℝ)^68)^2
  let Γc := (1/256 : ℝ)^3/(3456*(96*H^4)^3)
  let ρc := Γc^2/(3328*B^4)
  let c := 3*ρc/256
  let t₀ := max 1 (1/c)
  let s₁ := 3072*t₀/(1/32)
  have hH : 0 < H := by dsimp only [H]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hΓc : 0 < Γc := by dsimp only [Γc]; positivity
  have hρc : 0 < ρc := by dsimp only [ρc]; positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  have ht₀ : 1 ≤ t₀ := le_max_left _ _
  have hct₀ : 1 ≤ c*t₀ := by
    have hh := mul_le_mul_of_nonneg_left (le_max_right 1 (1/c)) hc.le
    simpa only [mul_one_div_cancel hc.ne', t₀] using hh
  have hs₁ : 0 < s₁ := by dsimp only [s₁]; positivity
  refine ⟨ρc, c, t₀, s₁, hρc, rfl, hc, ht₀, hct₀, hs₁, rfl, ?_⟩
  intro η θ Θ a δ α A p q z hη hηone hθ hδ hδupper
    hA1 hAi hα hαone hA hsmall hp hq hpq hspan hz hfar hdet b δs σ₁ Kinv
  obtain ⟨g, hg, hfirst, hsecond⟩ := exists_actual_two_readout_coefficients
    hA1 hAi hα hαone hA hsmall hp hq hpq
    (Real.rpow_pos_of_pos hη θ) hspan hz (by positivity : 0 < η^θ/32) hfar
  have hΓ : (η^θ/32/8)^3/(3456*(96*H^4/η^θ)^3) = Γc*η^(6*θ) := by
    have hp₆ : η^(6*θ) = (η^θ)^6 := by
      rw [show 6*θ = θ*(6 : ℕ) by norm_num; ring, Real.rpow_mul_natCast hη.le]
    rw [hp₆]
    dsimp only [Γc]
    field_simp
    ring
  have hρ : ((η^θ/32/8)^3/(3456*(96*H^4/η^θ)^3))^2/(3328*B^4) =
      ρc*η^(12*θ) := by
    rw [hΓ, mul_pow]
    have hp₂ : (η^(6*θ))^2 = η^(12*θ) := by
      rw [← Real.rpow_mul_natCast hη.le]
      congr 1
      norm_num
      ring
    rw [hp₂]
    dsimp only [ρc]
    ring
  change ((η^θ/32/8)^3/(3456*(96*H^4/η^θ)^3))^2/(3328*B^4) ≤ _ at hfirst hsecond
  rw [hρ] at hfirst hsecond
  obtain ⟨hu, hv, hsum, hmax⟩ := normalized_trace_square_coefficients hdet
    (centered_near_identity_generator_bounds z hz).2
    (by positivity : 0 ≤ ρc*η^(12*θ)) hfirst hsecond
  have heq : 3*(ρc*η^(12*θ))/256 = c*η^(12*θ) := by dsimp only [c]; ring
  rw [heq] at hu hv
  obtain ⟨hδs, hδδs, hσ₁, hspacing, hcoeff⟩ := trace_square_scalar_spacing
    (a := a) (l₀ := 1/32) hη hηone hθ (by norm_num) ht₀ hδ hδupper
    (le_refl s₁)
  have hK : Kinv = (3072/(1/32))*η^(-(θ+a)) := by
    dsimp only [Kinv]
    rw [Real.rpow_neg hη.le, Real.rpow_add hη]
    field_simp
  refine ⟨hδs, hδδs, hσ₁, ?_, g, hg, hfirst, hsecond, hu, hv, hsum, hmax,
    hcoeff _ c hu hct₀, hcoeff _ c hv hct₀⟩
  rw [hK]
  exact hspacing

end TransposeFollowup.SL2Projection

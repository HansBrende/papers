import TransposeFollowup.NilpotentExtractionParameters
import TransposeFollowup.ScalarSampleNormalization
import TransposeFollowup.DyadicCenterTrimming

/-! Power envelopes for the actual two-stage sampling costs.
The fine sampling cost is reused from the existing extraction parameters.
All constants are independent of the native scale. -/
namespace TransposeFollowup.SL2Projection
set_option autoImplicit false

theorem two_stage_sampling_power_bounds {η θ Θ a l₀ s₀ s₁ R : ℝ}
    (hη : 0 < η) (hηone : η ≤ 1) (hθ : 0 ≤ θ) (hΘ : 0 ≤ Θ) (ha : 0 ≤ a)
    (hl₀ : 0 < l₀) (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) (hR : 0 ≤ R)
    (hretention : 12*Θ+88*θ+4*a ≤ 36*Θ) (hinverse : θ+a ≤ 3*Θ) :
    let p := 3*Θ+13*θ+a
    let σ₀ := s₀*η^(1-9*θ)
    let σ₁ := s₁*η^(1-p)
    let C₀ := 6561*(4*σ₀/η+1)^4
    let C₁ := 6561*(4*σ₁/η+1)^4
    let S₀ := 6561*(4*s₀+1)^4
    let S₁ := 6561*(4*s₁+1)^4
    let Kinv := 3072/((l₀*η^θ)*η^a)
    let Dloc := 40*(2*R)^11*(Kinv+2)
    let Dc := 40*(2*R)^11*(3072/l₀+2)
    C₀ ≤ S₀*η^(-(36*θ)) ∧
      C₁ ≤ S₁*η^(-(4*p)) ∧
      4*C₀*C₁ ≤ (4*S₀*S₁)*η^(-(36*Θ)) ∧
      Kinv = (3072/l₀)*η^(-(θ+a)) ∧
      Dloc ≤ Dc*η^(-(3*Θ)) := by
  intro p σ₀ σ₁ C₀ C₁ S₀ S₁ Kinv Dloc Dc
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hC₀ := (first_extraction_cost_bounds
    (a := 1) (b := 1) (l := 1) (s := s₀) (e := 0) (B := 0) (B₀ := 0) (R := 0)
    hη hηone hθ zero_lt_one zero_lt_one hs₀ le_rfl le_rfl le_rfl le_rfl).2.1
  have hC₁ := (first_extraction_cost_bounds
    (θ := p/9) (a := 1) (b := 1) (l := 1) (s := s₁)
    (e := 0) (B := 0) (B₀ := 0) (R := 0)
    hη hηone (by positivity) zero_lt_one zero_lt_one hs₁
    le_rfl le_rfl le_rfl le_rfl).2.1
  change C₀ ≤ S₀*η^(-(36*θ)) at hC₀
  simp only [show 9*(p/9) = p by ring, show 36*(p/9) = 4*p by ring] at hC₁
  change C₁ ≤ S₁*η^(-(4*p)) at hC₁
  have hC₀0 : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hC₁0 : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  have hS₀ : 0 ≤ S₀ := by dsimp only [S₀]; positivity
  have hS₁ : 0 ≤ S₁ := by dsimp only [S₁]; positivity
  have hK : Kinv = (3072/l₀)*η^(-(θ+a)) := by
    dsimp only [Kinv]
    rw [Real.rpow_neg hη.le, Real.rpow_add hη]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  refine ⟨hC₀, hC₁, ?_, hK, ?_⟩
  · calc
      4*C₀*C₁ ≤ 4*(S₀*η^(-(36*θ)))*(S₁*η^(-(4*p))) := by gcongr
      _ = (4*S₀*S₁)*η^(-(36*θ+4*p)) := by
        rw [neg_add, Real.rpow_add hη]
        ring
      _ ≤ (4*S₀*S₁)*η^(-(36*Θ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_ge hη hηone
          (by dsimp only [p]; linarith only [hretention])
  · have hone : 1 ≤ η^(-(θ+a)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hη hηone (by linarith only [hθ, ha])
    have hbase : Kinv+2 ≤ (3072/l₀+2)*η^(-(θ+a)) := by
      rw [hK]
      nlinarith only [hone]
    calc
      Dloc ≤ Dc*η^(-(θ+a)) := by
        simpa only [Dloc, Dc, mul_assoc] using
          mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ 40*(2*R)^11)
      _ ≤ Dc*η^(-(3*Θ)) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hη hηone (neg_le_neg hinverse))
          (by dsimp only [Dc]; positivity)

/-- The final scalar and matrix spacings are chosen from the same radius.
The last conclusion pays the smaller readout coefficient without assuming
that coefficient is bounded below by a scale-independent constant. -/
theorem trace_square_scalar_spacing {η θ Θ a l₀ t₀ s₁ δ : ℝ}
    (hη : 0 < η) (hηone : η ≤ 1) (hθ : 0 ≤ θ)
    (hl₀ : 0 < l₀) (ht₀ : 1 ≤ t₀) (hδ : 0 < δ)
    (hδupper : δ ≤ 2*η^(1-3*Θ)) (hconstant : 3072*t₀/l₀ ≤ s₁) :
    let δs := t₀*δ*η^(-(12*θ))
    let Kinv := (3072/l₀)*η^(-(θ+a))
    let σ₁ := s₁*η^(1-(3*Θ+13*θ+a))
    0 < δs ∧ δ ≤ δs ∧ 0 < σ₁ ∧ Kinv*δs ≤ 2*σ₁ ∧
      ∀ z c : ℝ, c*η^(12*θ) ≤ |z| → 1 ≤ c*t₀ → δ ≤ |z| *δs := by
  intro δs Kinv σ₁
  have ht₀pos : 0 < t₀ := zero_lt_one.trans_le ht₀
  have hs₁ : 0 < s₁ := (by positivity : 0 < 3072*t₀/l₀).trans_le hconstant
  have hK : 0 ≤ Kinv := by dsimp only [Kinv]; positivity
  have hp : 1 ≤ η^(-(12*θ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hη hηone (by linarith only [hθ])
  refine ⟨by dsimp only [δs]; positivity, ?_, by dsimp only [σ₁]; positivity, ?_, ?_⟩
  · calc
      δ ≤ t₀*δ := le_mul_of_one_le_left hδ.le ht₀
      _ ≤ (t₀*δ)*η^(-(12*θ)) := le_mul_of_one_le_right (by positivity) hp
      _ = δs := rfl
  · calc
      Kinv*δs ≤ Kinv*(t₀*(2*η^(1-3*Θ))*η^(-(12*θ))) := by
        dsimp only [δs]
        gcongr
      _ = 2*(3072*t₀/l₀)*η^(1-(3*Θ+13*θ+a)) := by
        have he : 1-(3*Θ+13*θ+a) = -(θ+a)+(1-3*Θ)+(-(12*θ)) := by ring
        rw [he, Real.rpow_add hη, Real.rpow_add hη]
        dsimp only [Kinv]
        ring
      _ ≤ 2*s₁*η^(1-(3*Θ+13*θ+a)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hconstant (by norm_num)) (by positivity)
      _ = 2*σ₁ := by dsimp only [σ₁]; ring
  · intro z c hz hct
    have hinv : η^(12*θ)*η^(-(12*θ)) = 1 := by
      rw [← Real.rpow_add hη, add_neg_cancel, Real.rpow_zero]
    calc
      δ ≤ (c*t₀)*δ := le_mul_of_one_le_left hδ.le hct
      _ = (c*η^(12*θ))*δs := by
        dsimp only [δs]
        calc
          _ = (c*t₀*δ)*(η^(12*θ)*η^(-(12*θ))) := by rw [hinv, mul_one]
          _ = _ := by ring
      _ ≤ |z| *δs := mul_le_mul_of_nonneg_right hz (by dsimp only [δs]; positivity)

/-- The quantitative extraction has the actual `d^11` denominator.
Its fixed constant and that denominator are both retained. -/
theorem trace_square_normalization_power_bound {η θ C P H Hc : ℝ}
    (hη : 0 < η) (hC : 0 ≤ C) (hP : 0 ≤ P) (hH : 0 ≤ H)
    (hPb : P ≤ η^(-θ)) (hHb : H ≤ Hc*η^(-(8*θ))) :
    C*(9*P*H)^3/(η^θ)^11 ≤ (C*(9*Hc)^3)*η^(-(38*θ)) := by
  calc
    C*(9*P*H)^3/(η^θ)^11 ≤
        C*(9*η^(-θ)*(Hc*η^(-(8*θ))))^3/(η^θ)^11 := by gcongr
    _ = (C*(9*Hc)^3)*η^(-(38*θ)) := by
      have hnum : (η^(-θ)*η^(-(8*θ)))^3 = η^(-(27*θ)) := by
        rw [← Real.rpow_add hη, ← Real.rpow_mul_natCast hη.le]
        congr 1
        norm_num
        ring
      have hden : (η^θ)^11 = η^(11*θ) := by
        rw [← Real.rpow_mul_natCast hη.le]
        congr 1
        norm_num
        ring
      have heq : 9*η^(-θ)*(Hc*η^(-(8*θ))) =
          (9*Hc)*(η^(-θ)*η^(-(8*θ))) := by ring
      rw [heq, mul_pow, hnum, hden, mul_div_assoc, mul_div_assoc,
        ← Real.rpow_sub hη, show -(27*θ)-11*θ = -(38*θ) by ring]
      ring

/-- The localized near-identity count has a decaying cutoff factor.
This is the exact profile expression used in the fine trimming budget. -/
theorem trace_square_near_power_bound {η θ a κ γ R ε E Ec Cp K J : ℝ}
    (hη : 0 < η) (hηone : η ≤ 1)
    (hκ : 0 ≤ κ) (hκone : κ ≤ 1) (hγ : 0 ≤ γ) (hγθ : γ ≤ θ)
    (hR : 0 ≤ R) (hε : 0 ≤ ε) (hEc : 0 ≤ Ec)
    (hCp : 0 ≤ Cp) (hK : 0 ≤ K) (hJ : 0 ≤ J)
    (hεs : ε ≤ η^a) (hEb : E ≤ Ec*η^(-(8*θ)))
    (hKb : K ≤ η^(-θ)) (hJb : J ≤ η^(-θ)) :
    E*(Cp*K*J*η^(-(γ*κ)))*(40*(2*R)^11*(η^a+ε))^κ ≤
      (Ec*Cp*(80*(2*R)^11)^κ)*η^(κ*a-11*θ) := by
  have hγpow : η^(-(γ*κ)) ≤ η^(-θ) :=
    Real.rpow_le_rpow_of_exponent_ge hη hηone
      (by nlinarith only [hγ, hκone, hγθ])
  have hrad : 40*(2*R)^11*(η^a+ε) ≤ (80*(2*R)^11)*η^a := by
    have hh := mul_le_mul_of_nonneg_left hεs (by positivity : 0 ≤ 40*(2*R)^11)
    nlinarith only [hh]
  have hradpow : (40*(2*R)^11*(η^a+ε))^κ ≤
      (80*(2*R)^11)^κ*η^(a*κ) := by
    calc
      _ ≤ ((80*(2*R)^11)*η^a)^κ :=
        Real.rpow_le_rpow (by positivity) hrad hκ
      _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hη.le]
  calc
    _ ≤ (Ec*η^(-(8*θ)))*(Cp*η^(-θ)*η^(-θ)*η^(-θ))*
        ((80*(2*R)^11)^κ*η^(a*κ)) := by gcongr
    _ = (Ec*Cp*(80*(2*R)^11)^κ)*η^(κ*a-11*θ) := by
      have he : κ*a-11*θ = -(8*θ)+(-θ)+(-θ)+(-θ)+a*κ := by ring
      rw [he, Real.rpow_add hη, Real.rpow_add hη, Real.rpow_add hη, Real.rpow_add hη]
      ring

theorem fine_trim_ratio_power_bound {η θ a κ L C W A Lc Cc Wc Ac : ℝ}
    (hη : 0 < η) (hL : 0 ≤ L) (hC : 0 ≤ C) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (hLc : 0 ≤ Lc) (hCc : 0 ≤ Cc) (hWc : 0 ≤ Wc)
    (hLb : L ≤ Lc*η^(-(44*θ))) (hCb : C ≤ Cc*η^(-(36*θ)))
    (hWb : W ≤ Wc*η^(-(38*θ))) (hAb : A ≤ Ac*η^(κ*a-11*θ)) :
    32*L^3*C^3*W*(A+1/(2*η)^(-κ)) ≤
      (32*Lc^3*Cc^3*Wc)*
        (Ac*η^(κ*a-289*θ)+(2 : ℝ)^κ*η^(κ-278*θ)) := by
  have hrecip : 1/(2*η)^(-κ) = (2 : ℝ)^κ*η^κ := by
    rw [Real.rpow_neg (by positivity : 0 ≤ 2*η), one_div, inv_inv,
      Real.mul_rpow (by norm_num) hη.le]
  have hcore : 32*L^3*C^3*W ≤ (32*Lc^3*Cc^3*Wc)*η^(-(278*θ)) := by
    calc
      _ ≤ 32*(Lc*η^(-(44*θ)))^3*(Cc*η^(-(36*θ)))^3*(Wc*η^(-(38*θ))) := by gcongr
      _ = _ := by
        rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hη.le,
          ← Real.rpow_mul_natCast hη.le]
        have he : -(278*θ) = -(44*θ)*(3 : ℕ)+(-(36*θ)*(3 : ℕ))+(-(38*θ)) := by ring
        rw [he, Real.rpow_add hη, Real.rpow_add hη]
        ring
  rw [hrecip]
  calc
    _ ≤ ((32*Lc^3*Cc^3*Wc)*η^(-(278*θ)))*
        (Ac*η^(κ*a-11*θ)+(2 : ℝ)^κ*η^κ) := by gcongr
    _ = _ := by
      have hfirst : η^(-(278*θ))*η^(κ*a-11*θ) = η^(κ*a-289*θ) := by
        rw [← Real.rpow_add hη]
        congr 1
        ring
      have hsecond : η^(-(278*θ))*η^κ = η^(κ-278*θ) := by
        rw [← Real.rpow_add hη]
        congr 1
        ring
      simp only [mul_add]
      rw [show ((32*Lc^3*Cc^3*Wc)*η^(-(278*θ)))*(Ac*η^(κ*a-11*θ)) =
        (32*Lc^3*Cc^3*Wc)*Ac*(η^(-(278*θ))*η^(κ*a-11*θ)) by ring,
        show ((32*Lc^3*Cc^3*Wc)*η^(-(278*θ)))*((2 : ℝ)^κ*η^κ) =
        (32*Lc^3*Cc^3*Wc)*(2 : ℝ)^κ*(η^(-(278*θ))*η^κ) by ring,
        hfirst, hsecond]
      ring

/-- One threshold pays both terms of the fine trimming ratio. -/
theorem exists_fine_trim_ratio_threshold {θ a κ B Ac : ℝ}
    (hB : 0 ≤ B) (hAc : 0 ≤ Ac)
    (hnear : 289*θ < κ*a) (hone : 278*θ < κ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      let η := (1/4 : ℝ)^j
      B*(Ac*η^(κ*a-289*θ)+(2 : ℝ)^κ*η^(κ-278*θ)) ≤ 1 := by
  obtain ⟨J₁, hJ₁⟩ := exists_dyadic_scaled_rpow_bound
    (by positivity : 0 < 2*(B*Ac+1)) (sub_pos.mpr hnear)
  obtain ⟨J₂, hJ₂⟩ := exists_dyadic_scaled_rpow_bound
    (by positivity : 0 < 2*(B*(2 : ℝ)^κ+1)) (sub_pos.mpr hone)
  refine ⟨max J₁ J₂, ?_⟩
  intro j hj η
  have hfirst := hJ₁ j ((le_max_left _ _).trans hj)
  have hsecond := hJ₂ j ((le_max_right _ _).trans hj)
  have hp : 0 ≤ η^(κ*a-289*θ) := Real.rpow_nonneg (by dsimp only [η]; positivity) _
  have hq : 0 ≤ η^(κ-278*θ) := Real.rpow_nonneg (by dsimp only [η]; positivity) _
  change 2*(B*Ac+1)*η^(κ*a-289*θ) ≤ 1 at hfirst
  change 2*(B*(2 : ℝ)^κ+1)*η^(κ-278*θ) ≤ 1 at hsecond
  nlinarith only [hfirst, hsecond, hp, hq]

end TransposeFollowup.SL2Projection

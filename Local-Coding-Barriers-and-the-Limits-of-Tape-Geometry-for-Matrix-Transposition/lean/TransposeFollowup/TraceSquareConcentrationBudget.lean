import TransposeFollowup.TraceSquarePowerBounds

/-! Reuse the existing concentration power bounds for the quantitative
trace-square extraction. Its fixed extraction constant and its `d^11`
normalization are retained explicitly. -/
namespace TransposeFollowup.SL2Projection
set_option autoImplicit false

theorem trace_square_concentration_power_budget
    {η θ Θ κ γ H S L E D P K J Cp Hc Sc Lc Ec Dc Cext : ℝ}
    (hη : 0 < η) (hηone : η ≤ 1) (hΘ : 0 ≤ Θ)
    (hκ : 0 ≤ κ) (hκone : κ ≤ 1) (hγ : 0 ≤ γ) (hγΘ : γ ≤ Θ)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hP : 0 ≤ P) (hK : 0 ≤ K) (hJ : 0 ≤ J) (hCp : 0 ≤ Cp)
    (hHc : 0 ≤ Hc) (hSc : 0 ≤ Sc) (hLc : 0 ≤ Lc)
    (hEc : 0 ≤ Ec) (hDc : 0 ≤ Dc) (hCext : 0 ≤ Cext)
    (hHb : H ≤ Hc*η^(-(8*Θ))) (hSb : S ≤ Sc*η^(-(36*Θ)))
    (hLb : L ≤ Lc*η^(-(44*Θ))) (hEb : E ≤ Ec*η^(-(8*Θ)))
    (hDb : D ≤ Dc*η^(-(3*Θ)))
    (hPb : P ≤ η^(-Θ)) (hKb : K ≤ η^(-Θ)) (hJb : J ≤ η^(-Θ))
    (hnormalization : 11*θ ≤ 8*Θ) :
    let Q := 4*L^3*(E*(Cp*K*J*η^(-(γ*κ)))*D^κ+(2 : ℝ)^κ)
    let W := Cext*(9*P*H)^3/(η^θ)^11*S^3
    let Qc := 4*Lc^3*(Ec*Cp*Dc^κ+(2 : ℝ)^κ)
    let Wc := (9*Hc)^3*Sc^3
    let Cscalar := 1+Qc*(Cext*Wc)
    Q ≤ Qc*η^(-(146*Θ)) ∧ W ≤ (Cext*Wc)*η^(-(143*Θ)) ∧
      1 ≤ Cscalar ∧ Q*W ≤ (Cscalar*η^(-(100*Θ)))^3 := by
  intro Q W Qc Wc Cscalar
  obtain ⟨hQb, hWold⟩ := scalar_concentration_power_bounds
    hη hηone hΘ hκ hκone hγ hγΘ hH hS hL hD hP hK hJ hCp
    hHc hEc hDc hHb hSb hLb hEb hDb hPb hKb hJb
  have hden : (η^θ)^11 = η^(11*θ) := by
    rw [← Real.rpow_mul_natCast hη.le]
    congr 1
    norm_num
    ring
  have hWrepr : W = Cext*((9*P*H)^3*η^(-(11*θ))*S^3) := by
    dsimp only [W]
    rw [hden, Real.rpow_neg hη.le]
    simp only [div_eq_mul_inv]
    ring
  have hWb : W ≤ (Cext*Wc)*η^(-(143*Θ)) := by
    calc
      W = Cext*((9*P*H)^3*η^(-(11*θ))*S^3) := hWrepr
      _ ≤ Cext*((9*P*H)^3*η^(-(8*Θ))*S^3) := by
        have hp := Real.rpow_le_rpow_of_exponent_ge hη hηone (neg_le_neg hnormalization)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (9*P*H)^3))
            (pow_nonneg hS 3)) hCext
      _ ≤ Cext*(Wc*η^(-(143*Θ))) := mul_le_mul_of_nonneg_left hWold hCext
      _ = _ := by ring
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hQc : 0 ≤ Qc := by dsimp only [Qc]; positivity
  have hWc : 0 ≤ Wc := by dsimp only [Wc]; positivity
  refine ⟨hQb, hWb, ?_, ?_⟩
  · exact le_add_of_nonneg_right (mul_nonneg hQc (mul_nonneg hCext hWc))
  · exact concentration_budget_of_power_bounds hη hηone hΘ hW hQc
      (mul_nonneg hCext hWc) hQb hWb

end TransposeFollowup.SL2Projection

import TransposeFollowup.TraceSquareConcentrationBudget
import TransposeFollowup.TraceSquareExponentMargins

/-! A single dyadic threshold pays the actual two-stage cost formulas.
No trimming or concentration budget is assumed. The fine-chart constants
may be chosen by `exists_scaled_extraction_parameters` and the final
spacing constant by `exists_actual_trace_square_readout_parameters`. -/
namespace TransposeFollowup.SL2Projection
open BoundedCoordinatePacking
set_option autoImplicit false

/-- All constants precede the scale. `W₀` normalizes the original source;
`W` also pays both coarsening losses. Fine trimming uses only `C₀`.
`Eerr` and `Ffar` allow the later actual-word error to be paid at the
same threshold, without changing the previously chosen coefficients. -/
theorem exists_trace_square_joint_budgets
    {κ e b s₀ s₁ e₀ Cext Cp B R Eerr Ffar : ℝ}
    (hκ : 0 < κ) (hκone : κ ≤ 1) (he : 0 < e) (heone : e ≤ 1)
    (hb : 0 < b) (hs₀ : 0 < s₀) (hs₁ : 0 < s₁)
    (he₀ : 26214400 ≤ e₀) (hCext : 0 < Cext) (hCp : 0 ≤ Cp)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hEerr : 1 ≤ Eerr) (hFfar : 0 < Ffar) :
    let Θ := min e κ/16384
    let θ := κ*Θ/1024
    let a := 5*Θ/16
    ∃ Cscalar Wc : ℝ, 1 ≤ Cscalar ∧ 0 < Wc ∧
      ∃ J₀ : ℕ, ∀ j : ℕ, J₀ ≤ j →
        let η := (1/4 : ℝ)^j
        let ε := e₀*η^(1-2*θ)
        let s := η^a
        let P := η^(-θ)
        let σ₀ := s₀*η^(1-9*θ)
        let σ₁ := s₁*η^(1-(3*Θ+13*θ+a))
        let C₀ := 6561*(4*σ₀/η+1)^4
        let C₁ := 6561*(4*σ₁/η+1)^4
        let H := (419430400/η^θ+17)^4
        let L := ((binCount B (b*η^(11*θ))^4 : ℕ) : ℝ)
        let E := (4*(20*(2*R)^10*ε+2*R*η)/η+1)^4
        let Kinv := 3072/(((1/32)*η^θ)*s)
        let Dloc := 40*(2*R)^11*(Kinv+2)
        let W₀ := Cext*(9*P*H)^3/(η^θ)^11
        let W := W₀*(4*C₀*C₁)^3
        let Anear := E*(Cp*P*P*η^(-((θ/2)*κ)))*(40*(2*R)^11*(s+ε))^κ
        let Q := 4*L^3*(E*(Cp*P*P*η^(-((θ/2)*κ)))*Dloc^κ+(2 : ℝ)^κ)
        0 < η ∧ η ≤ 1 ∧ 0 < s ∧ s ≤ 1 ∧ η ≤ ε ∧
        26214400*η^(1-θ) ≤ ε ∧ ε ≤ s ∧ ε ≤ 1/128 ∧
        Eerr*ε ≤ η^(1-3*Θ) ∧ Eerr*ε ≤ Ffar*η^(12*θ+a) ∧
        2*η < η^(θ/2) ∧
        32*L^3*C₀^3*W₀*(Anear+1/(2*η)^(-κ)) ≤ 1 ∧
        W ≤ Wc*η^(-(143*Θ)) ∧ Q*W ≤ (Cscalar*η^(-(100*Θ)))^3 := by
  intro Θ θ a
  obtain ⟨hΘ, hΘfour, hθ, hθΘ, ha, _, htrim₁, htrim₂, hnorm,
    hretention, hinverse, _, herror, _, _⟩ :=
      trace_square_two_stage_exponent_margins hκ hκone he heone
  change 0 < Θ at hΘ
  change 0 < θ at hθ
  change θ ≤ Θ at hθΘ
  change 0 < a at ha
  change Θ < 1/4 at hΘfour
  change 289*θ < κ*a at htrim₁
  change 278*θ < κ at htrim₂
  change 11*θ ≤ 8*Θ at hnorm
  change 12*Θ+88*θ+4*a ≤ 36*Θ at hretention
  change θ+a ≤ 3*Θ at hinverse
  change 14*θ+a < 1 at herror
  have he₀pos : 0 < e₀ := by linarith only [he₀]
  have hEerrpos : 0 < Eerr := zero_lt_one.trans_le hEerr
  let Hc := (102400*(2 : ℝ)^7/(1/32)+8*2+1)^4
  let S₀ := 6561*(4*s₀+1)^4
  let S₁ := 6561*(4*s₁+1)^4
  let Sc := 4*S₀*S₁
  let Lc := (2*B/b+1)^4
  let Ec := (80*(2*R)^10*e₀+8*R+1)^4
  let Dc := 40*(2*R)^11*(3072/(1/32)+2)
  let W₀c := Cext*(9*Hc)^3
  let Ac := Ec*Cp*(80*(2*R)^11)^κ
  let Qc := 4*Lc^3*(Ec*Cp*Dc^κ+(2 : ℝ)^κ)
  let Wc := Cext*((9*Hc)^3*Sc^3)
  let Cscalar := 1+Qc*Wc
  have hHc : 0 < Hc := by dsimp only [Hc]; positivity
  have hS₀ : 0 < S₀ := by dsimp only [S₀]; positivity
  have hS₁ : 0 < S₁ := by dsimp only [S₁]; positivity
  have hSc : 0 < Sc := by dsimp only [Sc]; positivity
  have hLc : 0 < Lc := by dsimp only [Lc]; positivity
  have hEc : 0 < Ec := by dsimp only [Ec]; positivity
  have hDc : 0 ≤ Dc := by dsimp only [Dc]; positivity
  have hW₀c : 0 < W₀c := by dsimp only [W₀c]; positivity
  have hAc : 0 ≤ Ac := by dsimp only [Ac]; positivity
  have hQc : 0 ≤ Qc := by dsimp only [Qc]; positivity
  have hWc : 0 < Wc := by dsimp only [Wc]; positivity
  have hCscalar : 1 ≤ Cscalar := le_add_of_nonneg_right (mul_nonneg hQc hWc.le)
  obtain ⟨Jtrim, hJtrim⟩ := exists_fine_trim_ratio_threshold
    (B := 32*Lc^3*S₀^3*W₀c) (Ac := Ac) (by positivity) hAc htrim₁ htrim₂
  obtain ⟨Js, hJs⟩ := exists_dyadic_power_comparison (a := -(1-2*θ)) (b := -a)
    he₀pos (by linarith only [herror, hθ])
  obtain ⟨Jnear, hJnear⟩ := exists_dyadic_scaled_rpow_bound
    (c := 128*e₀) (e := 1-2*θ) (by positivity) (by linarith only [herror, ha, hθ])
  obtain ⟨Jerr, hJerr⟩ := exists_dyadic_power_comparison
    (a := -(1-2*θ)) (b := -(1-3*Θ))
    (by positivity : 0 < Eerr*e₀) (by linarith only [hθΘ, hΘ])
  obtain ⟨Jfar, hJfar⟩ := exists_dyadic_power_comparison
    (a := -(1-2*θ)) (b := -(12*θ+a))
    (by positivity : 0 < Eerr*e₀/Ffar) (by linarith only [herror])
  obtain ⟨Jwindow, hJwindow⟩ := exists_dyadic_power_comparison
    (c := 4) (a := -1) (b := -(θ/2))
    (by norm_num) (by linarith only [hθΘ, hΘfour])
  refine ⟨Cscalar, Wc, hCscalar, hWc,
    max Jtrim (max Js (max Jnear (max Jerr (max Jfar Jwindow)))), ?_⟩
  intro j hj η ε s P σ₀ σ₁ C₀ C₁ H L E Kinv Dloc W₀ W Anear Q
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηone : η ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hs : 0 < s := Real.rpow_pos_of_pos hη a
  have hsone : s ≤ 1 := Real.rpow_le_one hη.le hηone ha.le
  have hεs : ε ≤ s := by simpa only [neg_neg] using hJs j (by omega)
  have hεnear : ε ≤ 1/128 := by
    have hh := hJnear j (by omega)
    change 128*e₀*η^(1-2*θ) ≤ 1 at hh
    dsimp only [ε]
    linarith only [hh]
  have herr : Eerr*ε ≤ η^(1-3*Θ) := by
    simpa only [neg_neg, ε, mul_assoc] using hJerr j (by omega)
  have hfar : Eerr*ε ≤ Ffar*η^(12*θ+a) := by
    have hh := hJfar j (by omega)
    simp only [neg_neg] at hh
    have heq : Eerr*ε/Ffar = (Eerr*e₀/Ffar)*η^(1-2*θ) := by dsimp only [ε]; ring
    rw [← heq] at hh
    simpa only [mul_comm] using (div_le_iff₀ hFfar).mp hh
  have hwindow : 2*η < η^(θ/2) := by
    have hh := hJwindow j (by omega)
    simp only [neg_neg, Real.rpow_one] at hh
    linarith only [hh, hη]
  have hsource : 26214400*η^(1-θ) ≤ ε := by
    exact mul_le_mul he₀
      (Real.rpow_le_rpow_of_exponent_ge hη hηone (by linarith only [hθ]))
      (by positivity) he₀pos.le
  have hηε : η ≤ ε := by
    have hp : η ≤ η^(1-2*θ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
        hη hηone (by linarith only [hθ] : 1-2*θ ≤ 1)
    exact hp.trans (le_mul_of_one_le_left (by positivity) (by linarith only [he₀]))
  obtain ⟨hHw, hC₀b, hLb, hEb, _⟩ := first_extraction_cost_bounds
    (a := 1/32) (b := b) (s := s₀) (l := 1) (e := e₀) (B := B) (B₀ := 2) (R := R)
    hη hηone hθ.le (by norm_num) hb hs₀ he₀pos.le hB (by norm_num) hR
  change C₀ ≤ S₀*η^(-(36*θ)) at hC₀b
  change L ≤ Lc*η^(-(44*θ)) at hLb
  change E ≤ Ec*η^(-(8*θ)) at hEb
  have hHb : H ≤ Hc*η^(-(8*θ)) := by
    apply le_trans ?_ hHw
    have hp := Real.rpow_le_rpow_of_exponent_ge hη hηone
      (by linarith only [hθ] : θ ≤ 2*θ)
    change (419430400/η^θ+17)^4 ≤
      (102400*(2 : ℝ)^7/((1/32)*η^(2*θ))+8*2+1)^4
    have heq : 102400*(2 : ℝ)^7/((1/32)*η^(2*θ))+8*2+1 =
        419430400/η^(2*θ)+17 := by ring
    rw [heq]
    gcongr
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hW₀ : 0 ≤ W₀ := by dsimp only [W₀]; positivity
  have hAnear : 0 ≤ Anear := by dsimp only [Anear, E]; positivity
  have hW₀b : W₀ ≤ W₀c*η^(-(38*θ)) :=
    trace_square_normalization_power_bound hη hCext.le hP hH le_rfl hHb
  have hAnearB : Anear ≤ Ac*η^(κ*a-11*θ) :=
    trace_square_near_power_bound hη hηone hκ.le hκone
      (by positivity : 0 ≤ θ/2) (by linarith only [hθ]) hR hε hEc.le hCp hP hP
      hεs hEb le_rfl le_rfl
  have htrim := (fine_trim_ratio_power_bound hη hL hC₀ hW₀ hAnear
    hLc.le hS₀.le hW₀c.le hLb hC₀b hW₀b hAnearB).trans (hJtrim j (by omega))
  obtain ⟨_, _, hSb, _, hDb⟩ := two_stage_sampling_power_bounds
    hη hηone hθ.le hΘ.le ha.le (by norm_num : (0 : ℝ) < 1/32)
    hs₀ hs₁ hR hretention hinverse
  change 4*C₀*C₁ ≤ Sc*η^(-(36*Θ)) at hSb
  change Dloc ≤ Dc*η^(-(3*Θ)) at hDb
  have hweaken {x C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p)
      (hx : x ≤ C*η^(-(p*θ))) : x ≤ C*η^(-(p*Θ)) := by
    exact hx.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hη hηone
        (neg_le_neg (mul_le_mul_of_nonneg_left hθΘ hp))) hC)
  have hPb : P ≤ η^(-Θ) :=
    Real.rpow_le_rpow_of_exponent_ge hη hηone (neg_le_neg hθΘ)
  obtain ⟨_, hWb, _, hbudget⟩ := trace_square_concentration_power_budget
    (θ := θ) hη hηone hΘ.le hκ.le hκone (by positivity : 0 ≤ θ/2)
    (by linarith only [hθΘ, hθ]) hH (by positivity : 0 ≤ 4*C₀*C₁) hL
    (by dsimp only [Dloc, Kinv]; positivity) hP hP hP hCp
    hHc.le hSc.le hLc.le hEc.le hDc hCext.le
    (hweaken hHc.le (by norm_num) hHb) hSb
    (hweaken hLc.le (by norm_num) hLb) (hweaken hEc.le (by norm_num) hEb)
    hDb hPb hPb hPb hnorm
  exact ⟨hη, hηone, hs, hsone, hηε, hsource, hεs, hεnear, herr, hfar, hwindow,
    htrim, hWb, hbudget⟩

end TransposeFollowup.SL2Projection

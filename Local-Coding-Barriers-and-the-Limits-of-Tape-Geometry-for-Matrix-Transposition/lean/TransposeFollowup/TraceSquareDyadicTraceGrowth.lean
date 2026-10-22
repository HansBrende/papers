import TransposeFollowup.TraceSquareActualWordGrowth
import TransposeFollowup.TraceSquareSampleApplication
import TransposeFollowup.ScalarRingProjection

/-! Actual trace growth for the nondegenerate trace-square branch. The
same retained sample pays the scalar sum/product hypotheses, both mixed
readout coefficients, approximation errors and distance from the identity.
All constants and thresholds are chosen before the source family. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem exists_trace_square_dyadic_trace_growth {κ₀ Cext : ℝ}
    (hκ₀ : 0 < κ₀) (hκ₀one : κ₀ ≤ 1) (hCext : 0 < Cext) :
    ∃ Θ θ gain α₀ a₂ Ws : ℝ, ∃ J : ℕ,
      0 < Θ ∧ Θ < 1/4 ∧ 0 < θ ∧ θ ≤ Θ ∧
      0 < gain ∧ 691*Θ < 3*gain ∧ 0 < α₀ ∧ 0 < a₂ ∧ 0 < Ws ∧
      ∀ j : ℕ, J ≤ j →
        let η := (1/4 : ℝ)^j
        let ηn : ℝ≥0 := ⟨η, by positivity⟩
        ∃ k : ℕ, 0 < k ∧
          let δ := (1/2 : ℝ)^k
          let δn : ℝ≥0 := ⟨δ, by positivity⟩
          η ≤ δ ∧ η^(1-3*Θ) ≤ δ ∧ δ < 2*η^(1-3*Θ) ∧
        ∀ {ι : Type*} (f X : ι → G) (c t : ι → ℝ) (base z : G) (Dset : Set G)
          {A : Set G} {p q : G} {α : ℝ},
        1 ∈ A → A⁻¹=A → 0 < α → α ≤ α₀ → A ⊆ mobiusIdentityBall α →
        p ∈ A^34 → q ∈ A^34 → p*q ∈ A^34 →
        η^θ ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det| →
        z ∈ mobiusIdentityBall (1/2) → η^θ/32 ≤ dist (z : RMat) 1 →
        η^θ/32 ≤ |((z : RMat)-(Matrix.trace (z : RMat)/2) • (1 : RMat)).det| →
        base ∈ A → (∀ i, X i ∈ A) →
        (∀ i, (f i : RMat) = scalarAffine (z : RMat) (c i) (t i)) →
        (Set.range (fun i => (f i : RMat))).Nonempty →
        (∀ i, dist (f i : RMat) ((base⁻¹*X i : G) : RMat) ≤ 26214400*η^(1-θ)) →
        (∀ ρ : ℝ, η < ρ → ρ < η^(θ/2) →
          ∃ T : Finset G, (T : Set G) ⊆ A ∧
            Metric.IsSeparated (ENNReal.ofReal ρ) ((fun x : G => (x : RMat)) '' (T : Set G)) ∧
            ρ^(-κ₀) ≤ (T.card : ℝ)) →
        let N := (Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal
        let NV := (Metric.externalCoveringNumber ηn (Set.range (fun i => (f i : RMat))) : ℝ≥0∞).toReal
        let H := (419430400/η^θ+17)^4
        N ≤ η^(-(3-κ₀)) →
        (Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' (A^284)) : ℝ≥0∞).toReal ≤ η^(-θ)*N →
        (Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' (A^142)) : ℝ≥0∞).toReal ≤ η^(-θ)*N →
        (Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' Dset) : ℝ≥0∞).toReal ≤ η^(-θ)*N →
        (η^θ)^11*N^4 ≤ Cext*(9*(Metric.externalCoveringNumber ηn
          ((fun x : G => (x : RMat)) '' Dset) : ℝ≥0∞).toReal*H*NV)^3 →
        ∃ m : ℝ, 0 < m ∧ N ≤ Ws*η^(-(143*Θ))*m^3 ∧
          ∃ D : Finset G, D.Nonempty ∧ (D : Set G) ⊆ A^420 ∧
            (∀ w ∈ D, w ∈ mobiusIdentityBall (1/2) ∧ a₂*η^(3*Θ) ≤ dist (w : RMat) 1) ∧
            η^(-gain)*m < 25*(Metric.externalCoveringNumber δn
              ((D.image (fun w : G => Matrix.trace (w : RMat))) : Set ℝ) : ℝ≥0∞).toReal := by
  let κ := κ₀/12
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hκone : κ ≤ 1 := by dsimp only [κ]; linarith only [hκ₀one]
  obtain ⟨eRaw, Jg, heRaw, hJg, hscalar⟩ := ScalarMetric.scalar_sum_product_alternative hκ hκone
  let e := min eRaw 1
  have he : 0 < e := lt_min heRaw zero_lt_one
  have heone : e ≤ 1 := min_le_right _ _
  let Θ := min e κ₀/16384
  let θ := κ₀*Θ/1024
  let a := 5*Θ/16
  let gain := e/32
  let gexp := e/8
  obtain ⟨hΘ, hΘfour, hθ, hθΘ, _ha, _hproduct, _htrim₁, _htrim₂, _hnorm,
    _hretain, _hinverse, hfarExponent, _herror, _hspacing, hgain, hgainSquare, hgainStrong,
    hd, hdone, _hκ, _hκone, hgexp, hc, hfour, hjoint, hsizeMargin, herrorMargin, _⟩ :=
    trace_square_two_stage_exponent_margins hκ₀ hκ₀one he heone
  change 0 < Θ at hΘ
  change Θ < 1/4 at hΘfour
  change 0 < θ at hθ
  change θ ≤ Θ at hθΘ
  change 12*θ+a ≤ 3*Θ at hfarExponent
  change 0 < gain at hgain
  change 2*gain < gexp at hgainSquare
  change 691*Θ < 3*gain at hgainStrong
  obtain ⟨ρc, c₀, t₀, s₁, hρc, hc₀eq, _hc₀, ht₀, hc₀t₀, _hs₁, _hs₁eq, hreadout⟩ :=
    exists_actual_trace_square_readout_parameters
  let R := (4 : ℝ)^204
  let M := 128*R^2
  let Eerr := 1024*(2*R^2)^7*(8*R^2)
  let Ffar := ρc/(288*M^2)
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRtwo : 2 ≤ R := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by norm_num : 1 ≤ 204)
    rw [pow_one] at hh
    exact (by norm_num : (2 : ℝ) ≤ 4).trans hh
  have hRpow : (4 : ℝ)^2 ≤ R :=
    pow_le_pow_right₀ (by norm_num) (by norm_num : 2 ≤ 204)
  have hM : 32 ≤ M := by
    have hh : 1 ≤ R^2 := one_le_pow₀ hR
    dsimp only [M]
    linarith only [hh]
  have hEerr : 1 ≤ Eerr := by
    have hh : 1 ≤ R^2 := one_le_pow₀ hR
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num)
        (one_le_pow₀ (one_le_mul_of_one_le_of_one_le (by norm_num) hh)))
      (one_le_mul_of_one_le_of_one_le (by norm_num) hh)
  have hFfar : 0 < Ffar := by dsimp only [Ffar]; positivity
  obtain ⟨e₀, αsample, Cs, Ws, Vs, he₀, hαsample, hαsampleOne, hαsampleSmall,
    hCs, hWs, hVs, Jsample, hsample⟩ :=
    exists_trace_square_sample_bounds hκ₀ hκ₀one he heone hCext ht₀ hEerr hFfar
  obtain ⟨Jbudget, hbudget⟩ := exists_scalar_growth_budget_scale hd hdone he hκone
    hgexp hc (K₀ := 1) le_rfl hCs hVs he₀ hfour hjoint hsizeMargin herrorMargin Jg
  obtain ⟨Jsquare, hsquare⟩ := exists_dyadic_power_comparison
    (by norm_num : (0 : ℝ) < 560) hgainSquare
  let α₀ := min αsample (1/(4*(5 : ℝ)^420))
  have hα₀ : 0 < α₀ := by dsimp only [α₀]; positivity
  refine ⟨Θ, θ, gain, α₀, Ffar, Ws, max Jsample (max Jbudget Jsquare),
    hΘ, hΘfour, hθ, hθΘ, hgain, hgainStrong, hα₀, hFfar, hWs, ?_⟩
  intro j hj η ηn
  have hjsample : Jsample ≤ j := (le_max_left _ _).trans hj
  have hjbudget : Jbudget ≤ j := by omega
  have hjsquare : Jsquare ≤ j := by omega
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηone : η ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨k, hk, hηδ, hδlo, hδhi, hK, hC, hproj, hpoint, hcoeff, _herrorBudget, hlog⟩ :=
    hbudget j hjbudget
  simp only [one_mul] at hK hproj hcoeff
  let δ := (1/2 : ℝ)^k
  let δn : ℝ≥0 := ⟨δ, by positivity⟩
  let K := η^(-gexp)
  let C := Cs*η^(-(100*Θ))
  let ε := e₀*η^(1-2*θ)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  refine ⟨k, hJg.trans_le hk, hηδ, hδlo, hδhi, ?_⟩
  intro ι f X c t base z Dset A p q α
    hA1 hAi hα hαbound hA hp hq hpq hspan hz hzfar hzdet hbase hX hform hfn hclose hdist
    N NV H hNbound h284 h142 hmixed hcube
  have hαsampleBound : α ≤ αsample := hαbound.trans (min_le_left _ _)
  have hαone : α ≤ 1 := hαsampleBound.trans hαsampleOne
  have hαsmall : 4*(5 : ℝ)^102*α ≤ 1 :=
    (mul_le_mul_of_nonneg_left hαsampleBound (by positivity)).trans hαsampleSmall
  have hαwords : (5 : ℝ)^420*α ≤ 1/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*(5 : ℝ)^420)).mp
      (hαbound.trans (min_le_right _ _))
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
  obtain ⟨_hηδ, _hεδ, hscalarError, hfarError, hclose', T, hT, hTfar, _hTsign, hTnear,
    hZ, _hZcard, hZrange, hZsep, hglobal, hsize, hball⟩ :=
    hsample j hjsample δ hδlo hδhi.le f X c t base z Dset
      hA1 hAi hα hαsampleBound hA hp hq hpq hspan hz hzfar hzdet hbase hX hform hfn hclose
      hdist hNbound h284 h142 hmixed hcube
  let Z := T.image (fun i => traceSquareScalar (f i))
  let b := (z : RMat)-(Matrix.trace (z : RMat)/2) • (1 : RMat)
  let σ := t₀*δ*η^(-(12*θ))
  let ρ := ρc*η^(12*θ)
  have hb : Matrix.trace b = 0 := (centered_generator_coordinates (z : RMat)).1
  have hdet : b.det ≠ 0 := abs_pos.mp ((by positivity : 0 < η^θ/32).trans_le hzdet)
  obtain ⟨hσ, hδσ, _hσ₁, _hwindow, g, hgA, hD, hD', _⟩ :=
    hreadout (a := a) hη hηone hθ.le hδ hδhi.le
      hA1 hAi hα hαone hA hαsmall hp hq hpq hspan hz hzfar hdet
  have hZpos : 0 < (Z.card : ℝ) := by exact_mod_cast hZ.card_pos
  change (Z.card : ℝ) ≤ Vs*η^(-(1-κ₀/3+83*θ)) at hsize
  have hsize' : (Z.card : ℝ) ≤ Vs*η^(-(1-κ₀/3+84*Θ)) :=
    hsize.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hη hηone (by linarith only [hθΘ, hΘ])) hVs.le)
  have hball' (v r : ℝ) (hdr : δ ≤ r) (hrone : r ≤ 1) :
      OAI.Falconer.scalarBallMass Z v r ≤ C*r^(2*κ)*Z.card := by
    have hh : r^(κ₀/3) ≤ r^(2*κ) := Real.rpow_le_rpow_of_exponent_ge
      (hδ.trans_le hdr) hrone (by dsimp only [κ]; linarith only [hκ₀])
    exact (hball v r hdr).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hh (zero_le_one.trans hC)) (Nat.cast_nonneg _))
  have hW : Real.exp (e*((k+1 : ℕ) : ℝ)*Real.log 2) ≤
      Real.exp (eRaw*((k+1 : ℕ) : ℝ)*Real.log 2) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
      (Real.log_nonneg (by norm_num))
  have hgrowth := hscalar k hk K C hK hC (hproj.trans hW) (hpoint.trans hW) (hcoeff.trans hW)
    Z hZ hZrange (fun x hx y hy hxy => hδσ.trans (hZsep x hx y hy hxy).le)
    (hlog Z.card hZpos hsize') hball'
  let P := T.image (fun i => (f i, base⁻¹*X i))
  have hP : P.Nonempty := hT.image _
  have hPZ : P.image (fun w => traceSquareScalar w.1) = Z := by
    simp only [P, Z, Finset.image_image, Function.comp_def]
  have hAb : A ⊆ matrixEntryBox 2 :=
    hA.trans (mobiusIdentityBall_subset_entryBox_two hα hαone)
  have hsource (i : ι) : base⁻¹*X i ∈ A^2 := by
    have hi : base⁻¹ ∈ A := by simpa only [hAi] using Set.inv_mem_inv.mpr hbase
    simpa only [pow_two] using Set.mul_mem_mul hi (hX i)
  have hgBound (i j : Fin 2) : |g i j| ≤ R := by
    simpa only [show (2 : ℝ)*2=4 by norm_num] using
      set_pow_subset_matrixEntryBox hAb 204 hgA i j
  have hPsource : ∀ w ∈ P, w.2 ∈ A^2 := by
    intro w hw
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hw
    exact hsource i
  have hPform : ∀ w ∈ P, ∃ c t : ℝ, (w.1 : RMat) = scalarAffine b c t := by
    intro w hw
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨c i+t i*Matrix.trace (z : RMat)/2, t i, ?_⟩
    rw [hform i, scalarAffine_recenter]
  have hPnear : ∀ w ∈ P, dist (w.1 : RMat) 1 ≤ 1/64 := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact hTnear i hi
  have hPfar : ∀ w ∈ P, η^a ≤ dist (w.1 : RMat) 1 := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact (hTfar i hi).le
  have hPbound : ∀ w ∈ P, ∀ i j, |w.1 i j| ≤ R ∧ |w.2 i j| ≤ R := by
    intro w hw i j
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    have hfnear : f v ∈ mobiusIdentityBall (1/2) :=
      (mobiusIdentityBall_iff_frobenius_dist _ (by norm_num)).mpr
        ((hTnear v hv).trans_lt (by norm_num))
    refine ⟨(mobiusIdentityBall_subset_entryBox_two (by norm_num) (by norm_num) hfnear i j).trans hRtwo, ?_⟩
    have hh := set_pow_subset_matrixEntryBox hAb 2 (hsource v) i j
    simp only [show (2 : ℝ)*2=4 by norm_num] at hh
    exact hh.trans hRpow
  have hPclose : ∀ w ∈ P, dist (w.1 : RMat) (w.2 : RMat) ≤ ε := by
    intro w hw
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hw
    exact hclose' i
  obtain ⟨hbn, hbd⟩ := centered_near_identity_generator_bounds z hz
  have hbg : ‖matrixConjugationLinear g b‖ ≤ M := by
    have hh := (matrixConjugation_trace_det_norm g b (zero_le_one.trans hR) hgBound hbn).2.2
    convert hh using 1
    dsimp only [M]
    ring
  have hscale : δ ≤ (3*ρ/256)*σ := by
    have hp : η^(12*θ)*η^(-(12*θ)) = 1 := by
      rw [← Real.rpow_add hη, add_neg_cancel, Real.rpow_zero]
    have heq : (3*ρ/256)*σ = (c₀*t₀)*δ := by
      dsimp only [ρ, σ]
      rw [hc₀eq]
      calc
        _ = (3*ρc/256*t₀)*δ*(η^(12*θ)*η^(-(12*θ))) := by ring
        _ = _ := by rw [hp, mul_one]
    rw [heq]
    exact le_mul_of_one_le_left hδ.le hc₀t₀
  have hserr : 1024*(2*R^2)^7*(8*R^2*ε) ≤ δ := by
    simpa only [Eerr, mul_assoc] using hscalarError
  have hferr : 512*(2*R^2)^7*(8*R^2*ε) ≤ ρ*η^a/(288*M^2) := by
    have heq : Ffar*η^(12*θ+a) = ρ*η^a/(288*M^2) := by
      rw [Real.rpow_add hη]
      dsimp only [Ffar, ρ]
      ring
    rw [heq] at hfarError
    have hh : 512*(2*R^2)^7*(8*R^2*ε) ≤ Eerr*ε := by
      dsimp only [Eerr]
      nlinarith only [show 0 ≤ (2*R^2)^7*(8*R^2*ε) by positivity]
    exact hh.trans hfarError
  have hsquare' : 560*(η^(-gain))^2 ≤ K := by
    have hp : (η^(-gain))^2 = η^(-(2*gain)) := by
      rw [← Real.rpow_mul_natCast hη.le]
      congr 1
      norm_num
      ring
    rw [hp]
    exact hsquare j hjsquare
  have hsep : ∀ x ∈ P.image (fun w => traceSquareScalar w.1),
      ∀ y ∈ P.image (fun w => traceSquareScalar w.1), x ≠ y → σ ≤ |x-y| := by
    rw [hPZ]
    exact fun x hx y hy hxy => (hZsep x hx y hy hxy).le
  rw [← hPZ] at hgrowth
  obtain ⟨D, hDnonempty, hDpower, hDgeom, hDgrowth⟩ :=
    trace_square_actual_word_growth P b g hP hA1 hAi hα hαone hA
      (show 0 < δn from hδ) hR hε hM (show 0 < ρ by dsimp only [ρ]; positivity)
      (show 0 ≤ σ from hσ.le) hb hdet (hbn.trans hM) hbd hbg hD hD'
      hPsource hgA hPform hPnear hPfar hPbound hgBound hPclose hscale hserr hferr hsquare' hsep hgrowth
  rw [hPZ] at hDgrowth
  refine ⟨Z.card, hZpos, hglobal, D, hDnonempty, hDpower, ?_, hDgrowth⟩
  intro w hw
  obtain ⟨hnear, hfar⟩ := hDgeom w hw
  refine ⟨(mobiusIdentityBall_iff_frobenius_dist _ (by norm_num)).mpr
    ((hnear.trans hαwords).trans_lt (by norm_num)), ?_⟩
  have hpow : Ffar*η^(3*Θ) ≤ Ffar*η^(12*θ+a) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hη hηone hfarExponent) hFfar.le
  apply hpow.trans
  convert hfar using 1
  rw [Real.rpow_add hη]
  dsimp only [Ffar, ρ]
  ring

end TransposeFollowup.SL2Projection

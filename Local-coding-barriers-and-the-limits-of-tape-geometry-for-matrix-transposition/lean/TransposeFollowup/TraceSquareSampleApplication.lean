import TransposeFollowup.TraceSquareJointBudgets
import TransposeFollowup.TraceSquareTwoStageSample
import TransposeFollowup.SourceScalarConcentration
import TransposeFollowup.CommutingFamilyCubicBound

/-! Apply the joint numerical budgets to the original source family.
The sample, scalar separation, global normalization, cardinality bound
and interval concentration are obtained together. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius BoundedCoordinatePacking
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group
local notation "H₀" => (4 : ℝ)^34
local notation "R₀" => (4 : ℝ)^68
local notation "M₀" => 128*R₀^2

theorem exists_trace_square_sample_bounds {κ e Cext t₀ Eerr Ffar : ℝ}
    (hκ : 0 < κ) (hκone : κ ≤ 1) (he : 0 < e) (heone : e ≤ 1)
    (hCext : 0 < Cext) (ht₀ : 1 ≤ t₀) (hEerr : 1 ≤ Eerr) (hFfar : 0 < Ffar) :
    let Θ := min e κ/16384
    let θ := κ*Θ/1024
    let a := 5*Θ/16
    ∃ e₀ α₀ Cs Ws Vs : ℝ,
      0 < e₀ ∧ 0 < α₀ ∧ α₀ ≤ 1 ∧ 4*(5 : ℝ)^102*α₀ ≤ 1 ∧
      1 ≤ Cs ∧ 0 < Ws ∧ 0 < Vs ∧
      ∃ J₀ : ℕ, ∀ j : ℕ, J₀ ≤ j →
        let η := (1/4 : ℝ)^j
        let ηn : ℝ≥0 := ⟨η, by positivity⟩
        let ε := e₀*η^(1-2*θ)
        ∀ δ : ℝ, η^(1-3*Θ) ≤ δ → δ ≤ 2*η^(1-3*Θ) →
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
            ρ^(-κ) ≤ (T.card : ℝ)) →
        let N := (Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal
        let NV := (Metric.externalCoveringNumber ηn (Set.range (fun i => (f i : RMat))) : ℝ≥0∞).toReal
        let H := (419430400/η^θ+17)^4
        N ≤ η^(-(3-κ)) →
        (Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' (A^284)) : ℝ≥0∞).toReal ≤ η^(-θ)*N →
        (Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' (A^142)) : ℝ≥0∞).toReal ≤ η^(-θ)*N →
        (Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' Dset) : ℝ≥0∞).toReal ≤ η^(-θ)*N →
        (η^θ)^11*N^4 ≤ Cext*(9*(Metric.externalCoveringNumber ηn
          ((fun x : G => (x : RMat)) '' Dset) : ℝ≥0∞).toReal*H*NV)^3 →
        η ≤ δ ∧ ε ≤ δ ∧ Eerr*ε ≤ δ ∧ Eerr*ε ≤ Ffar*η^(12*θ+a) ∧
        (∀ i, dist (f i : RMat) ((base⁻¹*X i : G) : RMat) ≤ ε) ∧
        ∃ T : Finset ι, T.Nonempty ∧
          (∀ i ∈ T, η^a < dist (f i : RMat) 1) ∧
          (∀ i ∈ T, ∀ j ∈ T, 0 ≤ t i*t j) ∧
          (∀ i ∈ T, dist (f i : RMat) 1 ≤ 1/64) ∧
          let Z := T.image (fun i => traceSquareScalar (f i))
          Z.Nonempty ∧ Z.card = T.card ∧
          (∀ x ∈ Z, 1 ≤ x ∧ x ≤ 2) ∧
          (∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → t₀*δ*η^(-(12*θ)) < |x-y|) ∧
          N ≤ (Ws*η^(-(143*Θ)))*(Z.card : ℝ)^3 ∧
          (Z.card : ℝ) ≤ Vs*η^(-(1-κ/3+83*θ)) ∧
          (∀ w ρ : ℝ, δ ≤ ρ → OAI.Falconer.scalarBallMass Z w ρ ≤
            (Cs*η^(-(100*Θ)))*ρ^(κ/3)*(Z.card : ℝ)) := by
  classical
  intro Θ θ a
  have hH₀ : 1 ≤ H₀ := one_le_pow₀ (by norm_num)
  have hR₀ : 1 ≤ R₀ := one_le_pow₀ (by norm_num)
  have hR₂ : 2 ≤ R₀ := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by norm_num : 1 ≤ 68)
    rw [pow_one] at hh
    exact (by norm_num : (2 : ℝ) ≤ 4).trans hh
  have hM₀ : 1 ≤ M₀ := one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hR₀)
  obtain ⟨b, s₀, l, e₀, d, rc, hb, hs₀, _hl, he₀, hd, hrc, _hlEq, he₀Eq, hparams⟩ :=
    exists_scaled_extraction_parameters hH₀
      (by norm_num : (1 : ℝ) ≤ 2) hM₀
      (by norm_num : (0 : ℝ) < 1/32) (by norm_num : (1/32 : ℝ) ≤ 1)
  have he₀large : 26214400 ≤ e₀ := by
    rw [he₀Eq]
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4)
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hH₀ (by norm_num : (0 : ℝ) ≤ 4)) 6
    rw [show (4 : ℝ)^6 = 4096 by norm_num] at hh
    linarith only [hh]
  let s₁ := 3072*t₀/(1/32)
  have ht₀pos : 0 < t₀ := zero_lt_one.trans_le ht₀
  have hs₁ : 0 < s₁ := by dsimp only [s₁]; positivity
  let Cp := (8*(4 : ℝ)^142+1)^4*(8*((4 : ℝ)^142)^2+4*(4 : ℝ)^142+1)^κ
  obtain ⟨Cs, Ws, hCs, hWs, J₀, hbudgets⟩ := exists_trace_square_joint_budgets
    (Cp := Cp) (B := 2) (R := R₀) hκ hκone he heone hb hs₀ hs₁ he₀large
    hCext (by dsimp only [Cp]; positivity) (by norm_num) (by positivity) hEerr hFfar
  obtain ⟨Vs, hVs, hsizeBudget⟩ := exists_first_extraction_size_constant
    (B := 2) (R := R₀) hb hs₀ he₀.le (by norm_num) (by positivity)
  let α₀ := min (1/3200 : ℝ) (1/(4*(5 : ℝ)^102))
  have hα₀ : 0 < α₀ := by dsimp only [α₀]; positivity
  have hα₀one : α₀ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hα₀small : 4*(5 : ℝ)^102*α₀ ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*(5 : ℝ)^102)).mp
      (min_le_right (1/3200 : ℝ) (1/(4*(5 : ℝ)^102)))
    simpa only [mul_comm] using hh
  refine ⟨e₀, α₀, Cs, Ws, Vs, he₀, hα₀, hα₀one, hα₀small, hCs, hWs, hVs, J₀, ?_⟩
  intro j hj η ηn ε δ hδlower hδupper ι f X c t base z Dset A p q α
    hA1 hAi hα hαα₀ hA hp hq hpq hspan hz hfar hgap hbase hX hform hfn hclose₀
    hdistribution N NV H hNbound h284 h142 hmixed hcube
  obtain ⟨hη, hηone, hs, hsone, hηε, hsource, _hεs, hεnear, herr, hfarError,
    hwindow, htrim, hWbound, hQbudget⟩ := hbudgets j hj
  change 0 < η at hη
  change η ≤ 1 at hηone
  change η ≤ ε at hηε
  change ε ≤ 1/128 at hεnear
  change Eerr*ε ≤ η^(1-3*Θ) at herr
  have hΘ : 0 < Θ := by dsimp only [Θ]; positivity
  have hθ : 0 ≤ θ := by dsimp only [θ]; positivity
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hδ : 0 < δ := (Real.rpow_pos_of_pos hη _).trans_le hδlower
  have hεδ : ε ≤ δ := (le_mul_of_one_le_left hε hEerr).trans (herr.trans hδlower)
  have hηδ : η ≤ δ := hηε.trans hεδ
  have hαone : α ≤ 1 := hαα₀.trans hα₀one
  have hsmall102 : 4*(5 : ℝ)^102*α ≤ 1 :=
    (mul_le_mul_of_nonneg_left hαα₀ (by positivity)).trans hα₀small
  have hαsmall : 2*(5 : ℝ)^34*α ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 5) (by norm_num : 34 ≤ 102)) hα.le
    linarith only [hh, hsmall102, mul_pos (by positivity : 0 < (5 : ℝ)^102) hα]
  have hnear : 25*α+ε ≤ 1/64 := by
    have ha : α ≤ 1/3200 := hαα₀.trans (min_le_left _ _)
    linarith only [ha, hεnear]
  have hclose (i : ι) : dist (f i : RMat) ((base⁻¹*X i : G) : RMat) ≤ ε :=
    (hclose₀ i).trans hsource
  have hinv : base⁻¹ ∈ A := by simpa only [hAi] using Set.inv_mem_inv.mpr hbase
  have hfnear (i : ι) : dist (f i : RMat) 1 ≤ 1/64 := by
    have hsource : base⁻¹*X i ∈ A^2 := by
      simpa only [pow_two] using Set.mul_mem_mul hinv (hX i)
    have hh := set_pow_dist_from_one_le hα hαone hA 2 _ hsource
    norm_num only [show (5 : ℝ)^2 = 25 by norm_num] at hh
    exact (dist_triangle _ ((base⁻¹*X i : G) : RMat) 1).trans
      ((add_le_add (hclose i) hh).trans (by linarith only [hnear]))
  have hf (i : ι) (k m : Fin 2) : |f i k m| ≤ 2 := by
    have hh := (entry_error_le_frobenius_dist (f i : RMat) 1 k m).trans (hfnear i)
    have hI : |(1 : RMat) k m| ≤ 1 := by fin_cases k <;> fin_cases m <;> norm_num
    have ht := abs_sub_le (f i k m) ((1 : RMat) k m) 0
    simp only [sub_zero] at ht
    linarith only [hh, hI, ht]
  let σ₀ : ℝ≥0 := ⟨s₀*η^(1-9*θ), by positivity⟩
  let σ₁ : ℝ≥0 := ⟨s₁*η^(1-(3*Θ+13*θ+a)), by positivity⟩
  let δs := t₀*δ*η^(-(12*θ))
  let Kinv := 3072/((η^θ/32)*η^a)
  let C₀ := 6561*(4*(σ₀ : ℝ)/η+1)^4
  let C₁ := 6561*(4*(σ₁ : ℝ)/η+1)^4
  let L := ((binCount 2 (b*η^(11*θ))^4 : ℕ) : ℝ)
  let E := (4*(20*(2*R₀)^10*ε+2*R₀*η)/η+1)^4
  let W₀ := Cext*(9*η^(-θ)*H)^3/(η^θ)^11
  let W := W₀*(4*C₀*C₁)^3
  let Anear := E*(Cp*η^(-θ)*η^(-θ)*η^(-((θ/2)*κ)))*
    (40*(2*R₀)^11*(η^a+ε))^κ
  have hσ₀ : 0 < σ₀ := by change 0 < s₀*η^(1-9*θ); positivity
  have hr₀ : 0 < (1/32)*η^(2*θ) := by positivity
  have hfarWeak : (1/32)*η^(2*θ) ≤ dist (z : RMat) 1 := by
    apply le_trans ?_ hfar
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hη hηone
        (by linarith only [hθ] : θ ≤ 2*θ)) (by norm_num : (0 : ℝ) ≤ 1/32)
  have hd₀ : 0 < η^θ := Real.rpow_pos_of_pos hη θ
  have hP : 1 ≤ η^(-θ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hη hηone (neg_nonpos.mpr hθ)
  obtain ⟨hrone, hrsmall, hrabsorb, hbranch, hradius, hframe, hspacing, hησ₀, _⟩ :=
    hparams η θ hη hηone hθ
  obtain ⟨hδs, _hδδs, hσ₁, hspacing₁, _⟩ := trace_square_scalar_spacing
    (a := a) (l₀ := 1/32) hη hηone hθ (by norm_num) ht₀ hδ hδupper (le_refl s₁)
  have hKrepr : Kinv = (3072/(1/32))*η^(-(θ+a)) := by
    dsimp only [Kinv]
    rw [Real.rpow_neg hη.le, Real.rpow_add hη]
    field_simp
  have hspacingFinal : Kinv*δs ≤ 2*(σ₁ : ℝ) := by rw [hKrepr]; exact hspacing₁
  have hAfin : Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' A) ≠ ⊤ :=
    finite_coveringNumber_of_entry_bound (by norm_num : (0 : ℝ) ≤ 2) hη
      (by rintro y ⟨x, hx, rfl⟩; exact mobiusIdentityBall_subset_entryBox_two hα hαone (hA hx))
  have hNlower := coveringNumber_lower_of_distribution (η := ηn) hη hwindow hAfin hdistribution
  have hN : 0 < N := (Real.rpow_pos_of_pos (by positivity : 0 < 2*η) (-κ)).trans_le hNlower
  have hnormalize : N ≤ W₀*NV^3 := coefficient_cube_normalization
    (by positivity) hCext hN ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (by positivity) (by dsimp only [H]; positivity) hcube hmixed
  change 32*L^3*C₀^3*W₀*(Anear+1/(2*η)^(-κ)) ≤ 1 at htrim
  let U := E*(Cp*η^(-θ)*η^(-θ)*η^(-((θ/2)*κ))*
    (40*(2*R₀)^11*(η^a+ε))^κ*N)
  have hU : U = Anear*N := by dsimp only [U, Anear]; ring
  have hbudget := trim_budget_of_global_normalization
    (by positivity : 0 < (2*η)^(-κ)) hNlower ENNReal.toReal_nonneg
    (show 0 ≤ L from Nat.cast_nonneg _) (by dsimp only [C₀]; positivity)
    (by dsimp only [Anear, E, Cp]; positivity) hnormalize
    hU.le htrim
  have hout : η ≤ 40*(2*R₀)^11*(η^a+ε) := by
    have hfac : 1 ≤ 40*(2*R₀)^11 :=
      one_le_mul_of_one_le_of_one_le (by norm_num)
        (one_le_pow₀ (one_le_mul_of_one_le_of_one_le (by norm_num) hR₀))
    exact hηε.trans ((le_add_of_nonneg_left hs.le).trans
      (le_mul_of_one_le_left (by positivity) hfac))
  obtain ⟨T, hTn, hTfar, hTsign, hTnear, hTsep, hTinv, hZn, hZcard, hZrange,
    hZsep, _hVfin, hretain, hupper⟩ :=
    exists_actual_trace_square_two_stage_sample (η := ηn) (σ₀ := σ₀) (σ₁ := σ₁)
      f X c t base hA1 hAi hα hαone hA hαsmall hp hq hpq hd₀ hspan hz hr₀ hfarWeak
      (by norm_num : (1 : ℝ) ≤ 2) hM₀ le_rfl
      (show 0 < b*η^(11*θ) by positivity) (show 0 ≤ rc*η^(9*θ) by positivity) hrone
      hf hform hbranch hradius.le (show 0 < d*η^(9*θ) by positivity) hframe.le hrsmall hrabsorb
      hspacing hbase hX hR₂ le_rfl hε hη hclose hs hsone
      hP (zero_le_one.trans hP) hκ.le (by positivity : 0 ≤ θ/2) hηone hout
      h284 h142 hdistribution hfn hσ₀ (show ηn ≤ σ₀ from hησ₀) hσ₁
      (by positivity : 0 < η^θ/32) hgap hnear hδs hspacingFinal
      hbudget
  let Z := T.image (fun i => traceSquareScalar (f i))
  have hglobal : N ≤ W*(Z.card : ℝ)^3 := by
    calc
      N ≤ W₀*NV^3 := hnormalize
      _ ≤ W₀*((4*C₀*C₁)*(Z.card : ℝ))^3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ENNReal.toReal_nonneg hretain 3)
          (by dsimp only [W₀, H]; positivity)
      _ = _ := by simp only [W, mul_pow, mul_assoc]
  have hnormalized : N ≤ W*(Fintype.card ↥T : ℝ)^3 := by
    have hZcard' : Z.card = T.card := hZcard
    simpa only [Fintype.card_coe, hZcard'] using hglobal
  have hpacksep (i k : ↥T) (hne : i ≠ k) :
      10*2*M₀*(384*M₀^4/(d*η^(9*θ))*η) < dist (f i : RMat) (f k : RMat) := by
    exact hspacing.trans_lt ((le_max_left _ _).trans_lt
      (hTsep i i.property k k.property (fun hh => hne (Subtype.ext hh))))
  have hdiam (w ρ : ℝ) (_hρ : 0 ≤ ρ) (i k : ↥T)
      (hi : |traceSquareScalar (f i)-w| ≤ ρ) (hk : |traceSquareScalar (f k)-w| ≤ ρ) :
      dist (f i : RMat) (f k : RMat) ≤ 2*Kinv*ρ := by
    have hh := abs_sub_le (traceSquareScalar (f i)) w (traceSquareScalar (f k))
    rw [abs_sub_comm w] at hh
    have hscalar : |traceSquareScalar (f i)-traceSquareScalar (f k)| ≤ 2*ρ := by
      linarith only [hh, hi, hk]
    calc
      _ ≤ Kinv*|traceSquareScalar (f i)-traceSquareScalar (f k)| := hTinv i i.property k k.property
      _ ≤ Kinv*(2*ρ) := mul_le_mul_of_nonneg_left hscalar (by dsimp only [Kinv]; positivity)
      _ = _ := by ring
  have hinj : Function.Injective (fun i : ↥T => traceSquareScalar (f i)) := by
    intro i k heq
    change traceSquareScalar (f i) = traceSquareScalar (f k) at heq
    by_contra hne
    have hpos := (le_max_left _ _).trans_lt (hTsep i i.property k k.property
      (fun hh => hne (Subtype.ext hh)))
    have hzero := hTinv i i.property k k.property
    rw [heq, sub_self, abs_zero, mul_zero] at hzero
    have hσpos : 0 < (σ₀ : ℝ) := hσ₀
    linarith only [hpos, hzero, hσpos]
  have hZeq : Finset.univ.image (fun i : ↥T => traceSquareScalar (f i)) = Z := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists, Z, exists_prop]
  have hQbudget' :
      (4*L^3*(E*(Cp*η^(-θ)*η^(-θ)*η^(-((θ/2)*κ)))*
        (40*(2*R₀)^11*(Kinv+2))^κ+(2 : ℝ)^κ))*W ≤ (Cs*η^(-(100*Θ)))^3 := by
    change (4*L^3*(E*(Cp*η^(-θ)*η^(-θ)*η^(-((θ/2)*κ)))*
      (40*(2*R₀)^11*(3072/(((1/32)*η^θ)*η^a)+2))^κ+(2 : ℝ)^κ))*W ≤
      (Cs*η^(-(100*Θ)))^3 at hQbudget
    simpa only [show (1/32 : ℝ)*η^θ = η^θ/32 by ring] using hQbudget
  have hball := source_scalar_sample_concentration (η := ηn)
    (fun i : ↥T => f i) (fun i : ↥T => X i) (fun i => c i) (fun i => t i)
    (fun i => traceSquareScalar (f i)) base
    hA1 hAi hα hαone hA hαsmall hp hq hpq hd₀ hspan hz hr₀ hfarWeak
    (by norm_num : (1 : ℝ) ≤ 2) hM₀ le_rfl
    (show 0 < b*η^(11*θ) by positivity) (show 0 ≤ rc*η^(9*θ) by positivity) hrone
    (fun i => hf i) (fun i => hform i) hbranch hradius.le
    (show 0 < d*η^(9*θ) by positivity) hframe.le hrsmall hrabsorb hpacksep
    hbase (fun i => hX i) hR₂ le_rfl hε hη (fun i => hclose i)
    hP (zero_le_one.trans hP) hκ.le (by positivity : 0 ≤ θ/2) hηone h284 h142 hdistribution
    hwindow (by dsimp only [Kinv]; positivity) hdiam hinj hnormalized
    (Cs*η^(-(100*Θ))) (by positivity) hQbudget'
  rw [hZeq] at hball
  obtain ⟨_, _, hcubic⟩ := commuting_family_cubic_bound (η := ηn) (σ := σ₀) f X c t base
    hA1 hAi hα hαone hA hαsmall hp hq hpq hd₀ hspan hz hr₀ hfarWeak
    (by norm_num : (1 : ℝ) ≤ 2) hM₀ le_rfl
    (show 0 < b*η^(11*θ) by positivity) (show 0 ≤ rc*η^(9*θ) by positivity) hrone
    hf hform hbranch hradius.le (show 0 < d*η^(9*θ) by positivity) hframe.le hrsmall hrabsorb
    hbase hX hR₂ le_rfl hε hη hσ₀ hclose hfn hspacing
  have hsize := hsizeBudget η θ κ N
    (Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' (A^142)) : ℝ≥0∞).toReal
    NV Z.card hη hηone hθ (hκone.trans (by norm_num)) (Nat.cast_nonneg _) ENNReal.toReal_nonneg
    hupper hcubic hNbound h142
  refine ⟨hηδ, hεδ, herr.trans hδlower, hfarError, hclose, T, hTn, hTfar, hTsign, hTnear,
    hZn, hZcard, hZrange, hZsep, ?_, hsize, ?_⟩
  · exact hglobal.trans (mul_le_mul_of_nonneg_right hWbound (by positivity))
  · intro w ρ hδρ
    exact hball w ρ (hηδ.trans hδρ) (hεδ.trans hδρ)

end TransposeFollowup.SL2Projection

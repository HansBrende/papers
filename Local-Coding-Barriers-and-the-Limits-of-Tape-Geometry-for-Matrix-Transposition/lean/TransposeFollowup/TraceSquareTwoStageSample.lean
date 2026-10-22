import TransposeFollowup.SourceResampling
import TransposeFollowup.TraceSquareSourceSample

/-! Trim at the fine matrix scale before imposing the final scalar spacing.
The first retention factor enters the trimming budget; the second is paid
only after a far, single-sign branch has already been obtained. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius BoundedCoordinatePacking
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem exists_actual_trace_square_two_stage_sample {ι : Type*}
    (f X : ι → G) (c t : ι → ℝ) (base : G) {A : Set G} {p q z : G}
    {α d₀ r₀ B M r δ d R ε s K J κ γ Lgap δs : ℝ} {η σ₀ σ₁ : ℝ≥0}
    (hA1 : 1 ∈ A) (hAi : A⁻¹ = A) (hα : 0 < α) (hαone : α ≤ 1)
    (hA : A ⊆ mobiusIdentityBall α) (hαsmall : 2 * (5 : ℝ) ^ 34 * α ≤ 1)
    (hp : p ∈ A ^ 34) (hq : q ∈ A ^ 34) (hpq : p * q ∈ A ^ 34)
    (hd₀ : 0 < d₀)
    (hspan : d₀ ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det|)
    (hz : z ∈ mobiusIdentityBall (1 / 2)) (hr₀ : 0 < r₀)
    (hfar : r₀ ≤ dist (z : RMat) 1)
    (hB : 1 ≤ B) (hM : 1 ≤ M) (hscale : 128 * ((4 : ℝ) ^ 68) ^ 2 ≤ M)
    (hδ : 0 < δ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hf : ∀ x i j, |f x i j| ≤ B)
    (hform : ∀ x, (f x : RMat) = scalarAffine (z : RMat) (c x) (t x))
    (hbranch : 8 * B * δ ≤ 1) (hradius : 8 * B * δ ≤ (r₀ / 8) * r)
    (hd : 0 < d)
    (hframe : d ≤ (r₀ / 8) ^ 3 / (3456 * (96 * ((4 : ℝ) ^ 34) ^ 4 / d₀) ^ 3))
    (hsmall : 3 * M * r ≤ 1) (habsorb : 36864 * M ^ 6 * r ≤ d)
    (hseparation : 10 * B * M * (384 * M ^ 4 / d * (η : ℝ)) ≤ 2*(σ₀ : ℝ))
    (hbase : base ∈ A) (hX : ∀ i, X i ∈ A) (hBR : B ≤ R)
    (hHR : (4 : ℝ) ^ 68 ≤ R) (hε : 0 ≤ ε) (hη : 0 < η)
    (he : ∀ i, dist (f i : RMat) ((base⁻¹ * X i : G) : RMat) ≤ ε)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hK : 1 ≤ K) (hJ : 0 ≤ J) (hκ : 0 ≤ κ) (hγ : 0 ≤ γ) (hηone : (η : ℝ) ≤ 1)
    (houtRadius : (η : ℝ) ≤ 40 * (2 * R) ^ 11 * (s + ε))
    (hproduct : (Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' (A ^ 284)) : ℝ≥0∞).toReal ≤
        K * (Metric.externalCoveringNumber η
          ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal)
    (hsize : (Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' (A ^ 142)) : ℝ≥0∞).toReal ≤
        J * (Metric.externalCoveringNumber η
          ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal)
    (hdistribution : ∀ ρ : ℝ, (η : ℝ) < ρ → ρ < (η : ℝ) ^ γ →
      ∃ T : Finset G, (T : Set G) ⊆ A ∧
        Metric.IsSeparated (ENNReal.ofReal ρ)
          ((fun x : G => (x : RMat)) '' (T : Set G)) ∧
        ρ ^ (-κ) ≤ (T.card : ℝ))
    (hfn : (Set.range (fun i => (f i : RMat))).Nonempty)
    (hσ₀ : 0 < σ₀) (hησ₀ : η ≤ σ₀) (hσ₁ : 0 < σ₁) (hLgap : 0 < Lgap)
    (hgap : Lgap ≤ |((z : RMat) - (Matrix.trace (z : RMat)/2) • (1 : RMat)).det|)
    (hnear : 25*α + ε ≤ 1/64) (hδs : 0 < δs)
    (hspacing : 3072/(Lgap*s)*δs ≤ 2*(σ₁ : ℝ)) :
    let Bpow := (4 : ℝ)^142
    let ρ := 40*(2*R)^11*(s+ε)
    let E := (4*(20*(2*R)^10*ε + 2*R*(η : ℝ))/(η : ℝ)+1)^4
    let L := binCount B δ ^ 4
    let U := E*((8*Bpow+1)^4*(8*Bpow^2+4*Bpow+1)^κ*K*J*
      (η : ℝ)^(-(γ*κ))*ρ^κ*
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal)
    let C₀ := 6561*(4*(σ₀ : ℝ)/(η : ℝ)+1)^4
    let C₁ := 6561*(4*(σ₁ : ℝ)/(η : ℝ)+1)^4
    let V := (Metric.externalCoveringNumber η
      (Set.range (fun i => (f i : RMat))) : ℝ≥0∞).toReal
    32*(L : ℝ)^3*(U+1)*C₀^3 ≤ V^3 →
    ∃ T : Finset ι, T.Nonempty ∧
      (∀ i ∈ T, s < dist (f i : RMat) 1) ∧
      (∀ i ∈ T, ∀ j ∈ T, 0 ≤ t i * t j) ∧
      (∀ i ∈ T, dist (f i : RMat) 1 ≤ 1/64) ∧
      (∀ i ∈ T, ∀ j ∈ T, i ≠ j → max (2*(σ₀ : ℝ)) (2*(σ₁ : ℝ)) < dist (f i : RMat) (f j : RMat)) ∧
      (∀ i ∈ T, ∀ j ∈ T,
        dist (f i : RMat) (f j : RMat) ≤
          3072/(Lgap*s)*|traceSquareScalar (f i)-traceSquareScalar (f j)|) ∧
      let Z := T.image (fun i => traceSquareScalar (f i))
      Z.Nonempty ∧ Z.card = T.card ∧
      (∀ x ∈ Z, 1 ≤ x ∧ x ≤ 2) ∧
      (∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → δs < |x-y|) ∧
      Metric.externalCoveringNumber η (Set.range (fun i => (f i : RMat))) ≠ ⊤ ∧
      V ≤ 4*C₀*C₁*(Z.card : ℝ) ∧
      (Z.card : ℝ) ≤ V := by
  classical
  intro Bpow ρ E L U C₀ C₁ V hbudget
  let δ₀ := (Lgap*s/3072)*(σ₀ : ℝ)
  have hδ₀ : 0 < δ₀ := by dsimp only [δ₀]; positivity
  have hspacing₀ : 3072/(Lgap*s)*δ₀ ≤ 2*(σ₀ : ℝ) := by
    have heq : 3072/(Lgap*s)*δ₀ = (σ₀ : ℝ) := by
      dsimp only [δ₀]
      field_simp
    rw [heq]
    linarith only [σ₀.coe_nonneg]
  obtain ⟨T₀, hT₀n, hT₀far, hT₀sign, hT₀near, hT₀sep, hT₀inv,
      _, hZ₀card, hZ₀range, _, hfin, hretain₀, hlower₀⟩ :=
    exists_actual_trace_square_source_sample f X c t base
      hA1 hAi hα hαone hA hαsmall hp hq hpq hd₀ hspan hz hr₀ hfar
      hB hM hscale hδ hr hr1 hf hform hbranch hradius hd hframe hsmall habsorb
      hseparation hbase hX hBR hHR hε hη he hs hs1 hK hJ hκ hγ hηone
      houtRadius hproduct hsize hdistribution hfn hσ₀ hησ₀ hLgap hgap hnear
      hδ₀ hspacing₀ hbudget
  have hT₀sepη (i : ι) (hi : i ∈ T₀) (j : ι) (hj : j ∈ T₀) (hne : i ≠ j) :
      2*(η : ℝ) < dist (f i : RMat) (f j : RMat) := by
    exact (mul_le_mul_of_nonneg_left (show (η : ℝ) ≤ σ₀ from hησ₀)
      (by norm_num : (0 : ℝ) ≤ 2)).trans_lt (hT₀sep i hi j hj hne)
  obtain ⟨T, hTT₀, hTn, hTsep, hZn, hZcard, hZsep, hretain₁⟩ :=
    exists_scalar_source_subsample (fun i => (f i : RMat))
      (fun i => traceSquareScalar (f i)) T₀ (zero_le_one.trans hB) hη hσ₁ hT₀n
      (fun i _ => hf i) hT₀sepη (by positivity) hδs.le hspacing hT₀inv
  refine ⟨T, hTn, ?_, ?_, ?_, ?_, ?_, hZn, hZcard, ?_, hZsep, hfin, ?_, ?_⟩
  · intro i hi
    exact hT₀far i (hTT₀ hi)
  · intro i hi j hj
    exact hT₀sign i (hTT₀ hi) j (hTT₀ hj)
  · intro i hi
    exact hT₀near i (hTT₀ hi)
  · intro i hi j hj hne
    exact max_lt (hT₀sep i (hTT₀ hi) j (hTT₀ hj) hne) (hTsep i hi j hj hne)
  · intro i hi j hj
    exact hT₀inv i (hTT₀ hi) j (hTT₀ hj)
  · intro x hx
    exact hZ₀range x (Finset.image_subset_image hTT₀ hx)
  · rw [hZ₀card] at hretain₀
    calc
      V ≤ (4*C₀)*(T₀.card : ℝ) := by
        convert hretain₀ using 1
        dsimp only [C₀]
        ring
      _ ≤ (4*C₀)*(C₁*((T.image (fun i => traceSquareScalar (f i))).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hretain₁ (by dsimp only [C₀]; positivity)
      _ = _ := by ring
  · rw [hZcard, hZ₀card] at *
    exact (show (T.card : ℝ) ≤ (T₀.card : ℝ) by exact_mod_cast Finset.card_le_card hTT₀).trans hlower₀

end TransposeFollowup.SL2Projection

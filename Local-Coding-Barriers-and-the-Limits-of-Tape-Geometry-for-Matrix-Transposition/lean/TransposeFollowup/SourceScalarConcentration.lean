import TransposeFollowup.ActualCentralizerSourcePacking
import TransposeFollowup.CubicSampleNormalization

/-! Reusable scalar concentration for an actual finite source family.
Only an interval inverse bound depends on the scalar coordinate. Matrix
packing, additive-one absorption and cubic normalization are shared by
the nilpotent and trace-square applications. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius BoundedCoordinatePacking
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem source_scalar_sample_concentration {ι : Type*} [Fintype ι]
    (f X : ι → G) (c t a : ι → ℝ) (base : G) {A : Set G} {p q z : G}
    {α d₀ r₀ B M r δ d R ε K J κ γ Kinv W : ℝ} {η : ℝ≥0}
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
    (hsep : ∀ x y, x ≠ y →
      10 * B * M * (384 * M ^ 4 / d * (η : ℝ)) < dist (f x : RMat) (f y : RMat))
    (hbase : base ∈ A) (hX : ∀ i, X i ∈ A) (hBR : B ≤ R)
    (hHR : (4 : ℝ) ^ 68 ≤ R) (hε : 0 ≤ ε) (hη : 0 < η)
    (he : ∀ i, dist (f i : RMat) ((base⁻¹ * X i : G) : RMat) ≤ ε)
    (hK : 1 ≤ K) (hJ : 0 ≤ J) (hκ : 0 ≤ κ) (hγ : 0 ≤ γ) (hηone : (η : ℝ) ≤ 1)
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
    (hwindow : 2 * (η : ℝ) < (η : ℝ) ^ γ)
    (hKinv : 0 ≤ Kinv)
    (hdiameter : ∀ w ρ : ℝ, 0 ≤ ρ → ∀ i j : ι,
      |a i-w| ≤ ρ → |a j-w| ≤ ρ → dist (f i : RMat) (f j : RMat) ≤ 2*Kinv*ρ)
    (hinj : Function.Injective a)
    (hnormalize : (Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal ≤ W*(Fintype.card ι : ℝ)^3) :
    let Z := Finset.univ.image a
    let Bpow := (4 : ℝ)^142
    let Dloc := 40*(2*R)^11*(Kinv+2)
    let E := (4*(20*(2*R)^10*ε + 2*R*(η : ℝ))/(η : ℝ)+1)^4
    let Q := 4*((binCount B δ ^ 4 : ℕ) : ℝ)^3 *
      (E*((8*Bpow+1)^4*(8*Bpow^2+4*Bpow+1)^κ*K*J*
        (η : ℝ)^(-(γ*κ)))*Dloc^κ + (2 : ℝ)^κ)
    ∀ C : ℝ, 0 ≤ C → Q*W ≤ C^3 →
      ∀ w ρ : ℝ, (η : ℝ) ≤ ρ → ε ≤ ρ →
        OAI.Falconer.scalarBallMass Z w ρ ≤ C*ρ^(κ/3)*(Z.card : ℝ) := by
  classical
  intro Z Bpow Dloc E Q C hC hbudget w ρ hηρ hερ
  let N := (Metric.externalCoveringNumber η
    ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal
  have hηR : 0 < (η : ℝ) := hη
  have hρ : 0 < ρ := hηR.trans_le hηρ
  have hR : 1 ≤ R := hB.trans hBR
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hDloc : 0 ≤ Dloc := by dsimp only [Dloc]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q, E, Bpow]; positivity
  have hAfin : Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' A) ≠ ⊤ :=
    finite_coveringNumber_of_entry_bound (by norm_num : (0 : ℝ) ≤ 2) hη
      (by rintro y ⟨x, hx, rfl⟩
          exact mobiusIdentityBall_subset_entryBox_two hα hαone (hA hx))
  have hNlower := coveringNumber_lower_of_distribution hη hwindow hAfin hdistribution
  have hN : 0 < N :=
    (Real.rpow_pos_of_pos (by positivity : 0 < 2 * (η : ℝ)) (-κ)).trans_le hNlower
  have hZcard : Z.card = Fintype.card ι := by
    exact (Finset.card_image_of_injective _ hinj).trans (Finset.card_univ)
  have hglobal : N ≤ W*(Z.card : ℝ)^3 := by
    rw [hZcard]
    exact hnormalize
  let I := {i : ι // |a i - w| ≤ ρ}
  let s := (Kinv + 1) * ρ
  have hs : 0 ≤ s := by dsimp only [s]; positivity
  have hdiam : ∀ i j : I, dist (f i : RMat) (f j : RMat) ≤ 2 * s := by
    intro i j
    have hh := hdiameter w ρ hρ.le i j i.property j.property
    dsimp only [s]
    linarith only [hh, hρ]
  have hρs : ρ ≤ s := by
    dsimp only [s]
    nlinarith only [hKinv, hρ]
  have hfac : 1 ≤ 40 * (2 * R) ^ 11 := by
    have hh := one_le_pow₀ (by linarith only [hR] : 1 ≤ 2 * R) (n := 11)
    linarith only [hh]
  have hout : (η : ℝ) ≤ 40 * (2 * R) ^ 11 * (s + ε) := by
    calc
      _ ≤ s + ε := by linarith only [hηρ, hρs, hε]
      _ ≤ 40 * (2 * R) ^ 11 * (s + ε) :=
        le_mul_of_one_le_left (by positivity) hfac
  have hscaleρ : 40 * (2 * R) ^ 11 * (s + ε) ≤ Dloc * ρ := by
    dsimp only [Dloc, s]
    have hh := mul_le_mul_of_nonneg_left hερ (by positivity : 0 ≤ 40 * (2 * R) ^ 11)
    nlinarith only [hh]
  have hcluster := finite_source_cluster_cubic_bound
    (fun i : I => f i) (fun i : I => X i) (fun i : I => c i) (fun i : I => t i) base
    hA1 hAi hα hαone hA hαsmall hp hq hpq hd₀ hspan hz hr₀ hfar
    hB hM hscale hδ hr hr1 (fun i => hf i) (fun i => hform i) hbranch hradius
    hd hframe hsmall habsorb
    (fun i j hij => hsep i j (fun he => hij (Subtype.ext he)))
    hbase (fun i => hX i) hBR hHR hε hη (fun i => he i) hs hdiam
    hK hJ hκ hγ hηone hout hproduct hsize hdistribution
  let Fcoef := E * ((8 * Bpow + 1) ^ 4 *
    (8 * Bpow ^ 2 + 4 * Bpow + 1) ^ κ * K * J * (η : ℝ) ^ (-(γ * κ)))
  have hFcoef : 0 ≤ Fcoef := by dsimp only [Fcoef, E, Bpow]; positivity
  have hcp : (Fintype.card I : ℝ) ^ 3 ≤
      4 * ((binCount B δ ^ 4 : ℕ) : ℝ) ^ 3 *
        (Fcoef * (40 * (2 * R) ^ 11 * (s + ε)) ^ κ * N + 1) := by
    convert hcluster using 1; dsimp only [Fcoef]; ring
  have hrpow := Real.rpow_le_rpow (by positivity : 0 ≤ 40 * (2 * R) ^ 11 * (s + ε))
    hscaleρ hκ
  rw [Real.mul_rpow hDloc hρ.le] at hrpow
  have hmain := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hrpow hFcoef) hN.le
  have hone := one_le_scaled_cover_of_lower hηR hηρ hκ hNlower
  have hlocal : OAI.Falconer.scalarBallMass Z w ρ ^ 3 ≤ Q * ρ ^ κ * N := by
    rw [scalarBallMass_image a hinj]
    calc
      _ ≤ 4 * ((binCount B δ ^ 4 : ℕ) : ℝ) ^ 3 *
          (Fcoef * (40 * (2 * R) ^ 11 * (s + ε)) ^ κ * N + 1) := hcp
      _ ≤ 4 * ((binCount B δ ^ 4 : ℕ) : ℝ) ^ 3 *
          (Fcoef * (Dloc ^ κ * ρ ^ κ) * N + (2 : ℝ) ^ κ * ρ ^ κ * N) :=
        mul_le_mul_of_nonneg_left (add_le_add hmain hone) (by positivity)
      _ = _ := by dsimp only [Q, Fcoef]; push_cast; ring
  exact normalized_count_of_cubic (Nat.cast_nonneg _) (OAI.Falconer.scalarBallMass_nonneg _ _ _)
    hQ hC hρ.le hlocal hglobal hbudget

end TransposeFollowup.SL2Projection

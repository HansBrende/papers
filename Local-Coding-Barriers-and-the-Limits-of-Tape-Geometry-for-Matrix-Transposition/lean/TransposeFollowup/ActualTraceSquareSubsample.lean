import TransposeFollowup.FarSignSubsample
import TransposeFollowup.ActualCentralizerSourcePacking

/-! An actual retained nonnilpotent scalar sample. The discarded near-identity
indices are controlled by the existing cubic source-cluster theorem; sign
selection, source witnesses, scalar spacing and the loss of a factor four
are proved, not assumed for a hypothetical sample. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius BoundedCoordinatePacking
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem exists_actual_trace_square_subsample {ι : Type*} [Fintype ι]
    (f X : ι → G) (c t : ι → ℝ) (base : G) {A : Set G} {p q z : G}
    {α d₀ r₀ B M r δ d R ε s K J κ γ Lgap δs : ℝ} {η : ℝ≥0}
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
      max (10 * B * M * (384 * M ^ 4 / d * (η : ℝ))) (3072/(Lgap*s)*δs) <
        dist (f x : RMat) (f y : RMat))
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
    (hι : 0 < Fintype.card ι) (hLgap : 0 < Lgap)
    (hgap : Lgap ≤ |((z : RMat) - (Matrix.trace (z : RMat)/2) • (1 : RMat)).det|)
    (hnear : 25*α + ε ≤ 1/64) (hδs : 0 < δs) :
    let Bpow := (4 : ℝ)^142
    let ρ := 40*(2*R)^11*(s+ε)
    let E := (4*(20*(2*R)^10*ε + 2*R*(η : ℝ))/(η : ℝ)+1)^4
    let L := binCount B δ ^ 4
    let U := E*((8*Bpow+1)^4*(8*Bpow^2+4*Bpow+1)^κ*K*J*
      (η : ℝ)^(-(γ*κ))*ρ^κ*
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal)
    32*(L : ℝ)^3*(U+1) ≤ (Fintype.card ι : ℝ)^3 →
    ∃ S : Finset ι, S.Nonempty ∧ Fintype.card ι ≤ 4*S.card ∧
      (∀ i ∈ S, s < dist (f i : RMat) 1) ∧
      (∀ i ∈ S, ∀ j ∈ S, 0 ≤ t i * t j) ∧
      (∀ i, dist (f i : RMat) 1 ≤ 1/64) ∧
      (∀ i ∈ S, ∀ j ∈ S,
        dist (f i : RMat) (f j : RMat) ≤
          3072/(Lgap*s)*|traceSquareScalar (f i)-traceSquareScalar (f j)|) ∧
      let Z := S.image (fun i => traceSquareScalar (f i))
      Z.Nonempty ∧ Z.card = S.card ∧
      (∀ x ∈ Z, 1 ≤ x ∧ x ≤ 2) ∧
      (∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → δs < |x-y|) := by
  classical
  intro Bpow ρ E L U hbudget
  let I := {i : ι // dist (f i : RMat) 1 ≤ s}
  have hdiam : ∀ i j : I, dist (f i : RMat) (f j : RMat) ≤ 2*s := by
    intro i j
    have hh := dist_triangle (f i : RMat) 1 (f j : RMat)
    rw [dist_comm 1] at hh
    linarith only [hh, i.property, j.property]
  have hcluster := finite_source_cluster_cubic_bound
    (fun i : I => f i) (fun i : I => X i) (fun i : I => c i) (fun i : I => t i) base
    hA1 hAi hα hαone hA hαsmall hp hq hpq hd₀ hspan hz hr₀ hfar
    hB hM hscale hδ hr hr1 (fun i => hf i) (fun i => hform i) hbranch hradius
    hd hframe hsmall habsorb
    (fun i j hij => (le_max_left _ _).trans_lt (hsep i j (fun he => hij (Subtype.ext he))))
    hbase (fun i => hX i) hBR hHR hε hη (fun i => he i) hs.le hdiam
    hK hJ hκ hγ hηone houtRadius hproduct hsize hdistribution
  have hcube : (Fintype.card I : ℝ)^3 ≤ 4*(L : ℝ)^3*(U+1) := hcluster
  have hhalfR : 2*(Fintype.card I : ℝ) ≤ (Fintype.card ι : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by positivity) (Nat.cast_nonneg _)
      (by norm_num : (3 : ℕ) ≠ 0)).mp
    calc
      _ = 8*(Fintype.card I : ℝ)^3 := by ring
      _ ≤ 8*(4*(L : ℝ)^3*(U+1)) := mul_le_mul_of_nonneg_left hcube (by norm_num)
      _ ≤ (Fintype.card ι : ℝ)^3 := by nlinarith only [hbudget]
  have hhalf : 2*((Finset.univ : Finset ι).filter
      (fun i => dist (f i : RMat) 1 ≤ s)).card ≤ (Finset.univ : Finset ι).card := by
    have hcard : Fintype.card I = ((Finset.univ : Finset ι).filter
        (fun i => dist (f i : RMat) 1 ≤ s)).card := Fintype.card_subtype _
    rw [hcard] at hhalfR
    simpa only [Finset.card_univ] using (show 2*((Finset.univ : Finset ι).filter
      (fun i => dist (f i : RMat) 1 ≤ s)).card ≤ Fintype.card ι by exact_mod_cast hhalfR)
  obtain ⟨S, _, hSn, hcard, hSfar, hSsign⟩ := exists_far_sign_subsample Finset.univ
    (fun i => (f i : RMat)) t s (Finset.card_pos.mp (by simpa using hι)) hhalf
  have hinv : base⁻¹ ∈ A := by simpa only [hAi] using Set.inv_mem_inv.mpr hbase
  have hsource (i : ι) : base⁻¹*X i ∈ A^2 := by
    simpa only [pow_two] using Set.mul_mem_mul hinv (hX i)
  have hdist (i : ι) : dist (f i : RMat) 1 ≤ 1/64 := by
    have hh := set_pow_dist_from_one_le hα hαone hA 2 (base⁻¹*X i) (hsource i)
    norm_num only [show (5 : ℝ)^2 = 25 by norm_num] at hh
    exact (dist_triangle _ ((base⁻¹*X i : G) : RMat) 1).trans
      ((add_le_add (he i) hh).trans (by linarith only [hnear]))
  let b := (z : RMat) - (Matrix.trace (z : RMat)/2) • (1 : RMat)
  have hb : Matrix.trace b = 0 := (centered_generator_coordinates (z : RMat)).1
  have hcenter (i : ι) : (f i : RMat) =
      scalarAffine b (c i + t i * Matrix.trace (z : RMat)/2) (t i) := by
    rw [hform i, scalarAffine_recenter]
  obtain ⟨hbn, hbd⟩ := centered_near_identity_generator_bounds z hz
  have hInv (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      dist (f i : RMat) (f j : RMat) ≤
        3072/(Lgap*s)*|traceSquareScalar (f i)-traceSquareScalar (f j)| := by
    have hh := traceSquareScalar_inverse_distance b (f i) (f j)
      (by norm_num : (1 : ℝ) ≤ 32) hLgap hs hs1 hb hbn hbd hgap
      (hcenter i) (hcenter j) ((hdist i).trans (by norm_num))
      ((hdist j).trans (by norm_num)) (hSfar i hi).le (hSsign i hi j hj)
    norm_num only [show 3*(32 : ℝ)^2 = 3072 by norm_num] at hh
    exact hh
  have hscalar (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) (hne : i ≠ j) :
      δs < |traceSquareScalar (f i)-traceSquareScalar (f j)| := by
    have hh := ((le_max_right _ _).trans_lt (hsep i j hne)).trans_le (hInv i hi j hj)
    by_contra hn
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hn)
      (show 0 ≤ 3072/(Lgap*s) by positivity)
    exact (not_lt_of_ge hm) hh
  have hInj : Set.InjOn (fun i => traceSquareScalar (f i)) (S : Set ι) := by
    intro i hi j hj heq
    change traceSquareScalar (f i) = traceSquareScalar (f j) at heq
    by_contra hne
    have hh := hscalar i hi j hj hne
    rw [heq, sub_self, abs_zero] at hh
    exact (not_lt_of_ge hδs.le) hh
  refine ⟨S, hSn, by simpa only [Finset.card_univ] using hcard,
    hSfar, hSsign, hdist, hInv, hSn.image _, Finset.card_image_of_injOn hInj, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact traceSquareScalar_near_identity (f i) ((hdist i).trans (by norm_num))
  · intro x hx y hy hne
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact hscalar i hi j hj (fun heq => hne (congrArg (fun k => traceSquareScalar (f k)) heq))

end TransposeFollowup.SL2Projection

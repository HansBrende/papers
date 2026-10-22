import TransposeFollowup.ActualTraceSquareSubsample
import TransposeFollowup.CoarsenedSourceSample

/-! Apply the coarse sampler before trimming. The final scalar sample is
indexed by actual original sources, and retains native covering complexity
with a displayed finite sampling and trimming loss. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius BoundedCoordinatePacking
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem exists_actual_trace_square_source_sample {ι : Type*}
    (f X : ι → G) (c t : ι → ℝ) (base : G) {A : Set G} {p q z : G}
    {α d₀ r₀ B M r δ d R ε s K J κ γ Lgap δs : ℝ} {η σ : ℝ≥0}
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
    (hseparation : 10 * B * M * (384 * M ^ 4 / d * (η : ℝ)) ≤ 2*(σ : ℝ))
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
    (hσ : 0 < σ) (hησ : η ≤ σ) (hLgap : 0 < Lgap)
    (hgap : Lgap ≤ |((z : RMat) - (Matrix.trace (z : RMat)/2) • (1 : RMat)).det|)
    (hnear : 25*α + ε ≤ 1/64) (hδs : 0 < δs)
    (hspacing : 3072/(Lgap*s)*δs ≤ 2*(σ : ℝ)) :
    let Bpow := (4 : ℝ)^142
    let ρ := 40*(2*R)^11*(s+ε)
    let E := (4*(20*(2*R)^10*ε + 2*R*(η : ℝ))/(η : ℝ)+1)^4
    let L := binCount B δ ^ 4
    let U := E*((8*Bpow+1)^4*(8*Bpow^2+4*Bpow+1)^κ*K*J*
      (η : ℝ)^(-(γ*κ))*ρ^κ*
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal)
    let C := 6561*(4*(σ : ℝ)/(η : ℝ)+1)^4
    let V := (Metric.externalCoveringNumber η
      (Set.range (fun i => (f i : RMat))) : ℝ≥0∞).toReal
    32*(L : ℝ)^3*(U+1)*C^3 ≤ V^3 →
    ∃ T : Finset ι, T.Nonempty ∧
      (∀ i ∈ T, s < dist (f i : RMat) 1) ∧
      (∀ i ∈ T, ∀ j ∈ T, 0 ≤ t i * t j) ∧
      (∀ i ∈ T, dist (f i : RMat) 1 ≤ 1/64) ∧
      (∀ i ∈ T, ∀ j ∈ T, i ≠ j → 2*(σ : ℝ) < dist (f i : RMat) (f j : RMat)) ∧
      (∀ i ∈ T, ∀ j ∈ T,
        dist (f i : RMat) (f j : RMat) ≤
          3072/(Lgap*s)*|traceSquareScalar (f i)-traceSquareScalar (f j)|) ∧
      let Z := T.image (fun i => traceSquareScalar (f i))
      Z.Nonempty ∧ Z.card = T.card ∧
      (∀ x ∈ Z, 1 ≤ x ∧ x ≤ 2) ∧
      (∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → δs < |x-y|) ∧
      Metric.externalCoveringNumber η (Set.range (fun i => (f i : RMat))) ≠ ⊤ ∧
      V ≤ 26244*(4*(σ : ℝ)/(η : ℝ)+1)^4*(Z.card : ℝ) ∧
      (Z.card : ℝ) ≤ V := by
  classical
  intro Bpow ρ E L U C V hbudget
  obtain ⟨F, a, hFn, ha, hFsep, hfin, hretain⟩ :=
    exists_coarse_source_sample (fun i => (f i : RMat)) (zero_le_one.trans hB) hη hσ hfn hf
  have hC : 0 < C := by dsimp only [C]; positivity
  have hret : V ≤ C*(F.card : ℝ) := hretain
  have hbud : 32*(L : ℝ)^3*(U+1) ≤ (Fintype.card ↥F : ℝ)^3 := by
    simp only [Fintype.card_coe]
    have hh : 32*(L : ℝ)^3*(U+1)*C^3 ≤ (F.card : ℝ)^3*C^3 := by
      calc
        _ ≤ V^3 := hbudget
        _ ≤ (C*(F.card : ℝ))^3 := pow_le_pow_left₀ ENNReal.toReal_nonneg hret 3
        _ = _ := by ring
    exact (mul_le_mul_iff_left₀ (pow_pos hC 3)).mp hh
  have hsep' (i j : ↥F) (hne : i ≠ j) :
      max (10*B*M*(384*M^4/d*(η : ℝ))) (3072/(Lgap*s)*δs) <
        dist (f (a i) : RMat) (f (a j) : RMat) := by
    rw [ha i, ha j]
    exact (max_le hseparation hspacing).trans_lt (hFsep i i.property j j.property (fun heq => hne (Subtype.ext heq)))
  obtain ⟨S, hSn, hcard, hSfar, hSsign, hdist, hInv, hZn, hZcard, hZrange, hZsep⟩ :=
    exists_actual_trace_square_subsample
      (fun i : ↥F => f (a i)) (fun i : ↥F => X (a i))
      (fun i : ↥F => c (a i)) (fun i : ↥F => t (a i)) base
      hA1 hAi hα hαone hA hαsmall hp hq hpq hd₀ hspan hz hr₀ hfar
      hB hM hscale hδ hr hr1 (fun i => hf (a i)) (fun i => hform (a i)) hbranch hradius
      hd hframe hsmall habsorb hsep' hbase (fun i => hX (a i)) hBR hHR hε hη
      (fun i => he (a i)) hs hs1 hK hJ hκ hγ hηone houtRadius hproduct hsize hdistribution
      (by simpa only [Fintype.card_coe] using hFn.card_pos) hLgap hgap hnear hδs hbud
  have hainj : Function.Injective a := by
    intro x y heq
    apply Subtype.ext
    rw [← ha x, ← ha y, heq]
  let T := S.image a
  have hTcard : T.card = S.card := Finset.card_image_of_injective _ hainj
  have hZeq : T.image (fun i => traceSquareScalar (f i)) =
      S.image (fun i => traceSquareScalar (f (a i))) := by
    simp only [T, Finset.image_image, Function.comp_def]
  refine ⟨T, hSn.image a, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfin, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact hSfar j hj
  · intro i hi j hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hj
    exact hSsign x hx y hy
  · intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact hdist j
  · intro i hi j hj hne
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hj
    rw [ha x, ha y]
    exact hFsep x x.property y y.property
      (fun heq => hne (congrArg a (Subtype.ext heq)))
  · intro i hi j hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hj
    exact hInv x hx y hy
  · rw [hZeq]; exact hZn
  · rw [hZeq, hZcard, hTcard]
  · rw [hZeq]; exact hZrange
  · rw [hZeq]; exact hZsep
  · rw [hZeq, hZcard]
    have hc : (F.card : ℝ) ≤ 4*(S.card : ℝ) := by
      exact_mod_cast (show F.card ≤ 4*S.card by simpa only [Fintype.card_coe] using hcard)
    calc
      V ≤ C*(F.card : ℝ) := hret
      _ ≤ C*(4*(S.card : ℝ)) := mul_le_mul_of_nonneg_left hc hC.le
      _ = _ := by dsimp only [C]; ring
  · rw [hZeq, hZcard]
    have hSc : (S.card : ℝ) ≤ (F.card : ℝ) := by
      exact_mod_cast (show S.card ≤ F.card by simpa only [Fintype.card_coe] using Finset.card_le_univ S)
    apply hSc.trans
    apply separated_matrix_card_le_coveringNumber F
      (by intro x hx; exact ⟨a ⟨x,hx⟩, ha ⟨x,hx⟩⟩) _ hfin
    intro x hx y hy hne
    exact (mul_le_mul_of_nonneg_left (show (η : ℝ) ≤ σ from hησ)
      (by norm_num : (0 : ℝ) ≤ 2)).trans_lt (hFsep x hx y hy hne)

/-- Products and quotients of the retained near-identity family remain
near the identity. Quotients may equal the identity. -/
theorem sl2_enlargement_near_identity (F : Finset G)
    (hnear : ∀ u ∈ F, dist (u : RMat) 1 ≤ 1/64) :
    ∀ w ∈ F ∪ F*F ∪ F*F⁻¹, dist (w : RMat) 1 ≤ 1/16 := by
  have hprod (u v : G) (hu : dist (u : RMat) 1 ≤ 1/64)
      (hv : dist (v : RMat) 1 ≤ 1/64) :
      dist ((u*v : G) : RMat) 1 ≤ 1/16 := by
    have hn := frobenius_norm_of_near_one (v : RMat) (hv.trans (by norm_num))
    have ht := dist_triangle ((u*v : G) : RMat) (v : RMat) 1
    have he : dist ((u*v : G) : RMat) (v : RMat) ≤ dist (u : RMat) 1 * ‖(v : RMat)‖ := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul, one_mul] using
        frobenius_dist_right_mul (u : RMat) 1 (v : RMat)
    have hm := mul_le_mul hu hn (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/64)
    linarith only [ht, he, hm, hv]
  intro w hw
  rcases Finset.mem_union.mp hw with hw | hw
  · rcases Finset.mem_union.mp hw with hw | hw
    · exact (hnear w hw).trans (by norm_num)
    · obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp hw
      exact hprod u v (hnear u hu) (hnear v hv)
  · obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp hw
    apply hprod u v (hnear u hu)
    obtain ⟨w, hwF, hvw⟩ := Finset.mem_inv.mp hv
    rw [← hvw, sl2_inverse_distance_one]
    exact hnear w hwF

/-- The actual two-factor enlargement stays in the scalar interval used
by sum-product. Quotients may equal the identity. -/
theorem traceSquareScalar_enlargement_range (F : Finset G)
    (hnear : ∀ u ∈ F, dist (u : RMat) 1 ≤ 1/64) :
    ∀ x ∈ (F ∪ F*F ∪ F*F⁻¹).image traceSquareScalar, 1 ≤ x ∧ x ≤ 2 := by
  intro x hx
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
  exact traceSquareScalar_near_identity w (sl2_enlargement_near_identity F hnear w hw)

end TransposeFollowup.SL2Projection

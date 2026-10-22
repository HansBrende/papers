import TransposeFollowup.ActualCentralizerSourcePacking
import TransposeFollowup.CoarsenedSourceSample

/-! Compose source sampling, localization, integer rounding and actual-word
packing into a bound on the entire commuting family. The additive one
retains the small-cardinality case. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius BoundedCoordinatePacking
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem commuting_family_cubic_bound {ι : Type*}
    (f X : ι → G) (c t : ι → ℝ) (base : G) {A : Set G} {p q z : G}
    {α d₀ r₀ B M r δ d R ε : ℝ} {η σ : ℝ≥0}
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
    (hbase : base ∈ A) (hX : ∀ i, X i ∈ A) (hBR : B ≤ R)
    (hHR : (4 : ℝ) ^ 68 ≤ R) (hε : 0 ≤ ε) (hη : 0 < η) (hσ : 0 < σ)
    (he : ∀ i, dist (f i : RMat) ((base⁻¹ * X i : G) : RMat) ≤ ε)
    (hfn : (Set.range (fun i => (f i : RMat))).Nonempty)
    (hspacing : 10 * B * M * (384 * M ^ 4 / d * (η : ℝ)) ≤ 2 * (σ : ℝ)) :
    let V := Set.range (fun i => (f i : RMat))
    let T := (fun g : G => (g : RMat)) '' (A ^ 142)
    let C := 6561 * (4 * (σ : ℝ) / (η : ℝ) + 1) ^ 4
    let L := binCount B δ ^ 4
    let E := (4 * (20 * (2 * R) ^ 10 * ε + 2 * R * (η : ℝ)) / (η : ℝ) + 1) ^ 4
    Metric.externalCoveringNumber η V ≠ ⊤ ∧ Metric.externalCoveringNumber η T ≠ ⊤ ∧
      (Metric.externalCoveringNumber η V : ℝ≥0∞).toReal ^ 3 ≤
        4 * (C * (L : ℝ)) ^ 3 *
          (E * (Metric.externalCoveringNumber η T : ℝ≥0∞).toReal + 1) := by
  let V := Set.range (fun i => (f i : RMat))
  let T := (fun g : G => (g : RMat)) '' (A ^ 142)
  let C := 6561 * (4 * (σ : ℝ) / (η : ℝ) + 1) ^ 4
  let L := binCount B δ ^ 4
  let E := (4 * (20 * (2 * R) ^ 10 * ε + 2 * R * (η : ℝ)) / (η : ℝ) + 1) ^ 4
  let U := E * (Metric.externalCoveringNumber η T : ℝ≥0∞).toReal
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hU : 0 ≤ U := by dsimp only [U, E]; positivity
  have hL : 0 < L := pow_pos (binCount_pos B δ) 4
  obtain ⟨F, s, _hFn, hs, hsep, hVfin, hsize⟩ :=
    exists_coarse_source_sample (fun i => (f i : RMat)) (by linarith) hη hσ hfn hf
  have hAb : A ⊆ matrixEntryBox 2 :=
    hA.trans (mobiusIdentityBall_subset_entryBox_two hα hαone)
  have hTfin : Metric.externalCoveringNumber η T ≠ ⊤ :=
    finite_coveringNumber_of_entry_bound (by positivity : 0 ≤ (4 : ℝ) ^ 142) hη (by
      rintro g ⟨x, hx, rfl⟩ i j
      simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
        set_pow_subset_matrixEntryBox hAb 142 hx i j)
  let m := F.card / L
  have hmcard : L * m ≤ Fintype.card ↥F := by
    simpa only [Fintype.card_coe] using Nat.mul_div_le F.card L
  have hmpow : (m : ℝ) ^ 3 ≤ U := by
    by_cases hm : m = 0
    · simpa only [hm, Nat.cast_zero, zero_pow (by norm_num : 3 ≠ 0)] using hU
    · have hms : 0 < m := Nat.pos_of_ne_zero hm
      have hsep' (x y : ↥F) (hxy : x ≠ y) :
          10 * B * M * (384 * M ^ 4 / d * (η : ℝ)) <
            dist (f (s x) : RMat) (f (s y) : RMat) := by
        rw [hs x, hs y]
        exact hspacing.trans_lt (hsep x x.property y y.property
          (fun heq => hxy (Subtype.ext heq)))
      exact (actual_localized_source_packing (fun x : ↥F => f (s x))
        (fun x => X (s x)) (fun x => c (s x)) (fun x => t (s x)) base
        hA1 hAi hα hαone hA hαsmall hp hq hpq hd₀ hspan hz hr₀ hfar
        hB hM hscale hδ hr hr1 hms (fun x => hf (s x)) (fun x => hform (s x))
        hbranch hradius hmcard hd hframe hsmall habsorb hsep'
        hbase (fun x => hX (s x)) hBR hHR hε hη (fun x => he (s x))).2
  have hcardCube := nat_cubic_bound_of_quotient F.card L hL hmpow
  refine ⟨hVfin, hTfin, ?_⟩
  calc
    _ ≤ (C * (F.card : ℝ)) ^ 3 := pow_le_pow_left₀ ENNReal.toReal_nonneg hsize 3
    _ = C ^ 3 * (F.card : ℝ) ^ 3 := mul_pow _ _ _
    _ ≤ C ^ 3 * (4 * (L : ℝ) ^ 3 * (U + 1)) :=
      mul_le_mul_of_nonneg_left hcardCube (by positivity)
    _ = _ := by ring

end TransposeFollowup.SL2Projection

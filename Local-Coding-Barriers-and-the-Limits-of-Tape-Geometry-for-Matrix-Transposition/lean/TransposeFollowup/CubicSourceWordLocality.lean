import TransposeFollowup.CubicSourceWordTransfer

/-! The actual cubic words retain the radius of their input cluster.
The existing normalized-product error estimate supplies the radius bound;
the existing cover transfer keeps this restricted output set. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem shared_center_cubic_word_near (a : Fin 3 → G) (a₀ u v : G) {R ρ : ℝ}
    (hR : 1 ≤ R) (hρ : 0 ≤ ρ)
    (ha₀ : ∀ i j, |a₀ i j| ≤ R) (ha : ∀ k i j, |a k i j| ≤ R)
    (hu : ∀ i j, |u i j| ≤ R) (hv : ∀ i j, |v i j| ≤ R)
    (hclose : ∀ k, dist (a₀ : RMat) (a k : RMat) ≤ ρ) :
    dist (((a₀⁻¹ * a 0) * u * (a₀⁻¹ * a 1) * (u⁻¹ * v) *
      (a₀⁻¹ * a 2) : G) : RMat) (v : RMat) ≤ 20 * (2 * R) ^ 11 * ρ := by
  let q : G := (a₀⁻¹ * a 0) * u * (a₀⁻¹ * a 1) * (u⁻¹ * v) * (a₀⁻¹ * a 2)
  have he := normalized_cubic_product_dist_error (fun _ => a₀) a a₀ a₀ u v hR hρ
    ha₀ ha₀ (fun _ => ha₀) ha hu hv (by simpa using hρ) hclose
  have heq : (a₀⁻¹ * a 0) * (u * (a₀⁻¹ * a 1) * u⁻¹) *
      (v * (a₀⁻¹ * a 2) * v⁻¹) = q * v⁻¹ := by
    dsimp only [q]
    group
  simp only [inv_mul_cancel, mul_one, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, heq] at he
  have hd : dist ((q * v⁻¹ : G) : RMat) 1 ≤ 20 * (2 * R) ^ 10 * ρ := by
    simpa only [dist_comm] using he
  have hn := frobenius_norm_le_of_entry_bound (by linarith : 0 ≤ R) hv
  have hm := frobenius_dist_right_mul ((q * v⁻¹ : G) : RMat) (1 : RMat) (v : RMat)
  have hcancel : ((q * v⁻¹ : G) : RMat) * (v : RMat) = (q : RMat) := by
    exact congrArg (fun z : G => (z : RMat)) (by group : q * v⁻¹ * v = q)
  rw [hcancel, one_mul] at hm
  apply hm.trans
  calc
    _ ≤ (20 * (2 * R) ^ 10 * ρ) * (2 * R) :=
      mul_le_mul hd hn (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem cubic_source_word_covering_transfer_near {ι κ : Type*}
    (f x : ι → G) (base : G) (i₀ : ι) (s : κ → ι) (u v : G)
    {A : Set G} {R ε r : ℝ} {η : ℝ≥0}
    (hAi : A⁻¹ = A) (hA : A ⊆ matrixEntryBox 2) (hx : ∀ i, x i ∈ A)
    (huA : u ∈ A ^ 34) (hvA : v ∈ A ^ 68)
    (hR : 1 ≤ R) (hε : 0 ≤ ε) (hr : 0 ≤ r) (hη : 0 < η)
    (hf : ∀ i j k, |f i j k| ≤ R)
    (ha : ∀ i j k, |(base⁻¹ * x i : G) j k| ≤ R)
    (hu : ∀ i j, |u i j| ≤ R) (hv : ∀ i j, |v i j| ≤ R)
    (he : ∀ i, dist (f i : RMat) ((base⁻¹ * x i : G) : RMat) ≤ ε)
    (hdiam : ∀ i j, dist (f i : RMat) (f j : RMat) ≤ 2 * r) :
    let w := fun i => (f i₀)⁻¹ * f (s i)
    let P := Set.range (fun i : Fin 3 → κ =>
      ((w (i 0) * (u * w (i 1) * u⁻¹) * (v * w (i 2) * v⁻¹) : G) : RMat))
    let T := (fun z : G => (z : RMat)) ''
      {z : G | z ∈ A ^ 142 ∧ dist (z : RMat) (v : RMat) ≤ 40 * (2 * R) ^ 11 * (r + ε)}
    Metric.externalCoveringNumber η P ≠ ⊤ ∧ Metric.externalCoveringNumber η T ≠ ⊤ ∧
      (Metric.externalCoveringNumber η P : ℝ≥0∞).toReal ≤
        (4 * (20 * (2 * R) ^ 10 * ε + 2 * R * (η : ℝ)) / (η : ℝ) + 1) ^ 4 *
          (Metric.externalCoveringNumber η T : ℝ≥0∞).toReal := by
  apply cubic_source_word_covering_transfer_to_set f x base i₀ s u v
    hAi hA hx huA hvA hR hε hη hf ha hu hv he (fun _ hz => hz.1)
  intro i
  refine ⟨shared_center_cubic_word_mem_pow (fun k => x (s (i k))) (x i₀) u v
    hAi (hx i₀) (fun k => hx (s (i k))) huA hvA, ?_⟩
  have hclose (k : Fin 3) :
      dist ((base⁻¹ * x i₀ : G) : RMat) ((base⁻¹ * x (s (i k)) : G) : RMat) ≤
        2 * (r + ε) := by
    have ht := dist_triangle4 ((base⁻¹ * x i₀ : G) : RMat) (f i₀ : RMat)
      (f (s (i k)) : RMat) ((base⁻¹ * x (s (i k)) : G) : RMat)
    rw [dist_comm ((base⁻¹ * x i₀ : G) : RMat) (f i₀ : RMat)] at ht
    linarith [he i₀, he (s (i k)), hdiam i₀ (s (i k))]
  have hc (j : ι) : (base⁻¹ * x i₀)⁻¹ * (base⁻¹ * x j) = (x i₀)⁻¹ * x j := by
    group
  have hh := shared_center_cubic_word_near (fun k => base⁻¹ * x (s (i k)))
    (base⁻¹ * x i₀) u v hR (by positivity : 0 ≤ 2 * (r + ε))
    (ha i₀) (fun k => ha (s (i k))) hu hv hclose
  simp only [hc] at hh
  convert hh using 1; ring

end TransposeFollowup.SL2Projection

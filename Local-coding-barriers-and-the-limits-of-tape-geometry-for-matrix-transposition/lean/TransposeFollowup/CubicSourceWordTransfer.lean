import TransposeFollowup.NormalizedCubicProductError
import TransposeFollowup.SL2TranslatedCluster

/-! Transfer the exact normalized product to actual words. Retaining the
shared source center keeps each normalized source in A^2 and the resulting
unnormalized cubic word in A^142. The cover distortion is explicit. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem shared_center_cubic_word_mem_pow (x : Fin 3 → G) (x₀ u v : G)
    {A : Set G} {j k : ℕ} (hAi : A⁻¹ = A)
    (hx₀ : x₀ ∈ A) (hx : ∀ i, x i ∈ A) (hu : u ∈ A ^ j) (hv : v ∈ A ^ k) :
    (x₀⁻¹ * x 0) * u * (x₀⁻¹ * x 1) * (u⁻¹ * v) * (x₀⁻¹ * x 2) ∈
      A ^ (6 + 2 * j + k) := by
  have hxi : x₀⁻¹ ∈ A := hAi ▸ Set.inv_mem_inv.mpr hx₀
  have hw (i : Fin 3) : x₀⁻¹ * x i ∈ A ^ 2 := by
    rw [pow_two]
    exact Set.mul_mem_mul hxi (hx i)
  have hui : u⁻¹ ∈ A ^ j := by
    have hh := Set.inv_mem_inv.mpr hu
    rwa [← inv_pow, hAi] at hh
  have hm {a b : G} {s t : ℕ} (ha : a ∈ A ^ s) (hb : b ∈ A ^ t) :
      a * b ∈ A ^ (s + t) := by
    rw [pow_add]
    exact Set.mul_mem_mul ha hb
  have hh := hm (hm (hm (hm (hw 0) hu) (hw 1)) (hm hui hv)) (hw 2)
  simpa only [show 2 + j + 2 + (j + k) + 2 = 6 + 2 * j + k by omega] using hh

theorem cubic_source_word_covering_transfer_to_set {ι κ : Type*}
    (f x : ι → G) (base : G) (i₀ : ι) (s : κ → ι) (u v : G)
    {A D : Set G} {R ε : ℝ} {η : ℝ≥0}
    (hAi : A⁻¹ = A) (hA : A ⊆ matrixEntryBox 2) (hx : ∀ i, x i ∈ A)
    (huA : u ∈ A ^ 34) (hvA : v ∈ A ^ 68)
    (hR : 1 ≤ R) (hε : 0 ≤ ε) (hη : 0 < η)
    (hf : ∀ i j k, |f i j k| ≤ R)
    (ha : ∀ i j k, |(base⁻¹ * x i : G) j k| ≤ R)
    (hu : ∀ i j, |u i j| ≤ R) (hv : ∀ i j, |v i j| ≤ R)
    (he : ∀ i, dist (f i : RMat) ((base⁻¹ * x i : G) : RMat) ≤ ε)
    (hD : D ⊆ A ^ 142)
    (hword : ∀ i : Fin 3 → κ,
      ((x i₀)⁻¹ * x (s (i 0))) * u * ((x i₀)⁻¹ * x (s (i 1))) *
        (u⁻¹ * v) * ((x i₀)⁻¹ * x (s (i 2))) ∈ D) :
    let w := fun i => (f i₀)⁻¹ * f (s i)
    let P := Set.range (fun i : Fin 3 → κ =>
      ((w (i 0) * (u * w (i 1) * u⁻¹) * (v * w (i 2) * v⁻¹) : G) : RMat))
    let T := (fun z : G => (z : RMat)) '' D
    Metric.externalCoveringNumber η P ≠ ⊤ ∧ Metric.externalCoveringNumber η T ≠ ⊤ ∧
      (Metric.externalCoveringNumber η P : ℝ≥0∞).toReal ≤
        (4 * (20 * (2 * R) ^ 10 * ε + 2 * R * (η : ℝ)) / (η : ℝ) + 1) ^ 4 *
          (Metric.externalCoveringNumber η T : ℝ≥0∞).toReal := by
  let a : ι → G := fun i => base⁻¹ * x i
  let w : κ → G := fun i => (f i₀)⁻¹ * f (s i)
  let W : κ → G := fun i => (x i₀)⁻¹ * x (s i)
  let p : (Fin 3 → κ) → RMat := fun i =>
    ((w (i 0) * (u * w (i 1) * u⁻¹) * (v * w (i 2) * v⁻¹) : G) : RMat)
  let q : (Fin 3 → κ) → G := fun i =>
    W (i 0) * u * W (i 1) * (u⁻¹ * v) * W (i 2)
  let L : RMat → RMat := fun c => c * ((v⁻¹ : G) : RMat)
  have hcancel (i : ι) : (a i₀)⁻¹ * a i = (x i₀)⁻¹ * x i := by
    dsimp only [a]
    group
  have hqA (i : Fin 3 → κ) : q i ∈ A ^ 142 := by
    exact shared_center_cubic_word_mem_pow (fun k => x (s (i k))) (x i₀) u v
      hAi (hx i₀) (fun k => hx (s (i k))) huA hvA
  have hqb : ∀ i j k, |q i j k| ≤ (4 : ℝ) ^ 142 := by
    intro i j k
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
      set_pow_subset_matrixEntryBox hA 142 (hqA i) j k
  have herror (i : Fin 3 → κ) :
      dist (p i) (L (q i : RMat)) ≤ 20 * (2 * R) ^ 10 * ε := by
    have hh := normalized_cubic_product_dist_error (fun k => f (s (i k)))
      (fun k => a (s (i k))) (f i₀) (a i₀) u v hR hε (hf i₀) (ha i₀)
      (fun k => hf (s (i k))) (fun k => ha (s (i k))) hu hv
      (he i₀) (fun k => he (s (i k)))
    have hq : q i * v⁻¹ =
        W (i 0) * (u * W (i 1) * u⁻¹) * (v * W (i 2) * v⁻¹) := by
      dsimp only [q]
      group
    change dist (p i) ((q i * v⁻¹ : G) : RMat) ≤ _
    rw [hq]
    simpa only [hcancel] using hh
  have hvn := frobenius_norm_le_of_entry_bound (by linarith : 0 ≤ R)
    (matrixEntryBox_inv hv)
  have htrans : ∀ i c, dist (p i) (L c) ≤
      20 * (2 * R) ^ 10 * ε + (2 * R) * dist (q i : RMat) c := by
    intro i c
    calc
      _ ≤ dist (p i) (L (q i : RMat)) + dist (L (q i : RMat)) (L c) := dist_triangle _ _ _
      _ ≤ 20 * (2 * R) ^ 10 * ε + (2 * R) * dist (q i : RMat) c := by
        apply add_le_add (herror i)
        exact (frobenius_dist_right_mul _ _ _).trans
          (by simpa only [mul_comm] using
            mul_le_mul_of_nonneg_left hvn (dist_nonneg : 0 ≤ dist (q i : RMat) c))
  obtain ⟨hpfin, _hqfin, hbound⟩ := coveringNumber_le_bounded_transport p
    (fun i => (q i : RMat)) L (by positivity : 0 ≤ (4 : ℝ) ^ 142)
      (by positivity : 0 ≤ 20 * (2 * R) ^ 10 * ε)
      (by positivity : 0 ≤ 2 * R) hη hqb htrans
  let T := (fun z : G => (z : RMat)) '' D
  have hTfin : Metric.externalCoveringNumber η T ≠ ⊤ :=
    finite_coveringNumber_of_entry_bound (by positivity : 0 ≤ (4 : ℝ) ^ 142) hη (by
      rintro z ⟨g, hg, rfl⟩ j k
      simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
        set_pow_subset_matrixEntryBox hA 142 (hD hg) j k)
  have hsub : Set.range (fun i => (q i : RMat)) ⊆ T := by
    rintro z ⟨i, rfl⟩
    exact ⟨q i, hword i, rfl⟩
  have hmono := ENNReal.toReal_mono (ENat.toENNReal_ne_top.mpr hTfin)
    (ENat.toENNReal_mono (Metric.externalCoveringNumber_mono_set (ε := η) hsub))
  refine ⟨hpfin, hTfin, hbound.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

theorem cubic_source_word_covering_transfer {ι κ : Type*}
    (f x : ι → G) (base : G) (i₀ : ι) (s : κ → ι) (u v : G)
    {A : Set G} {R ε : ℝ} {η : ℝ≥0}
    (hAi : A⁻¹ = A) (hA : A ⊆ matrixEntryBox 2) (hx : ∀ i, x i ∈ A)
    (huA : u ∈ A ^ 34) (hvA : v ∈ A ^ 68)
    (hR : 1 ≤ R) (hε : 0 ≤ ε) (hη : 0 < η)
    (hf : ∀ i j k, |f i j k| ≤ R)
    (ha : ∀ i j k, |(base⁻¹ * x i : G) j k| ≤ R)
    (hu : ∀ i j, |u i j| ≤ R) (hv : ∀ i j, |v i j| ≤ R)
    (he : ∀ i, dist (f i : RMat) ((base⁻¹ * x i : G) : RMat) ≤ ε) :
    let w := fun i => (f i₀)⁻¹ * f (s i)
    let P := Set.range (fun i : Fin 3 → κ =>
      ((w (i 0) * (u * w (i 1) * u⁻¹) * (v * w (i 2) * v⁻¹) : G) : RMat))
    let T := (fun z : G => (z : RMat)) '' (A ^ 142)
    Metric.externalCoveringNumber η P ≠ ⊤ ∧ Metric.externalCoveringNumber η T ≠ ⊤ ∧
      (Metric.externalCoveringNumber η P : ℝ≥0∞).toReal ≤
        (4 * (20 * (2 * R) ^ 10 * ε + 2 * R * (η : ℝ)) / (η : ℝ) + 1) ^ 4 *
          (Metric.externalCoveringNumber η T : ℝ≥0∞).toReal := by
  apply cubic_source_word_covering_transfer_to_set f x base i₀ s u v
    hAi hA hx huA hvA hR hε hη hf ha hu hv he subset_rfl
  intro i
  exact shared_center_cubic_word_mem_pow (fun k => x (s (i k))) (x i₀) u v
    hAi (hx i₀) (fun k => hx (s (i k))) huA hvA

end TransposeFollowup.SL2Projection

import TransposeFollowup.FrobeniusCoverTransfer

/-! Covering complexity retained by exact commuting approximants to a
normalized actual conjugacy fiber. No injectivity premise is used. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Matrix.Norms.Frobenius Pointwise ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem frobenius_dist_left_mul (u a b : RMat) :
    dist (u * a) (u * b) ≤ ‖u‖ * dist a b := by
  rw [dist_eq_norm, ← mul_sub, dist_eq_norm]
  exact norm_mul_le _ _

theorem coveringNumber_le_normalized_approximation (x₀ : G) {A : Set G} (f : A → G)
    {B R : ℝ} {η : ℝ≥0} (hB : 1 ≤ B) (hR : 0 ≤ R) (hη : 0 < η)
    (hx₀ : ∀ i j, |x₀ i j| ≤ B) (hA : ∀ x ∈ A, ∀ i j, |x i j| ≤ B)
    (he : ∀ x : A, dist ((x₀⁻¹ * x : G) : RMat) (f x : RMat) ≤ R) :
    Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) ≠ ⊤ ∧
      Metric.externalCoveringNumber η (Set.range (fun x : A => (f x : RMat))) ≠ ⊤ ∧
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal ≤
        (8 * B * (R + (η : ℝ)) / (η : ℝ) + 1) ^ 4 *
          (Metric.externalCoveringNumber η (Set.range (fun x : A => (f x : RMat))) : ℝ≥0∞).toReal := by
  let a (x : A) : RMat := ((x : G) : RMat)
  let b (x : A) : RMat := (f x : RMat)
  let L (c : RMat) := (x₀ : RMat) * c
  have hB0 : 0 ≤ B := by linarith
  have hyn (x : A) (i j : Fin 2) : |(x₀⁻¹ * x : G) i j| ≤ 2 * B ^ 2 := by
    simpa only [pow_two, mul_assoc] using matrixEntryBox_mul
      (matrixEntryBox_inv hx₀) (hA x x.2) i j
  have hb : ∀ x i j, |b x i j| ≤ 2 * B ^ 2 + R := by
    intro x i j
    have hd := (entry_error_le_frobenius_dist ((x₀⁻¹ * x : G) : RMat) (f x : RMat) i j).trans (he x)
    have hh := abs_add_le (f x i j - (x₀⁻¹ * x : G) i j) ((x₀⁻¹ * x : G) i j)
    rw [sub_add_cancel] at hh
    have hd' : |f x i j - (x₀⁻¹ * x : G) i j| ≤ R := by rw [abs_sub_comm]; exact hd
    dsimp only [b]
    linarith [hyn x i j]
  have hxn := frobenius_norm_le_of_entry_bound hB0 hx₀
  have htrans : ∀ x c, dist (a x) (L c) ≤ 2 * B * R + (2 * B) * dist (b x) c := by
    intro x c
    have hxy : a x = (x₀ : RMat) * ((x₀⁻¹ * x : G) : RMat) := by
      have hh : x₀ * (x₀⁻¹ * (x : G)) = x := by group
      exact (congrArg (fun h : G => (h : RMat)) hh).symm
    rw [hxy]
    change dist ((x₀ : RMat) * ((x₀⁻¹ * x : G) : RMat)) ((x₀ : RMat) * c) ≤ _
    calc
      _ ≤ ‖(x₀ : RMat)‖ * dist ((x₀⁻¹ * x : G) : RMat) c := frobenius_dist_left_mul _ _ _
      _ ≤ (2 * B) * (R + dist (b x) c) := mul_le_mul hxn
        ((dist_triangle _ (f x : RMat) _).trans (add_le_add (he x) le_rfl))
        dist_nonneg (by positivity)
      _ = _ := by ring
  obtain ⟨hafin, hbfin, hbound⟩ := coveringNumber_le_bounded_transport a b L
    (by positivity : 0 ≤ 2 * B ^ 2 + R) (by positivity : 0 ≤ 2 * B * R)
    (by positivity : 0 ≤ 2 * B) hη hb htrans
  have ha : Set.range a = (fun x : G => (x : RMat)) '' A :=
    (Set.image_eq_range _ _).symm
  rw [ha] at hafin hbound
  refine ⟨hafin, hbfin, ?_⟩
  convert hbound using 1
  congr 2
  ring

theorem exists_conjugacy_fiber_commuting_cover (g x₀ : G) {A : Set G} {α r B δ : ℝ}
    {η : ℝ≥0} (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hg : g ∈ mobiusIdentityBall α)
    (hr : 0 < r) (hfar : r ≤ dist (g : RMat) 1)
    (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hη : 0 < η) (hsmall : 768 * B ^ 4 * δ ≤ r)
    (hx₀ : x₀ ∈ A) (hA : ∀ x ∈ A, ∀ i j, |x i j| ≤ B)
    (hclose : ∀ x ∈ A,
      dist ((x * g * x⁻¹ : G) : RMat) ((x₀ * g * x₀⁻¹ : G) : RMat) ≤ δ) :
    ∃ f : A → G,
      (∀ x : A, ∃ s t : ℝ, (f x : RMat) = scalarAffine (g : RMat) s t) ∧
      (∀ x : A, x₀⁻¹ * x ∈ A⁻¹ * A ∧
        dist ((x₀⁻¹ * x : G) : RMat) (f x : RMat) ≤ 6400 * B ^ 6 * δ / r) ∧
      (∀ x y : A, Commute (f x) (f y)) ∧
      Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) ≠ ⊤ ∧
      Metric.externalCoveringNumber η (Set.range (fun x : A => (f x : RMat))) ≠ ⊤ ∧
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal ≤
        (8 * B * (6400 * B ^ 6 * δ / r + (η : ℝ)) / (η : ℝ) + 1) ^ 4 *
          (Metric.externalCoveringNumber η (Set.range (fun x : A => (f x : RMat))) : ℝ≥0∞).toReal := by
  obtain ⟨f, hform, hclose', hpair⟩ := exists_conjugacy_fiber_commuting_approximants g x₀
    hα hαhalf hg hr hfar hB hδ hsmall hx₀ hA hclose
  obtain ⟨hAfin, hVfin, hcover⟩ := coveringNumber_le_normalized_approximation x₀ f hB
    (by positivity : 0 ≤ 6400 * B ^ 6 * δ / r) hη (hA x₀ hx₀) hA (fun x => (hclose' x).2)
  exact ⟨f, hform, hclose', hpair, hAfin, hVfin, hcover⟩

end TransposeFollowup.SL2Projection

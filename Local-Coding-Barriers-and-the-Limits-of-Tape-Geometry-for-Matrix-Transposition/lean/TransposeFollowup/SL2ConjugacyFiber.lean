import TransposeFollowup.SL2CommutingApproximation

/-! Normalize an actual conjugacy fiber inside A^-1*A and derive its
commutator bounds in the ambient Frobenius metric. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Matrix.Norms.Frobenius Pointwise
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem entry_error_le_frobenius_dist (a b : RMat) (i j : Fin 2) :
    |a i j - b i j| ≤ dist a b := by
  have hj : (a i j - b i j) ^ 2 ≤ ∑ j : Fin 2, (a i j - b i j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (a i j - b i j)) (Finset.mem_univ j)
  have hi : (∑ j : Fin 2, (a i j - b i j) ^ 2) ≤
      ∑ i : Fin 2, ∑ j : Fin 2, (a i j - b i j) ^ 2 :=
    Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (a i j - b i j))) (Finset.mem_univ i)
  apply (sq_le_sq₀ (abs_nonneg _) dist_nonneg).mp
  simpa only [sq_abs, frobenius_dist_sq] using hj.trans hi

theorem frobenius_norm_le_of_entry_bound {a : RMat} {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ i j, |a i j| ≤ B) : ‖a‖ ≤ 2 * B := by
  simpa only [dist_zero_right, Matrix.zero_apply, sub_zero] using
    frobenius_dist_le_of_entry_error (x := a) (y := 0) hB (by simpa only [Matrix.zero_apply, sub_zero] using ha)

theorem normalized_conjugacy_commutator (g x₀ x : G) :
    ((x₀⁻¹ * x : G) : RMat) * (g : RMat) - (g : RMat) * ((x₀⁻¹ * x : G) : RMat) =
      ((x₀⁻¹ : G) : RMat) *
        (((x * g * x⁻¹ : G) : RMat) - ((x₀ * g * x₀⁻¹ : G) : RMat)) * (x : RMat) := by
  have h₁ : x₀⁻¹ * (x * g * x⁻¹) * x = (x₀⁻¹ * x) * g := by group
  have h₂ : x₀⁻¹ * (x₀ * g * x₀⁻¹) * x = g * (x₀⁻¹ * x) := by group
  rw [mul_sub, sub_mul]
  exact congrArg₂ (fun a b : RMat => a - b)
    (congrArg (fun h : G => (h : RMat)) h₁).symm
    (congrArg (fun h : G => (h : RMat)) h₂).symm

theorem conjugacy_fiber_commutator_bound (g x₀ x : G) {B δ : ℝ}
    (hB : 0 ≤ B) (hx₀ : ∀ i j, |x₀ i j| ≤ B) (hx : ∀ i j, |x i j| ≤ B)
    (hclose : dist ((x * g * x⁻¹ : G) : RMat) ((x₀ * g * x₀⁻¹ : G) : RMat) ≤ δ) :
    ∀ i j, |(((x₀⁻¹ * x : G) : RMat) * (g : RMat) -
      (g : RMat) * ((x₀⁻¹ * x : G) : RMat)) i j| ≤ 4 * B ^ 2 * δ := by
  let E : RMat := ((x * g * x⁻¹ : G) : RMat) - ((x₀ * g * x₀⁻¹ : G) : RMat)
  have hE : ‖E‖ ≤ δ := by simpa only [dist_eq_norm] using hclose
  have hδ : 0 ≤ δ := (norm_nonneg E).trans hE
  have hx₀i := frobenius_norm_le_of_entry_bound hB (matrixEntryBox_inv hx₀)
  have hxn := frobenius_norm_le_of_entry_bound hB hx
  have hn : ‖((x₀⁻¹ : G) : RMat) * E * (x : RMat)‖ ≤ 4 * B ^ 2 * δ := by
    calc
      _ ≤ (‖((x₀⁻¹ : G) : RMat)‖ * ‖E‖) * ‖(x : RMat)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ((2 * B) * δ) * (2 * B) :=
        mul_le_mul (mul_le_mul hx₀i hE (norm_nonneg _) (by positivity)) hxn
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  intro i j
  rw [normalized_conjugacy_commutator]
  have hh := entry_error_le_frobenius_dist (((x₀⁻¹ : G) : RMat) * E * (x : RMat)) 0 i j
  have he : |(((x₀⁻¹ : G) : RMat) * E * (x : RMat)) i j| ≤
      ‖((x₀⁻¹ : G) : RMat) * E * (x : RMat)‖ := by
    simpa only [Matrix.zero_apply, sub_zero, dist_zero_right] using hh
  exact he.trans hn

theorem exists_conjugacy_fiber_commuting_approximants (g x₀ : G) {A : Set G} {α r B δ : ℝ}
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hg : g ∈ mobiusIdentityBall α)
    (hr : 0 < r) (hfar : r ≤ dist (g : RMat) 1)
    (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hsmall : 768 * B ^ 4 * δ ≤ r)
    (hx₀ : x₀ ∈ A) (hA : ∀ x ∈ A, ∀ i j, |x i j| ≤ B)
    (hclose : ∀ x ∈ A,
      dist ((x * g * x⁻¹ : G) : RMat) ((x₀ * g * x₀⁻¹ : G) : RMat) ≤ δ) :
    ∃ f : A → G,
      (∀ x : A, ∃ s t : ℝ, (f x : RMat) = scalarAffine (g : RMat) s t) ∧
      (∀ x : A, x₀⁻¹ * x ∈ A⁻¹ * A ∧
        dist ((x₀⁻¹ * x : G) : RMat) (f x : RMat) ≤ 6400 * B ^ 6 * δ / r) ∧
      ∀ x y : A, Commute (f x) (f y) := by
  let S := (fun x : G => x₀⁻¹ * x) '' A
  have hB0 : 0 ≤ B := by linarith
  have hS : ∀ y ∈ S, ∀ i j, |y i j| ≤ 2 * B ^ 2 := by
    rintro y ⟨x, hx, rfl⟩
    intro i j
    simpa only [pow_two, mul_assoc] using
      matrixEntryBox_mul (matrixEntryBox_inv (hA x₀ hx₀)) (hA x hx) i j
  have hcomm : ∀ y ∈ S, ∀ i j,
      |((g : RMat) * (y : RMat) - (y : RMat) * (g : RMat)) i j| ≤ 4 * B ^ 2 * δ := by
    rintro y ⟨x, hx, rfl⟩ i j
    have hh := conjugacy_fiber_commutator_bound g x₀ x hB0 (hA x₀ hx₀) (hA x hx) (hclose x hx) i j
    simpa only [Matrix.sub_apply, abs_sub_comm] using hh
  have hsmall' : 96 * (2 * B ^ 2) * (4 * B ^ 2 * δ) ≤ r := by
    convert hsmall using 1; ring
  obtain ⟨f, hform, _hentry, hdist, hpair⟩ := exists_near_identity_commuting_approximants g
    hα hαhalf hg hr hfar (by nlinarith [one_le_pow₀ (n := 2) hB] : 1 ≤ 2 * B ^ 2)
    (by positivity : 0 ≤ 4 * B ^ 2 * δ) hsmall' hS hcomm
  let k (x : A) : S := ⟨x₀⁻¹ * x, Set.mem_image_of_mem _ x.2⟩
  refine ⟨fun x => f (k x), fun x => hform (k x), ?_, fun x y => hpair (k x) (k y)⟩
  intro x
  refine ⟨Set.mul_mem_mul (Set.inv_mem_inv.mpr hx₀) x.2, ?_⟩
  have hh := hdist (k x)
  convert hh using 1; ring

end TransposeFollowup.SL2Projection

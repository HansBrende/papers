import TransposeFollowup.TraceBucketCover
import TransposeFollowup.SeparatedScalarCover

/-! Trace-driven extraction of an exact commuting family. The conjugating
set and the candidate set are independent. Separation from the identity
is required only of candidates, not of the conjugating set. All covering
numbers are the native external covering numbers at the stated radius. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Matrix.Norms.Frobenius Pointwise ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem exists_trace_commuting_extraction {A D : Set G} {α r B : ℝ} {η : ℝ≥0}
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hr : 0 < r) (hB : 1 ≤ B) (hη : 0 < η)
    (hAn : A.Nonempty) (hDn : D.Nonempty)
    (hA : ∀ x ∈ A, ∀ i j, |x i j| ≤ B)
    (hD : ∀ g ∈ D, ∀ i j, |g i j| ≤ B)
    (hnear : D ⊆ mobiusIdentityBall α)
    (hfar : ∀ g ∈ D, r ≤ dist (g : RMat) 1)
    (hsmall : 1536 * B ^ 4 * (η : ℝ) ≤ r) :
    ∃ g ∈ D, ∃ c : RMat,
      let S := {x : G | x ∈ A ∧ dist ((x * g * x⁻¹ : G) : RMat) c ≤ (η : ℝ)}
      ∃ x₀ ∈ S, ∃ f : S → G,
        (∀ x : S, ∃ s t : ℝ, (f x : RMat) = scalarAffine (g : RMat) s t) ∧
        (∀ x : S, x₀⁻¹ * x ∈ A⁻¹ * A ∧
          dist ((x₀⁻¹ * x : G) : RMat) (f x : RMat) ≤ 12800 * B ^ 6 * (η : ℝ) / r) ∧
        (∀ x y : S, Commute (f x) (f y)) ∧
        Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) ≠ ⊤ ∧
        Metric.externalCoveringNumber η ((fun g : G => Matrix.trace (g : RMat)) '' D) ≠ ⊤ ∧
        Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (A * D * A⁻¹)) ≠ ⊤ ∧
        Metric.externalCoveringNumber η (Set.range (fun x : S => (f x : RMat))) ≠ ⊤ ∧
        (Metric.externalCoveringNumber η ((fun g : G => Matrix.trace (g : RMat)) '' D) : ℝ≥0∞).toReal *
            (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal ≤
          9 * (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (A * D * A⁻¹)) : ℝ≥0∞).toReal *
            (102400 * B ^ 7 / r + 8 * B + 1) ^ 4 *
              (Metric.externalCoveringNumber η (Set.range (fun x : S => (f x : RMat))) : ℝ≥0∞).toReal := by
  have hB0 : 0 ≤ B := by linarith
  have hηR : (0 : ℝ) < η := hη
  have htrn : ((fun g : G => Matrix.trace (g : RMat)) '' D).Nonempty := hDn.image _
  have htrbound : ∀ t ∈ (fun g : G => Matrix.trace (g : RMat)) '' D, |t| ≤ 2 * B := by
    rintro t ⟨g, hg, rfl⟩
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    linarith [abs_add_le (g 0 0) (g 1 1), hD g hg 0 0, hD g hg 1 1]
  obtain ⟨T, hT, hTD, hsep, htrfin, htrcard⟩ :=
    exists_separated_scalar_cover (by positivity : 0 ≤ 2 * B) hη htrn htrbound
  have hCbound : ∀ z ∈ A * D * A⁻¹, ∀ i j, |z i j| ≤ 4 * B ^ 3 := by
    rintro z ⟨u, ⟨x, hx, g, hg, rfl⟩, v, hv, rfl⟩
    have hv' : v⁻¹ ∈ A := by simpa only [inv_inv] using Set.inv_mem_inv.mpr hv
    have hvb : v ∈ matrixEntryBox B := by
      simpa only [inv_inv] using matrixEntryBox_inv (hA v⁻¹ hv')
    intro i j
    have hh := matrixEntryBox_mul (matrixEntryBox_mul (hA x hx) (hD g hg)) hvb i j
    convert hh using 1; ring
  have hCfin : Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' (A * D * A⁻¹)) ≠ ⊤ := by
    apply finite_coveringNumber_of_entry_bound (by positivity : 0 ≤ 4 * B ^ 3) hη
    rintro z ⟨x, hx, rfl⟩
    exact hCbound x hx
  obtain ⟨F, hFcover, hFcard⟩ := Metric.exists_finset_card_eq_externalCoveringNumber hCfin
  have hcover : ∀ z ∈ A * D * A⁻¹, ∃ c ∈ F, dist (z : RMat) c ≤ (η : ℝ) := by
    intro z hz
    obtain ⟨c, hc, hd⟩ := hFcover ⟨z, hz, rfl⟩
    exact ⟨c, hc, by exact_mod_cast edist_le_coe.mp hd⟩
  obtain ⟨g, hg, E, _hEF, hEFcard, hEcover⟩ :=
    exists_small_conjugacy_orbit_cover T F hT hTD hsep hcover
  obtain ⟨c, _hc, x₀, hx₀, f, hform, hclose, hcomm, hAfin, hVfin, hbig⟩ :=
    exists_large_conjugacy_fiber_commuting_cover g E hα hαhalf (hnear hg) hr (hfar g hg)
      hB hηR.le hη hsmall hAn hA hEcover
  have hcoef : 8 * B * (12800 * B ^ 6 * (η : ℝ) / r + (η : ℝ)) / (η : ℝ) + 1 =
      102400 * B ^ 7 / r + 8 * B + 1 := by
    field_simp
    ring
  rw [hcoef] at hbig
  have hFcardR : (F.card : ℝ) =
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (A * D * A⁻¹)) : ℝ≥0∞).toReal := by
    have hh : (F.card : ℝ≥0∞) =
        (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (A * D * A⁻¹)) : ℝ≥0∞) := by
      exact_mod_cast hFcard
    simpa only [ENNReal.toReal_natCast] using congrArg ENNReal.toReal hh
  have hEFcardR : (T.card : ℝ) * (E.card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hEFcard
  refine ⟨g, hg, c, x₀, hx₀, f, hform, hclose, hcomm, hAfin, htrfin, hCfin, hVfin, ?_⟩
  let K := (102400 * B ^ 7 / r + 8 * B + 1) ^ 4
  let V := Set.range (fun x => (f x : RMat))
  change _ ≤ 9 * (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (A * D * A⁻¹)) : ℝ≥0∞).toReal *
    K * (Metric.externalCoveringNumber η V : ℝ≥0∞).toReal
  calc
    _ ≤ (9 * (T.card : ℝ)) *
        ((E.card : ℝ) * K * (Metric.externalCoveringNumber η V : ℝ≥0∞).toReal) :=
      mul_le_mul htrcard hbig ENNReal.toReal_nonneg (by positivity)
    _ = 9 * ((T.card : ℝ) * (E.card : ℝ)) * K *
        (Metric.externalCoveringNumber η V : ℝ≥0∞).toReal := by ring
    _ ≤ 9 * (F.card : ℝ) * K * (Metric.externalCoveringNumber η V : ℝ≥0∞).toReal := by
      apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
      apply mul_le_mul_of_nonneg_right _ (by dsimp only [K]; positivity)
      exact mul_le_mul_of_nonneg_left hEFcardR (by norm_num)
    _ = _ := by rw [hFcardR]

theorem trace_commuting_loss_le {B r : ℝ} (hB : 0 ≤ B) (hr : 0 < r) (hr1 : r ≤ 1) :
    9 * (102400 * B ^ 7 / r + 8 * B + 1) ^ 4 ≤
      9 * (102400 * B ^ 7 + 8 * B + 1) ^ 4 / r ^ 4 := by
  have he : 102400 * B ^ 7 / r + 8 * B + 1 ≤ (102400 * B ^ 7 + 8 * B + 1) / r := by
    apply (le_div_iff₀ hr).mpr
    have hh : (8 * B + 1) * r ≤ (8 * B + 1) * 1 :=
      mul_le_mul_of_nonneg_left hr1 (by positivity)
    have hc : (102400 * B ^ 7 / r + 8 * B + 1) * r =
        102400 * B ^ 7 + (8 * B + 1) * r := by field_simp; ring
    rw [hc]
    linarith
  calc
    _ ≤ 9 * ((102400 * B ^ 7 + 8 * B + 1) / r) ^ 4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) he 4) (by norm_num)
    _ = _ := by rw [div_pow, mul_div_assoc]

end TransposeFollowup.SL2Projection

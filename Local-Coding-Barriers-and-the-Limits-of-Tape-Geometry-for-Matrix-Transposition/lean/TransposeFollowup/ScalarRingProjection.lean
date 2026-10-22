import TransposeFollowup.RoundedDilateProjections
import OAI.MeasureTheory.Falconer.Geometry.ScalarWeakRadiusProjection

/-! Reuse the imported projection theorem to obtain a scalar sum/product
alternative. The scalar distribution and all quantitative budgets stay explicit. -/
namespace TransposeFollowup.ScalarMetric
open scoped Pointwise
open Finset OAI.Falconer
set_option autoImplicit false

/-- The actual retained ratio family inherits a proved scalar distribution,
with the size loss and dilation loss charged separately. -/
theorem small_sum_product_coefficient_family {δ K C s : ℝ}
    (hδ : 0 < δ) (hK : 0 < K) (hC : 1 ≤ C) (hs : 0 ≤ s)
    (X : Finset ℝ) (hX : X.Nonempty)
    (hbound : ∀ x ∈ X, 1 ≤ x ∧ x ≤ 2)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x - y|)
    (hsum : ((scalarCells δ (X + X)).card : ℝ) ≤ K * X.card)
    (hproduct : ((scalarCells δ (X * X)).card : ℝ) ≤ K * X.card)
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass X u r ≤ C * r ^ s * X.card) :
    ∃ F : Finset ℝ, F.Nonempty ∧ (X.card : ℝ) ≤ 2 * K * F.card ∧
      (∀ f ∈ F, |f| ≤ 2) ∧
      (∀ u r : ℝ, δ ≤ r → scalarBallMass F u r ≤
        (2 * K * C * (2 : ℝ) ^ s) * r ^ s * F.card) ∧
      ∀ f ∈ F, ((scalarCells δ (X + X.image (fun x => f * x))).card : ℝ) ≤
        54880 * K ^ 4 * X.card := by
  classical
  obtain ⟨a, ha, E, hEX, hsize, hproj⟩ :=
    small_sum_product_gives_small_projections hδ hK X hX hbound hsep hsum hproduct
  have ha0 : 0 < a := by linarith [(hbound a ha).1]
  have hE : E.Nonempty := by
    by_contra hn
    have he : E = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [he, card_empty, Nat.cast_zero, mul_zero] at hsize
    exact (not_le_of_gt (show (0 : ℝ) < X.card by exact_mod_cast hX.card_pos)) hsize
  let F := E.image (fun y => y / a)
  have hFcard : F.card = E.card := by
    simpa only [neg_div_neg_eq] using scalar_ratio_family_card (neg_ne_zero.mpr ha0.ne') E
  refine ⟨F, hE.image _, ?_, ?_, ?_, ?_⟩
  · simpa only [hFcard] using hsize
  · intro f hf
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hf
    have hbds := hbound b (hEX hb)
    rw [abs_of_pos (div_pos (by linarith) ha0), div_le_iff₀ ha0]
    nlinarith [(hbound a ha).1]
  · intro u r hr
    have h := scalar_ratio_family_ball hδ hs hC (by norm_num : (1 : ℝ) ≤ 2)
      (neg_ne_zero.mpr ha0.ne') (by simpa [abs_of_pos ha0] using (hbound a ha).2)
      X E hEX hsize hball u r hr
    simpa only [neg_div_neg_eq] using h
  · intro f hf
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hf
    exact hproj b hb

/-- At sufficiently fine dyadic scales, a scalar set in `[1,2]` satisfying
an explicit nonconcentration profile cannot have both small sums and products.
The three displayed loss budgets make the imported projection invocation concrete. -/
theorem scalar_sum_product_alternative {κ : ℝ} (hκ : 0 < κ) (hκone : κ ≤ 1) :
    ∃ ε : ℝ, ∃ J : ℕ, 0 < ε ∧ 0 < J ∧ ∀ n : ℕ, J ≤ n →
      let δ := (1 / 2 : ℝ) ^ n
      let W := Real.exp (ε * ((n + 1 : ℕ) : ℝ) * Real.log 2)
      ∀ K C : ℝ, 1 ≤ K → 1 ≤ C →
      109760 * K ^ 4 ≤ W →
      (2 : ℝ) ^ (2 * κ) * C ≤ W →
      (2 : ℝ) ^ (2 * κ) * (2 * K * C * (2 : ℝ) ^ (2 * κ)) ≤ W →
      ∀ X : Finset ℝ, X.Nonempty →
      (∀ x ∈ X, 1 ≤ x ∧ x ≤ 2) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x - y|) →
      Real.log (X.card : ℝ) ≤ (1 - κ) * (n : ℝ) * Real.log 2 →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 →
        scalarBallMass X u r ≤ C * r ^ (2 * κ) * X.card) →
      K * X.card < ((scalarCells δ (X + X)).card : ℝ) ∨
        K * X.card < ((scalarCells δ (X * X)).card : ℝ) := by
  obtain ⟨ε, J, hε, hJ, hprojection⟩ := Regularization.scalar_weak_radius_projection hκ hκone
  refine ⟨ε, J, hε, hJ, ?_⟩
  intro n hn
  dsimp only
  intro K C hK hC hprojBudget hpointBudget hcoeffBudget X hX hbound hsep hsize hball
  let δ := (1 / 2 : ℝ) ^ n
  let W := Real.exp (ε * ((n + 1 : ℕ) : ℝ) * Real.log 2)
  have hδ : 0 < δ := by positivity
  have hδone : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hδfine : (1 / 2 : ℝ) ^ (n + 1) = δ / 2 := by
    rw [pow_succ]
    dsimp [δ]
    ring
  have hs : 0 ≤ 2 * κ := by positivity
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hKfour : K ≤ K ^ 4 := by
    have hsq : K ≤ K ^ 2 := by nlinarith [mul_nonneg hK0.le (sub_nonneg.mpr hK)]
    have hfour : K ^ 2 ≤ (K ^ 2) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg K) (show 0 ≤ K ^ 2 - 1 by nlinarith)]
    nlinarith only [hsq, hfour]
  have hKW : 2 * K ≤ W := by dsimp [W]; nlinarith [sq_nonneg (K ^ 2)]
  have hWtwo : 2 ≤ W := by linarith
  by_contra hfail
  push Not at hfail
  obtain ⟨hsum, hproduct⟩ := hfail
  obtain ⟨F, hF, hFsize, hFbound, hFball, hFproj⟩ :=
    small_sum_product_coefficient_family hδ hK0 hC hs X hX hbound hsep hsum hproduct hball
  let Y := scalarZoom 0 2 X
  have hYcard : Y.card = X.card := scalarZoom_card (by norm_num) X
  have hY : Y.Nonempty := hX.image _
  have hYbound : ∀ y ∈ Y, |y| ≤ 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    have hxds := hbound x hx
    change |(x - 0) / 2| ≤ 1
    rw [sub_zero, abs_of_pos (by linarith : 0 < x / 2)]
    linarith
  have hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → (1 / 2 : ℝ) ^ (n + 1) ≤ |x - y| := by
    rw [hδfine]
    exact scalarZoom_separated (by norm_num) X hsep
  have hYsize : Real.log (Y.card : ℝ) ≤ (1 - κ) * ((n + 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [hYcard]
    push_cast
    have hnonneg : 0 ≤ (1 - κ) * Real.log 2 :=
      mul_nonneg (sub_nonneg.mpr hκone) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    nlinarith
  have htransfer (f : ℝ) :
      ((scalarCells ((1 / 2 : ℝ) ^ (n + 1)) (Y + Y.image (fun x => f * x))).card : ℝ) ≤
        2 * (scalarCells δ (X + X.image (fun x => f * x))).card := by
    dsimp only [Y]
    rw [hδfine, scalar_zoom_linear_sum]
    exact_mod_cast scalar_zoom_cells hδ (by norm_num : (0 : ℝ) < 2) ((1 + f) * 0)
      (X + X.image (fun x => f * x))
  have hYdouble : ((scalarCells ((1 / 2 : ℝ) ^ (n + 1)) (Y + Y)).card : ℝ) ≤ W * Y.card := by
    have h := htransfer 1
    simp only [one_mul, image_id'] at h
    rw [hYcard]
    have hbudget := mul_le_mul_of_nonneg_right hKW (Nat.cast_nonneg X.card)
    nlinarith
  have hYball : ∀ u r : ℝ, (1 / 2 : ℝ) ^ (n + 1) ≤ r → r ≤ 1 →
      scalarBallMass Y u r ≤ W * r ^ κ * Y.card := by
    intro u r hr hr1
    rw [hδfine] at hr
    have hr0 : 0 < r := (div_pos hδ (by norm_num)).trans_le hr
    have hb := scalar_zoom_ball_bound hδ (by norm_num : (1 : ℝ) ≤ 2) hC hs 0 X hball u r hr hr1
    have hpow : r ^ (2 * κ) ≤ r ^ κ :=
      Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
    have hc : (2 : ℝ) ^ (2 * κ) * C * r ^ (2 * κ) ≤ W * r ^ κ :=
      mul_le_mul hpointBudget hpow (Real.rpow_nonneg hr0.le _) (Real.exp_pos _).le
    exact hb.trans (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg Y.card))
  have hFfine : ∀ u r : ℝ, (1 / 2 : ℝ) ^ (n + 1) ≤ r → r ≤ 1 →
      scalarBallMass F u r ≤ W * r ^ (2 * κ) * F.card := by
    intro u r hr hr1
    rw [hδfine] at hr
    have hr0 : 0 < r := (div_pos hδ (by norm_num)).trans_le hr
    have hb := scalar_refined_ball_bound (div_pos hδ (by norm_num)) hδone
      (by norm_num : (1 : ℝ) ≤ 2) (by linarith : δ ≤ 2 * (δ / 2))
      (show 0 ≤ 2 * K * C * (2 : ℝ) ^ (2 * κ) by positivity) hs F
      (fun u r hr _ => hFball u r hr) u r hr hr1
    have hc := mul_le_mul_of_nonneg_right hcoeffBudget
      (show 0 ≤ r ^ (2 * κ) * (F.card : ℝ) by positivity)
    exact hb.trans (by nlinarith only [hc])
  obtain ⟨f, hf, hgain⟩ := hprojection (n + 1) (by omega) Y hY hYbound hYsep hYsize
    hYdouble hYball F hF (fun f hf => (hFbound f hf).trans hWtwo) hFfine
  have hlower := htransfer f
  have hupper := hFproj f hf
  have hbudget := mul_le_mul_of_nonneg_right hprojBudget (Nat.cast_nonneg X.card)
  rw [hYcard] at hgain
  change W * (X.card : ℝ) < _ at hgain
  nlinarith

end TransposeFollowup.ScalarMetric

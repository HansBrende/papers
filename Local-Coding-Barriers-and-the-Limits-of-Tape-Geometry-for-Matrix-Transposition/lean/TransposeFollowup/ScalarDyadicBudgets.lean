import TransposeFollowup.DyadicCenterTrimming

/-! One actual dyadic scalar radius pays the approximation, cardinality
and all three scalar-growth budgets. Strict exponent margins absorb
fixed constants before the matrix scale and sample are chosen. -/
namespace TransposeFollowup.SL2Projection
set_option autoImplicit false

theorem exists_dyadic_power_comparison {c a b : ℝ} (hc : 0 < c) (hab : a < b) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      c * ((1 / 4 : ℝ) ^ j) ^ (-a) ≤ ((1 / 4 : ℝ) ^ j) ^ (-b) := by
  obtain ⟨J, hJ⟩ := exists_dyadic_scaled_rpow_bound hc (sub_pos.mpr hab)
  refine ⟨J, ?_⟩
  intro j hj
  have hη : 0 < (1 / 4 : ℝ) ^ j := by positivity
  have he : ((1 / 4 : ℝ) ^ j) ^ (b - a) * ((1 / 4 : ℝ) ^ j) ^ (-b) =
      ((1 / 4 : ℝ) ^ j) ^ (-a) := by
    rw [← Real.rpow_add hη]
    congr 1
    ring
  calc
    _ = (c * ((1 / 4 : ℝ) ^ j) ^ (b - a)) *
        ((1 / 4 : ℝ) ^ j) ^ (-b) := by rw [mul_assoc, he]
    _ ≤ 1 * ((1 / 4 : ℝ) ^ j) ^ (-b) :=
      mul_le_mul_of_nonneg_right (hJ j hj) (by positivity)
    _ = _ := one_mul _

theorem exists_scalar_dyadic_radius {d : ℝ} (hd : 0 < d) (hdone : d ≤ 1) (J : ℕ) :
    ∃ J₀ : ℕ, ∀ j : ℕ, J₀ ≤ j →
      let η := (1 / 4 : ℝ) ^ j
      ∃ k : ℕ, J ≤ k ∧ η ≤ (1 / 2 : ℝ) ^ k ∧
        η ^ d ≤ (1 / 2 : ℝ) ^ k ∧ (1 / 2 : ℝ) ^ k < 2 * η ^ d := by
  obtain ⟨J₀, hJ₀⟩ := exists_separation_window_threshold hd J
  refine ⟨J₀, ?_⟩
  intro j hj η
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηone : η ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hx : η ^ d ≤ (1 / 2 : ℝ) ^ J :=
    ((hJ₀ j hj).trans (min_le_right _ _)).trans
      (pow_le_pow_left₀ (by norm_num) (by norm_num) J)
  have hxone : η ^ d ≤ 1 := hx.trans (pow_le_one₀ (by norm_num) (by norm_num))
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near_of_lt_one
    (Real.rpow_pos_of_pos hη d) hxone
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hJk : J ≤ k := by
    by_contra hn
    have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (show k + 1 ≤ J by omega)
    exact (not_lt_of_ge (hx.trans hp)) hklo
  have hηd : η ≤ η ^ d := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hη hηone hdone
  refine ⟨k, hJk, hηd.trans hkhi, hkhi, ?_⟩
  rw [pow_succ] at hklo
  linarith only [hklo]

/-- This is a simultaneous scale choice, not a family of independently
chosen thresholds. All constants and exponent margins precede `j` and `k`. -/
theorem exists_scalar_growth_budget_scale
    {d e κ g c u τ K₀ C₀ V₀ E₀ : ℝ}
    (hd : 0 < d) (hdone : d ≤ 1) (he : 0 < e)
    (hκone : κ ≤ 1) (hg : 0 ≤ g) (hc : 0 ≤ c)
    (hK₀ : 1 ≤ K₀) (hC₀ : 1 ≤ C₀) (hV₀ : 0 < V₀) (hE₀ : 0 < E₀)
    (hfour : 4 * g < d * e) (hjoint : g + c < d * e)
    (hsize : u < d * (1 - κ)) (herror : d < τ) (J : ℕ) :
    ∃ J₀ : ℕ, ∀ j : ℕ, J₀ ≤ j →
      let η := (1 / 4 : ℝ) ^ j
      let K := K₀ * η ^ (-g)
      let C := C₀ * η ^ (-c)
      ∃ k : ℕ, J ≤ k ∧
        let δ := (1 / 2 : ℝ) ^ k
        let W := Real.exp (e * ((k + 1 : ℕ) : ℝ) * Real.log 2)
        η ≤ δ ∧ η ^ d ≤ δ ∧ δ < 2 * η ^ d ∧
        1 ≤ K ∧ 1 ≤ C ∧
        109760 * K ^ 4 ≤ W ∧ (2 : ℝ) ^ (2 * κ) * C ≤ W ∧
        (2 : ℝ) ^ (2 * κ) * (2 * K * C * (2 : ℝ) ^ (2 * κ)) ≤ W ∧
        E₀ * η ^ τ ≤ δ ∧
        ∀ m : ℝ, 0 < m → m ≤ V₀ * η ^ (-u) →
          Real.log m ≤ (1 - κ) * (k : ℝ) * Real.log 2 := by
  have hK₀p : 0 < K₀ := zero_lt_one.trans_le hK₀
  have hC₀p : 0 < C₀ := zero_lt_one.trans_le hC₀
  obtain ⟨Jr, hJr⟩ := exists_scalar_dyadic_radius hd hdone J
  obtain ⟨Jk, hJk⟩ := exists_dyadic_power_comparison
    (by positivity : 0 < 109760 * K₀ ^ 4) hfour
  obtain ⟨Jc, hJc⟩ := exists_dyadic_power_comparison
    (by positivity : 0 < (2 : ℝ) ^ (2 * κ) * C₀)
    (by linarith only [hjoint, hg] : c < d * e)
  obtain ⟨Jkc, hJkc⟩ := exists_dyadic_power_comparison
    (by positivity : 0 < (2 : ℝ) ^ (2 * κ) * (2 * K₀ * C₀ * (2 : ℝ) ^ (2 * κ))) hjoint
  obtain ⟨Je, hJe⟩ := exists_dyadic_scaled_rpow_bound hE₀ (sub_pos.mpr herror)
  obtain ⟨Jv, hJv⟩ := exists_dyadic_scaled_rpow_bound
    (by positivity : 0 < (2 : ℝ) ^ (1 - κ) * V₀) (sub_pos.mpr hsize)
  refine ⟨max Jr (max Jk (max Jc (max Jkc (max Je Jv)))), ?_⟩
  intro j hj η K C
  have hjr : Jr ≤ j := le_trans (le_max_left _ _) hj
  have hjk : Jk ≤ j := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hj
  have hjc : Jc ≤ j := by omega
  have hjkc : Jkc ≤ j := by omega
  have hje : Je ≤ j := by omega
  have hjv : Jv ≤ j := by omega
  obtain ⟨k, hJk', hηδ, hδlo, hδhi⟩ := hJr j hjr
  let δ := (1 / 2 : ℝ) ^ k
  let W := Real.exp (e * ((k + 1 : ℕ) : ℝ) * Real.log 2)
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηone : η ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hW : η ^ (-(d * e)) ≤ W := by
    have hnext : (1 / 2 : ℝ) ^ (k + 1) ≤ η ^ d := by
      rw [pow_succ]
      linarith only [hδhi]
    calc
      _ = (η ^ d) ^ (-e) := by rw [← Real.rpow_mul hη.le]; congr 1; ring
      _ ≤ ((1 / 2 : ℝ) ^ (k + 1)) ^ (-e) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hnext (neg_nonpos.mpr he.le)
      _ = W := by
        rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
        simp only [one_div, Real.log_inv]
        congr 1
        ring
  have hK : 1 ≤ K := by
    have hh := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hη hηone (neg_nonpos.mpr hg)
    exact one_le_mul_of_one_le_of_one_le hK₀ hh
  have hC : 1 ≤ C := by
    have hh := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hη hηone (neg_nonpos.mpr hc)
    exact one_le_mul_of_one_le_of_one_le hC₀ hh
  refine ⟨k, hJk', hηδ, hδlo, hδhi, hK, hC, ?_, ?_, ?_, ?_, ?_⟩
  · apply le_trans ?_ hW
    have hp : (η ^ (-g)) ^ 4 = η ^ (-(4 * g)) := by
      rw [← Real.rpow_mul_natCast hη.le]
      congr 1
      norm_num
      ring
    calc
      _ = 109760 * K₀ ^ 4 * η ^ (-(4 * g)) := by
        dsimp only [K]
        rw [mul_pow, hp]
        ring
      _ ≤ _ := hJk j hjk
  · apply le_trans ?_ hW
    simpa only [C, mul_assoc] using hJc j hjc
  · apply le_trans ?_ hW
    have hp : η ^ (-(g + c)) = η ^ (-g) * η ^ (-c) := by
      rw [← Real.rpow_add hη]
      congr 1
      ring
    convert hJkc j hjkc using 1
    dsimp only [K, C]
    rw [hp]
    ring
  · apply le_trans ?_ hδlo
    have hh₀ : E₀ * η ^ (τ - d) ≤ 1 := hJe j hje
    have hh := mul_le_mul_of_nonneg_right hh₀ (Real.rpow_nonneg hη.le d)
    have hp : η ^ (τ - d) * η ^ d = η ^ τ := by
      rw [← Real.rpow_add hη, sub_add_cancel]
    simpa only [one_mul, mul_assoc, hp] using hh
  · intro m hm hmv
    have hp : η ^ (d * (1 - κ) - u) * η ^ (-(d * (1 - κ))) = η ^ (-u) := by
      rw [← Real.rpow_add hη]
      congr 1
      ring
    have hv : V₀ * η ^ (-u) ≤ (2 * η ^ d) ^ (-(1 - κ)) := by
      have hh₀ : (2 : ℝ) ^ (1 - κ) * V₀ * η ^ (d * (1 - κ) - u) ≤ 1 := hJv j hjv
      have hh := mul_le_mul_of_nonneg_right hh₀
        (Real.rpow_nonneg hη.le (-(d * (1 - κ))))
      simp only [one_mul, mul_assoc, hp] at hh
      have heq : (2 * η ^ d) ^ (-(1 - κ)) =
          η ^ (-(d * (1 - κ))) / (2 : ℝ) ^ (1 - κ) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hη.le d),
          ← Real.rpow_mul hη.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          show d * -(1 - κ) = -(d * (1 - κ)) by ring, div_eq_mul_inv, mul_comm]
      rw [heq]
      apply (le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (1 - κ))).mpr
      simpa only [mul_comm, mul_left_comm] using hh
    have hcard : m ≤ δ ^ (-(1 - κ)) :=
      hmv.trans (hv.trans (Real.rpow_le_rpow_of_nonpos hδ hδhi.le (by linarith only [hκone])))
    have hl := Real.log_le_log hm hcard
    rw [Real.log_rpow hδ, show Real.log δ = -(k : ℝ) * Real.log 2 by
      simp only [δ, Real.log_pow, one_div, Real.log_inv]; ring] at hl
    nlinarith only [hl]

/-- The scalar growth margins need only upper bounds on the exponent.
The original exact choice and the two-stage trace-square choice share this proof. -/
theorem scalar_exponent_margins_of_bounds {κ₀ e θ : ℝ}
    (hκ₀ : 0 < κ₀) (hκ₀one : κ₀ ≤ 1) (he : 0 < e) (heone : e ≤ 1)
    (hθ : 0 < θ) (hθe : θ ≤ e / 4096) (hθκ : θ ≤ κ₀ / 4096) :
    let d := 1 - 3 * θ
    let κ := κ₀ / 12
    let g := e / 8
    let c := 100 * θ
    let u := 1 - κ₀ / 3 + 84 * θ
    let τ := 1 - 2 * θ
    0 < d ∧ d ≤ 1 ∧ 0 < κ ∧ κ ≤ 1 ∧
      0 ≤ g ∧ 0 ≤ c ∧ 4 * g < d * e ∧ g + c < d * e ∧
      u < d * (1 - κ) ∧ d < τ ∧
      289 * θ / 3 < c ∧ 83 * θ < 84 * θ ∧ 173 * θ < g := by
  intro d κ g c u τ
  have hθone : θ ≤ 1 / 4096 := hθe.trans
    (div_le_div_of_nonneg_right heone (by norm_num))
  have hθemul : 0 ≤ θ * (1 - e) := mul_nonneg hθ.le (sub_nonneg.mpr heone)
  have hθκmul : 0 ≤ θ * κ₀ := mul_nonneg hθ.le hκ₀.le
  dsimp only [d, κ, g, c, u, τ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hθone]
  · linarith only [hθ]
  · positivity
  · linarith only [hκ₀one]
  · positivity
  · positivity
  · nlinarith only [he, hθe, hθemul]
  · nlinarith only [he, hθe, hθemul]
  · nlinarith only [hκ₀, hθκ, hθκmul]
  · linarith only [hθ]
  · linarith only [hθ]
  · linarith only [hθ]
  · linarith only [he, hθe]

end TransposeFollowup.SL2Projection

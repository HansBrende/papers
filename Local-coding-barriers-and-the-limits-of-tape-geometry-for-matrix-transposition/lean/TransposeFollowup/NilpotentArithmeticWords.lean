import TransposeFollowup.NilpotentScalarArithmetic
import TransposeFollowup.ActualTraceCoefficient
import TransposeFollowup.SL2TranslatedCluster
import TransposeFollowup.TraceBucketCover

/-! Actual bounded words realize the fixed-matrix scalar arithmetic.
The native Frobenius multiplication bounds charge both approximant error
and a small nonzero determinant of the centered generator. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Pointwise Matrix.Norms.Frobenius
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem frobenius_product_distance (a a' b b' : RMat) :
    dist (a * b) (a' * b') ≤ dist a a' * ‖b‖ + ‖a'‖ * dist b b' := by
  exact (dist_triangle _ (a' * b) _).trans
    (add_le_add (frobenius_dist_right_mul a a' b) (frobenius_dist_left_mul a' b b'))

/-- Shared native distance bounds; trace and weighted-trace readouts use
this same calculation. Only `v`, `u'` and the fixed factors need entry bounds. -/
theorem two_source_word_distances (u v u' v' g h : G) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hvb : ∀ i j, |v i j| ≤ R) (hu'b : ∀ i j, |u' i j| ≤ R)
    (hg : ∀ i j, |g i j| ≤ R) (hh : ∀ i j, |h i j| ≤ R)
    (heu : dist (u : RMat) (u' : RMat) ≤ ε)
    (hev : dist (v : RMat) (v' : RMat) ≤ ε) :
    dist ((u * v * g : G) : RMat) ((u' * v' * g : G) : RMat) ≤ 8 * R ^ 2 * ε ∧
      dist ((u * g * v * h : G) : RMat) ((u' * g * v' * h : G) : RMat) ≤
        16 * R ^ 3 * ε := by
  have hvn := frobenius_norm_le_of_entry_bound hR hvb
  have hu'n := frobenius_norm_le_of_entry_bound hR hu'b
  have hgn := frobenius_norm_le_of_entry_bound hR hg
  have hgin := frobenius_norm_le_of_entry_bound hR hh
  have hpair : dist ((u * v : G) : RMat) ((u' * v' : G) : RMat) ≤ 4 * R * ε := by
    calc
      _ ≤ dist (u : RMat) (u' : RMat) * ‖(v : RMat)‖ +
          ‖(u' : RMat)‖ * dist (v : RMat) (v' : RMat) :=
        frobenius_product_distance (u : RMat) (u' : RMat) (v : RMat) (v' : RMat)
      _ ≤ ε * (2 * R) + (2 * R) * ε := add_le_add
        (mul_le_mul heu hvn (norm_nonneg _) hε) (mul_le_mul hu'n hev dist_nonneg (by positivity))
      _ = _ := by ring
  have haddDist : dist ((u * v * g : G) : RMat) ((u' * v' * g : G) : RMat) ≤
      8 * R ^ 2 * ε := by
    calc
      _ ≤ dist ((u * v : G) : RMat) ((u' * v' : G) : RMat) * ‖(g : RMat)‖ :=
        frobenius_dist_right_mul _ _ _
      _ ≤ (4 * R * ε) * (2 * R) := mul_le_mul hpair hgn (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hug : dist ((u * g : G) : RMat) ((u' * g : G) : RMat) ≤ 2 * R * ε := by
    have hh := (frobenius_dist_right_mul (u : RMat) (u' : RMat) (g : RMat)).trans
      (mul_le_mul heu hgn (norm_nonneg _) hε)
    simpa only [Matrix.SpecialLinearGroup.coe_mul, mul_comm] using hh
  have hvgi : dist ((v * h : G) : RMat) ((v' * h : G) : RMat) ≤ 2 * R * ε := by
    have hh := (frobenius_dist_right_mul (v : RMat) (v' : RMat) ((h : G) : RMat)).trans
      (mul_le_mul hev hgin (norm_nonneg _) hε)
    simpa only [Matrix.SpecialLinearGroup.coe_mul, mul_comm] using hh
  have hu'gn : ‖((u' * g : G) : RMat)‖ ≤ 4 * R ^ 2 := by
    have hh := (norm_mul_le (u' : RMat) (g : RMat)).trans
      (mul_le_mul hu'n hgn (norm_nonneg _) (by positivity))
    convert hh using 1; ring
  have hvgin : ‖((v * h : G) : RMat)‖ ≤ 4 * R ^ 2 := by
    have hh := (norm_mul_le (v : RMat) ((h : G) : RMat)).trans
      (mul_le_mul hvn hgin (norm_nonneg _) (by positivity))
    convert hh using 1; ring
  have hmulDist : dist ((u * g * v * h : G) : RMat) ((u' * g * v' * h : G) : RMat) ≤
      16 * R ^ 3 * ε := by
    have hh := frobenius_product_distance ((u * g : G) : RMat) ((u' * g : G) : RMat)
      ((v * h : G) : RMat) ((v' * h : G) : RMat)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc] at hh ⊢
    apply hh.trans
    calc
      _ ≤ (2 * R * ε) * (4 * R ^ 2) + (4 * R ^ 2) * (2 * R * ε) :=
        add_le_add (mul_le_mul hug hvgin (norm_nonneg _) (by positivity))
          (mul_le_mul hu'gn hvgi dist_nonneg (by positivity))
      _ = _ := by ring
  exact ⟨haddDist, hmulDist⟩

/-- Shared native error bound for addition words and two source factors
separated by fixed matrices. The last factor can be `g` or its inverse. -/
theorem two_source_trace_word_errors (u v u' v' g h : G) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hvb : ∀ i j, |v i j| ≤ R) (hu'b : ∀ i j, |u' i j| ≤ R)
    (hg : ∀ i j, |g i j| ≤ R) (hh : ∀ i j, |h i j| ≤ R)
    (heu : dist (u : RMat) (u' : RMat) ≤ ε)
    (hev : dist (v : RMat) (v' : RMat) ≤ ε) :
    |Matrix.trace ((u' * v' * g : G) : RMat) -
        Matrix.trace ((u * v * g : G) : RMat)| ≤ 16 * R ^ 2 * ε ∧
      |Matrix.trace ((u' * g * v' * h : G) : RMat) -
        Matrix.trace ((u * g * v * h : G) : RMat)| ≤ 32 * R ^ 3 * ε := by
  obtain ⟨haddDist, hmulDist⟩ := two_source_word_distances u v u' v' g h
    hR hε hvb hu'b hg hh heu hev
  have htraceAdd : |Matrix.trace ((u' * v' * g : G) : RMat) -
      Matrix.trace ((u * v * g : G) : RMat)| ≤ 16 * R ^ 2 * ε := by
    rw [abs_sub_comm]
    have hh := (trace_error_le_frobenius_dist _ _).trans
      (mul_le_mul_of_nonneg_left haddDist (by norm_num : (0 : ℝ) ≤ 2))
    convert hh using 1; ring
  have htraceMul : |Matrix.trace ((u' * g * v' * h : G) : RMat) -
      Matrix.trace ((u * g * v * h : G) : RMat)| ≤ 32 * R ^ 3 * ε := by
    rw [abs_sub_comm]
    have hh := (trace_error_le_frobenius_dist _ _).trans
      (mul_le_mul_of_nonneg_left hmulDist (by norm_num : (0 : ℝ) ≤ 2))
    convert hh using 1; ring
  exact ⟨htraceAdd, htraceMul⟩

theorem centered_actual_arithmetic_words (b : RMat) (u v u' v' g : G)
    {A : Set G} {m n : ℕ} {c t p q κ r T L R ε : ℝ}
    (hAi : A⁻¹ = A) (hu'A : u' ∈ A ^ m) (hv'A : v' ∈ A ^ m) (hgA : g ∈ A ^ n)
    (hb : Matrix.trace b = 0) (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (hbd : |b.det| ≤ κ) (hsmall : κ * r ^ 2 ≤ 1)
    (hu : (u : RMat) = scalarAffine b c t) (hv : (v : RMat) = scalarAffine b p q)
    (hc : 1 / 2 ≤ c) (hp : 1 / 2 ≤ p) (ht : |t| ≤ r) (hq : |q| ≤ r)
    (hT : 0 ≤ T) (hgT : |Matrix.trace (g : RMat)| ≤ T)
    (hbg : |Matrix.trace (b * (g : RMat))| ≤ L)
    (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hvb : ∀ i j, |v i j| ≤ R)
    (hu'b : ∀ i j, |u' i j| ≤ R) (hg : ∀ i j, |g i j| ≤ R)
    (heu : dist (u : RMat) (u' : RMat) ≤ ε)
    (hev : dist (v : RMat) (v' : RMat) ≤ ε) :
    let ℓ := Matrix.trace (b * (g : RMat))
    ∃ wAdd ∈ A ^ (2 * m + n), ∃ wMul ∈ A ^ (2 * m + 2 * n),
      |Matrix.trace (wAdd : RMat) - (Matrix.trace (g : RMat) + ℓ * (t + q))| ≤
          16 * R ^ 2 * ε + 4 * κ * r ^ 2 * T + 2 * κ * r ^ 3 * L ∧
        |Matrix.trace (wMul : RMat) - (2 - ℓ ^ 2 * (t * q))| ≤
          32 * R ^ 3 * ε + κ * r ^ 2 * (8 + T ^ 2) := by
  obtain ⟨htraceAdd, htraceMul⟩ := two_source_trace_word_errors u v u' v' g g⁻¹
    hR hε hvb hu'b hg (matrixEntryBox_inv hg) heu hev
  have hm {x y : G} {i j : ℕ} (hx : x ∈ A ^ i) (hy : y ∈ A ^ j) :
      x * y ∈ A ^ (i + j) := by
    rw [pow_add]
    exact Set.mul_mem_mul hx hy
  have hgiA : g⁻¹ ∈ A ^ n := by
    have hh := Set.inv_mem_inv.mpr hgA
    rwa [← inv_pow, hAi] at hh
  obtain ⟨hadd, hmul⟩ := centered_trace_arithmetic_error b u v g hb hκ hr hbd hsmall
    hu hv hc hp ht hq hT hgT hbg
  refine ⟨u' * v' * g, ?_, u' * g * v' * g⁻¹, ?_, ?_, ?_⟩
  · simpa only [show m + m + n = 2 * m + n by omega] using hm (hm hu'A hv'A) hgA
  · simpa only [show m + n + m + n = 2 * m + 2 * n by omega] using hm (hm (hm hu'A hgA) hv'A) hgiA
  · have hh := (abs_sub_le _ (Matrix.trace ((u * v * g : G) : RMat)) _).trans
      (add_le_add htraceAdd hadd)
    simpa only [add_assoc] using hh
  · exact (abs_sub_le _ (Matrix.trace ((u * g * v * g⁻¹ : G) : RMat)) _).trans
      (add_le_add htraceMul hmul)

end TransposeFollowup.SL2Projection

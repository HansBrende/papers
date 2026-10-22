import TransposeFollowup.FiniteTraceAvoidance
import TransposeFollowup.SL2NearIdentityProducts
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Topology.Instances.Matrix

/-! Bounded powers preserve a trace gap uniformly near the identity.
The geometric-sum determinant avoids eigenvectors and diagonalization. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Filter
open scoped Matrix.Norms.Frobenius Topology
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem sl2_det_sub_one (g : G) : ((g : RMat) - 1).det = 2 - Matrix.trace (g : RMat) := by
  have hd := g.property
  simp only [Matrix.det_fin_two, Matrix.sub_apply, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at *
  nlinarith only [hd]

theorem sl2_trace_power_difference_factor (g : G) (n : ℕ) :
    Matrix.trace ((g ^ n : G) : RMat) - 2 =
      (Matrix.trace (g : RMat) - 2) * (∑ k ∈ Finset.range n, (g : RMat) ^ k).det := by
  have hh := congrArg Matrix.det (geom_sum_mul (g : RMat) n)
  rw [Matrix.det_mul, sl2_det_sub_one, ← Matrix.SpecialLinearGroup.coe_pow, sl2_det_sub_one] at hh
  linarith only [hh]

theorem exists_uniform_bounded_power_trace_gap (N : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ g : G, dist (g : RMat) 1 < r →
      ∀ n : ℕ, 0 < n → n ≤ N →
        |Matrix.trace (g : RMat) - 2| / 2 ≤ |Matrix.trace ((g ^ n : G) : RMat) - 2| ∧
        |Matrix.trace ((g ^ n : G) : RMat)| ≤ 3 := by
  have hlocal (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      ∀ᶠ x : RMat in 𝓝 1,
        1 / 2 < (∑ k ∈ Finset.range n, x ^ k).det ∧ |Matrix.trace (x ^ n)| < 3 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hdetval : (∑ k ∈ Finset.range n, (1 : RMat) ^ k).det = (n : ℝ) ^ 2 := by
      simp [Matrix.det_fin_two, Matrix.natCast_apply, pow_two]
    have hdetcont : Continuous (fun x : RMat => (∑ k ∈ Finset.range n, x ^ k).det) := by fun_prop
    have htrcont : Continuous (fun x : RMat => |Matrix.trace (x ^ n)|) := by fun_prop
    have hdet : ∀ᶠ x : RMat in 𝓝 1, 1 / 2 < (∑ k ∈ Finset.range n, x ^ k).det :=
      hdetcont.continuousAt.eventually (eventually_gt_nhds (by change 1 / 2 < (∑ k ∈ Finset.range n, (1 : RMat) ^ k).det; rw [hdetval]; nlinarith only [hn1]))
    have htr : ∀ᶠ x : RMat in 𝓝 1, |Matrix.trace (x ^ n)| < 3 :=
      htrcont.continuousAt.eventually (eventually_lt_nhds (by norm_num))
    exact hdet.and htr
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    ((Filter.eventually_all_finset (Finset.Icc 1 N)).mpr hlocal)
  refine ⟨r, hr, ?_⟩
  intro g hg n hn hnN
  obtain ⟨hdet, htr⟩ := hball hg n (Finset.mem_Icc.mpr ⟨hn, hnN⟩)
  constructor
  · rw [sl2_trace_power_difference_factor, abs_mul, abs_of_pos (show 0 < (∑ k ∈ Finset.range n, (g : RMat) ^ k).det by linarith only [hdet])]
    nlinarith only [hdet, abs_nonneg (Matrix.trace (g : RMat) - 2)]
  · simpa only [Matrix.SpecialLinearGroup.coe_pow] using htr.le

theorem sl2_trace_arithmetic_progression (g h : G) (a d : ℕ) :
    Matrix.trace ((g ^ (a + 2 * d) * h : G) : RMat) + Matrix.trace ((g ^ a * h : G) : RMat) =
      Matrix.trace ((g ^ d : G) : RMat) * Matrix.trace ((g ^ (a + d) * h : G) : RMat) := by
  have hc (u v : G) : Matrix.trace ((u * u * v : G) : RMat) + Matrix.trace (v : RMat) =
      Matrix.trace (u : RMat) * Matrix.trace ((u * v : G) : RMat) := by
    have hd := u.property
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.det_fin_two, Matrix.trace,
      Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two] at *
    linear_combination -(v 0 0 + v 1 1) * hd
  have hh := hc (g ^ d) (g ^ a * h)
  have h1 : g ^ d * (g ^ a * h) = g ^ (a + d) * h := by
    rw [← mul_assoc, ← pow_add, Nat.add_comm d a]
  have h2 : g ^ d * g ^ d * (g ^ a * h) = g ^ (a + 2 * d) * h := by
    rw [← mul_assoc, ← pow_add, ← pow_add]
    congr 2
    omega
  simpa only [h1, h2] using hh

theorem exists_simultaneous_matrix_trace_gap :
    ∃ N : ℕ, ∃ r : ℝ, 0 < N ∧ 0 < r ∧ ∀ g : G,
      dist (g : RMat) 1 < r → Matrix.trace (g : RMat) ≠ 2 →
      ∀ h : Fin 4 → G, ∃ m ≤ N, ∀ i,
        |Matrix.trace (g : RMat) - 2| / 8 < |Matrix.trace ((g ^ m * h i : G) : RMat) - 2| := by
  obtain ⟨N, hN, hescape⟩ := exists_simultaneous_recurrence_escape
  obtain ⟨r, hr, hpower⟩ := exists_uniform_bounded_power_trace_gap N
  refine ⟨N, r, hN, hr, ?_⟩
  intro g hg hgne h
  have hh := hescape (fun i m => Matrix.trace ((g ^ m * h i : G) : RMat))
    (fun d => Matrix.trace ((g ^ d : G) : RMat)) (|Matrix.trace (g : RMat) - 2| / 2)
    (div_pos (abs_pos.mpr (sub_ne_zero.mpr hgne)) (by norm_num))
    (hpower g hg) (fun i a d _ _ => sl2_trace_arithmetic_progression g (h i) a d)
  simpa only [div_div, show (2 : ℝ) * 4 = 8 by norm_num] using hh

end TransposeFollowup.SL2Projection

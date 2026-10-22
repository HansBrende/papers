import TransposeFollowup.BoundedPowerTraceGap
import TransposeFollowup.SL2SpanningTrace

/-! A common bounded right translation preserves the spanning determinant
and makes all four trace coordinates quantitatively avoid two at a chosen
center. The translating element is an actual commutator of the same set. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Pointwise Matrix.Norms.Frobenius commutatorElement
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem traceFrame_det_right_translate (k : Fin 4 → G) (u : G) :
    (traceFrame (fun i => k i * u)).det = (traceFrame k).det := by
  let L : Matrix (Fin 4) (Fin 4) ℝ :=
    !![u 0 0, u 1 0, 0, 0; u 0 1, u 1 1, 0, 0;
       0, 0, u 0 0, u 1 0; 0, 0, u 0 1, u 1 1]
  have hL : L.det = 1 := by
    have hu : u 0 0 * u 1 1 - u 0 1 * u 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using u.property
    have he : L.det = (u 0 0 * u 1 1 - u 0 1 * u 1 0) ^ 2 := by
      norm_num [L, Matrix.det_succ_row_zero, Matrix.det_fin_three,
        Fin.sum_univ_succ, Fin.succAbove]
      ring
    rw [he, hu, one_pow]
  rw [traceFrame_det, traceFrame_det]
  have he : (Matrix.of fun i j => matrixCoordinates ((k j * u : G) : RMat) i) =
      L * (Matrix.of fun i j => matrixCoordinates (k j : RMat) i) := by
    ext i j
    fin_cases i <;> simp [matrixCoordinates, L, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  rw [he, Matrix.det_mul, hL, one_mul]

theorem exists_shifted_trace_frame :
    ∃ N : ℕ, ∃ r : ℝ, 0 < N ∧ 0 < r ∧ ∀ (g : G) (k : Fin 4 → G) (x : G),
      dist (g : RMat) 1 < r → Matrix.trace (g : RMat) ≠ 2 →
      ∃ m ≤ N,
        (traceFrame (fun i => k i * (g⁻¹) ^ m)).det = (traceFrame k).det ∧
        ∀ i, |Matrix.trace (g : RMat) - 2| / 8 <
          |Matrix.trace ((((k i * (g⁻¹) ^ m)⁻¹) * x : G) : RMat) - 2| := by
  obtain ⟨N, r, hN, hr, hgap⟩ := exists_simultaneous_matrix_trace_gap
  refine ⟨N, r, hN, hr, ?_⟩
  intro g k x hg htr
  obtain ⟨m, hm, hgap⟩ := hgap g hg htr (fun i => (k i)⁻¹ * x)
  refine ⟨m, hm, traceFrame_det_right_translate k _, ?_⟩
  intro i
  simpa only [_root_.mul_inv_rev, ← inv_pow, inv_inv, mul_assoc] using hgap i

theorem exists_actual_frame_away_trace_two :
    ∃ n₀ : ℕ, ∃ α₀ : ℝ, 34 ≤ n₀ ∧ 0 < α₀ ∧ α₀ ≤ 1 / 2 ∧
      ∀ {A : Set G} {α d : ℝ} {p q : G},
      1 ∈ A → A⁻¹ = A → 0 < α → α ≤ α₀ → A ⊆ mobiusIdentityBall α →
      0 < d → p ∈ A ^ 34 → q ∈ A ^ 34 → p * q ∈ A ^ 34 →
      d ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det| →
      ∀ x : G, ∃ k : Fin 4 → G,
        (∀ i, k i ∈ A ^ n₀) ∧
        d ≤ |(traceFrame k).det| ∧
        ∀ i, d / 8 < |Matrix.trace (((k i)⁻¹ * x : G) : RMat) - 2| := by
  obtain ⟨N, r, _hN, hr, hshift⟩ := exists_shifted_trace_frame
  let n₀ := 34 + 136 * N
  let α₀ := min (1 / 2) (r / (2 * (5 : ℝ) ^ 136))
  have hα₀ : 0 < α₀ := by dsimp only [α₀]; positivity
  refine ⟨n₀, α₀, by dsimp only [n₀]; omega, hα₀, min_le_left _ _, ?_⟩
  intro A α d p q hA1 hAi hα hαbound hA hd hp hq hpq hspan x
  have hαone : α ≤ 1 := (hαbound.trans (min_le_left _ _)).trans (by norm_num)
  have hp' : p⁻¹ ∈ A ^ 34 := by simpa only [← inv_pow, hAi] using Set.inv_mem_inv.mpr hp
  have hq' : q⁻¹ ∈ A ^ 34 := by simpa only [← inv_pow, hAi] using Set.inv_mem_inv.mpr hq
  let g : G := ⁅p, q⁆
  have hg : g ∈ A ^ 136 := by
    change p * q * p⁻¹ * q⁻¹ ∈ A ^ (34 + 34 + 34 + 34)
    simp only [pow_add]
    exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul hp hq) hp') hq'
  have hgnear : dist (g : RMat) 1 < r := by
    have hh := set_pow_dist_from_one_le hα hαone hA 136 g hg
    have hs := hαbound.trans (min_le_right _ _)
    have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (5 : ℝ) ^ 136)
    have he : (5 : ℝ) ^ 136 * (r / (2 * (5 : ℝ) ^ 136)) = r / 2 := by field_simp
    rw [he] at hm
    exact hh.trans_lt (hm.trans_lt (by linarith only [hr]))
  have hgspan : d ≤ |Matrix.trace (g : RMat) - 2| := by
    simpa only [SL2Escape.pairSpanMatrix_det_commutator, abs_sub_comm] using hspan
  have hgtr : Matrix.trace (g : RMat) ≠ 2 := by
    intro he
    rw [he, sub_self, abs_zero] at hgspan
    exact (not_le_of_gt hd) hgspan
  let k : Fin 4 → G := ![1, p, q, p * q]
  have hk (i : Fin 4) : k i ∈ A ^ 34 := by
    fin_cases i
    · exact Set.one_mem_pow hA1
    · exact hp
    · exact hq
    · exact hpq
  obtain ⟨m, hm, hdet, hgap⟩ := hshift g k x hgnear hgtr
  refine ⟨fun i => k i * (g⁻¹) ^ m, ?_, ?_, ?_⟩
  · intro i
    have hgi : g⁻¹ ∈ A ^ 136 := by simpa only [← inv_pow, hAi] using Set.inv_mem_inv.mpr hg
    have hgm : (g⁻¹) ^ m ∈ A ^ (136 * m) := by
      rw [pow_mul]
      exact Set.pow_mem_pow hgi
    have hmem : k i * (g⁻¹) ^ m ∈ A ^ (34 + 136 * m) := by
      rw [pow_add]
      exact Set.mul_mem_mul (hk i) hgm
    exact Set.pow_subset_pow_right hA1 (by dsimp only [n₀]; omega) hmem
  · rw [hdet]
    simpa only [k, traceFrame_pair_det] using hspan
  · intro i
    exact (div_le_div_of_nonneg_right hgspan (by norm_num)).trans_lt (hgap i)

end TransposeFollowup.SL2Projection

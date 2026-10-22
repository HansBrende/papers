import TransposeFollowup.SL2GlobalTraceCover
import TransposeFollowup.MobiusMatrixGeometryCore

/-! Apply the three-trace projection to an actual bounded-power spanning
certificate. All entry bounds and the fixed covering loss are explicit. -/
namespace TransposeFollowup.RealMobius
open Classical Set
open scoped Pointwise
set_option autoImplicit false

theorem set_pow_subset_matrixEntryBox {A : Set Group} {B : ℝ}
    (hA : A ⊆ matrixEntryBox B) (n : ℕ) :
    A ^ n ⊆ matrixEntryBox ((2 * B) ^ n) := by
  induction n with
  | zero =>
    intro x hx
    have he : x = 1 := by simpa only [pow_zero, Set.mem_one] using hx
    subst x
    simpa only [pow_zero] using one_mem_matrixEntryBox
  | succ n ih =>
    rw [pow_succ]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have hh := matrixEntryBox_mul (ih hx) (hA hy)
    rw [pow_succ, show (2 * B) ^ n * (2 * B) = 2 * (2 * B) ^ n * B by ring]
    exact hh

theorem mobiusIdentityBall_entry_zero_lower {α : ℝ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2)
    {x : Group} (hx : x ∈ mobiusIdentityBall α) : 1 / 2 ≤ |x 0 0| := by
  have hh := (abs_lt.mp (mobiusIdentityBall_entry_bounds hα hx).1).1
  exact (show 1 / 2 ≤ x 0 0 by linarith).trans (le_abs_self _)

end TransposeFollowup.RealMobius

namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

noncomputable def spanningTraceLoss : ℝ :=
  (12288 * ((4 : ℝ) ^ 34 + 1) * ((4 : ℝ) ^ 34) ^ 5 + 1) ^ 4 *
    (6144 * ((4 : ℝ) ^ 34) ^ 5 + 3) ^ 3

theorem spanningTraceLoss_pos : 0 < spanningTraceLoss := by
  unfold spanningTraceLoss
  positivity

theorem exists_large_trace_of_frame (g : Fin 4 → G) {A : Set G} {M d : ℝ}
    {η : ℝ≥0} (hM : 1 ≤ M) (hd : 0 < d) (hd1 : d ≤ 1) (hη : 0 < η)
    (hg : ∀ i j k, |g i j k| ≤ M)
    (hA : ∀ x ∈ A, ∀ j k, |x j k| ≤ M)
    (hA0 : ∀ x ∈ A, 1 / 2 ≤ |x 0 0|)
    (hdet : d ≤ |(traceFrame g).det|) :
    ∃ i : Fin 4,
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal ≤
        ((12288 * (M + 1) * M ^ 5 + 1) ^ 4 * (6144 * M ^ 5 + 3) ^ 3 / d ^ 7) *
        (Metric.externalCoveringNumber η
          ((fun x : G => Matrix.trace (((g i)⁻¹ * x : G) : RMat)) '' A) : ℝ≥0∞).toReal ^ 3 := by
  obtain ⟨i, hi⟩ := global_three_trace_coveringNumber_polynomial g hM hd hd1 hη hg hA hA0 hdet
  let T (j : Fin 4) : ℝ := (Metric.externalCoveringNumber η
    ((fun x : G => Matrix.trace (((g j)⁻¹ * x : G) : RMat)) '' A) : ℝ≥0∞).toReal
  obtain ⟨j, _hj, hmax⟩ := Finset.univ.exists_max_image T Finset.univ_nonempty
  have hp : (∏ k : Fin 3, T (i.succAbove k)) ≤ T j ^ 3 := by
    calc
      _ ≤ ∏ _k : Fin 3, T j := Finset.prod_le_prod₀
        (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => hmax _ (Finset.mem_univ _))
      _ = _ := by simp
  refine ⟨j, hi.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hp (by positivity)

theorem exists_large_trace_of_spanning {A : Set G} {α d : ℝ} {η : ℝ≥0}
    (hA1 : 1 ∈ A) (hα : 0 < α) (hαhalf : α ≤ 1 / 2)
    (hA : A ⊆ mobiusIdentityBall α) (hd : 0 < d) (hd1 : d ≤ 1) (hη : 0 < η)
    {p q : G} (hp : p ∈ A ^ 34) (hq : q ∈ A ^ 34) (hpq : p * q ∈ A ^ 34)
    (hdet : d ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det|) :
    ∃ h ∈ A ^ 34,
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal ≤
        (spanningTraceLoss / d ^ 7) * (Metric.externalCoveringNumber η
          ((fun x : G => Matrix.trace ((h⁻¹ * x : G) : RMat)) '' A) : ℝ≥0∞).toReal ^ 3 := by
  have hAb : A ⊆ matrixEntryBox 2 := hA.trans
    (mobiusIdentityBall_subset_entryBox_two hα (by linarith))
  have hpow : A ^ 34 ⊆ matrixEntryBox ((4 : ℝ) ^ 34) := by
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using set_pow_subset_matrixEntryBox hAb 34
  let g : Fin 4 → G := ![1, p, q, p * q]
  have hmem (i : Fin 4) : g i ∈ A ^ 34 := by
    fin_cases i
    · exact Set.one_mem_pow hA1
    · exact hp
    · exact hq
    · exact hpq
  have hframe : d ≤ |(traceFrame g).det| := by
    simpa only [g, traceFrame_pair_det] using hdet
  obtain ⟨i, hi⟩ := exists_large_trace_of_frame g (M := (4 : ℝ) ^ 34)
    (by norm_num) hd hd1 hη (fun i => hpow (hmem i))
    (fun x hx j k => (hAb hx j k).trans (by norm_num))
    (fun x hx => mobiusIdentityBall_entry_zero_lower hα hαhalf (hA hx)) hframe
  exact ⟨g i, hmem i, hi⟩

end TransposeFollowup.SL2Projection

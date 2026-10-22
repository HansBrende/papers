import TransposeFollowup.ContractionCorrelation
import Mathlib.Analysis.Normed.Group.Lemmas

/-! A nearby L2 limit and uniformly small discards preserve enough
quadratic correlation in at least one finite retained sum. -/
namespace TransposeFollowup
open Classical Filter
open scoped Topology
set_option autoImplicit false

theorem exists_retained_finite_correlation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    {f h : E} (hf : ‖f‖ = 1) (hcorr : 1 / 2 ≤ inner ℝ (T f) f)
    (hdist : ‖f - h‖ ≤ 1 / 16) (v w : ℕ → E)
    (hv : Tendsto v atTop (𝓝 h)) (hdiscard : ∀ N, ‖v N - w N‖ ≤ 1 / 1024) :
    ∃ N, 1 / 3 ≤ inner ℝ (T (w N)) (w N) := by
  have hvnorm := tendsto_iff_norm_sub_tendsto_zero.mp hv
  obtain ⟨N, hN⟩ := (hvnorm.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 1024)).exists
  have hd : ‖f - w N‖ ≤ 1 / 14 := by
    have h1 := dist_triangle f h (w N)
    have h2 := dist_triangle h (v N) (w N)
    simp only [dist_eq_norm] at h1 h2
    rw [norm_sub_rev h (v N)] at h2
    linarith [hdiscard N]
  have hloss := (abs_le.mp (normalized_correlation_loss_le T hT hf (1 / 14) hd)).2
  exact ⟨N, by linarith⟩

end TransposeFollowup

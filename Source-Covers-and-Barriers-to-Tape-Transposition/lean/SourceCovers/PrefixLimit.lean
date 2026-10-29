import SourceCovers.PrefixErrorLimit
import LeanMachine.BoundedLimsup

set_option autoImplicit false

/-!
# The dimension limit with fixed finite prefixes

The finite certificate is applied to each actual geometry along the common
joint-profile subsequence. Widths and omitted-family budgets are rounded up
before taking the dimension limit. No convergence of runtime or of the
original geometries' full tail masses is used.
-/

namespace SourceCovers.NearFullSequence.JointProfile

open Classical Finset Filter LeanMachine
open scoped BigOperators Topology
noncomputable section

variable {c β : ℝ} {N q : ℕ} {S : NearFullSequence c β N q}
    (P : S.JointProfile)

/-- Reciprocal cover means along the same joint-profile subsequence. -/
def prefixReciprocal (J R M : ℕ) (hM : 2 ≤ M) (n : ℕ) : ℝ :=
  (S.geometry (P.subsequence n)).prefixMeanReciprocal (S.order (P.subsequence n)) J R M hM

theorem prefixReciprocal_bounds {J R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) (n : ℕ) :
    1 / (2 * (M : ℝ) + 4) ^ q ≤ P.prefixReciprocal J R M hM n ∧
      P.prefixReciprocal J R M hM n ≤ 1 :=
  (S.geometry (P.subsequence n)).prefixMeanReciprocal_bounds
    (S.order (P.subsequence n)) hM hRM

/-- Keep the actual reciprocal cover mean through the dimension limsup.
The distinguished and protected cutoffs need not be comparable. -/
theorem prefix_reciprocal_limit {K R M J : ℕ}
    (hKJ : K ≤ J) (hRJ : R ≤ J) (hM : 2 ≤ M) (hRM : R < M)
    {lam : ℝ} (hlam : 0 < lam) :
    max (1 - ∑ i ∈ Ico K J, P.v i) 0 ^ 2 /
        (2 * (2 * (K : ℝ) + 1)) * limsup (P.prefixReciprocal J R M hM) atTop ≤
      β * (∑ i ∈ Ico R J, P.h i) / ((M - R : ℕ) : ℝ) + 2 * lam +
        β * N * (bankCost M q : ℝ) * c ^ 2 / (lam * (J + 1)) := by
  obtain ⟨w, a, F, hdata, hF⟩ := P.prefix_error_limit J R M hlam
  let credit := fun n => max (1 - ∑ i ∈ Ico K J, S.variation (P.subsequence n) i) 0 ^ 2 /
    (2 * (2 * (K : ℝ) + 1))
  have hpoint : ∀ n, credit n * P.prefixReciprocal J R M hM n ≤
      (S.geometry (P.subsequence n)).relativeDeficit + F n := by
    intro n
    obtain ⟨hw, ha0, ha, he⟩ := hdata n
    have hp := (S.geometry (P.subsequence n)).prefix_reciprocal_deficit
      (S.order (P.subsequence n)) hKJ hRJ hM hRM hw ha0 ha
    change (S.geometry (P.subsequence n)).relativeDeficit ≥
      credit n * P.prefixReciprocal J R M hM n -
        (S.geometry (P.subsequence n)).prefixError
          (S.order (P.subsequence n)) J R M (w n) (a n) at hp
    linarith
  have hcredit : Tendsto credit atTop
      (𝓝 (max (1 - ∑ i ∈ Ico K J, P.v i) 0 ^ 2 / (2 * (2 * (K : ℝ) + 1)))) :=
    (((tendsto_const_nhds.sub (P.finite_sums_tendsto (Ico K J)).2).max
      tendsto_const_nhds).pow 2).div_const _
  have hbnd := fun n => P.prefixReciprocal_bounds (J := J) hM hRM n
  exact BoundedLimsup.mul_limsup_le_of_tendsto
    (fun n => (by positivity : (0 : ℝ) ≤ 1 / (2 * (M : ℝ) + 4) ^ q).trans (hbnd n).1)
    (fun n => (hbnd n).2) hcredit hF (Eventually.of_forall hpoint)

/-- The original orbit-count limit follows from the stronger cover limit. -/
theorem prefix_limit {K R M J : ℕ}
    (hKJ : K ≤ J) (hRJ : R ≤ J) (hM : 2 ≤ M) (hRM : R < M)
    {lam : ℝ} (hlam : 0 < lam) :
    max (1 - ∑ i ∈ Ico K J, P.v i) 0 ^ 2 /
        (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4) ^ q) ≤
      β * (∑ i ∈ Ico R J, P.h i) / ((M - R : ℕ) : ℝ) + 2 * lam +
        β * N * (bankCost M q : ℝ) * c ^ 2 / (lam * (J + 1)) := by
  have hlo := BoundedLimsup.le_limsup
    (fun n => (P.prefixReciprocal_bounds (J := J) hM hRM n).2)
    (Eventually.of_forall fun n => (P.prefixReciprocal_bounds (J := J) hM hRM n).1)
  have h := mul_le_mul_of_nonneg_left hlo (by positivity :
    0 ≤ max (1 - ∑ i ∈ Ico K J, P.v i) 0 ^ 2 / (2 * (2 * (K : ℝ) + 1)))
  have hfinal := h.trans (P.prefix_reciprocal_limit hKJ hRJ hM hRM hlam)
  simpa only [div_mul_eq_div_mul_one_div] using hfinal

end
end SourceCovers.NearFullSequence.JointProfile

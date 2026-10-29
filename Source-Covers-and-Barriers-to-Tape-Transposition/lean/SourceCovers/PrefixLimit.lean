import SourceCovers.JointProfiles
import SourceCovers.PrefixDeficit
import LeanMachine.PrefixError
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
  have hβ : 0 ≤ β := recordCapacity_nonneg (S.geometry 0).capacity
  let G := fun n => S.geometry (P.subsequence n)
  let O := fun n => S.order (P.subsequence n)
  let L := fun n => (G n).inputLength
  let w := fun n => Nat.ceil (lam * (L n : ℝ))
  let a := fun n => max (G n).a0 (Nat.ceil ((c / ((J : ℝ) + 1)) * (L n : ℝ)))
  let H := fun n => ∑ i ∈ Ico R J, S.hops (P.subsequence n) i
  let V := fun n => ∑ i ∈ Ico K J, S.variation (P.subsequence n) i
  let C : ℝ := bankCost M q
  let F := fun n =>
    (2 * C * c + 1) / (G n).d + 2 * ((w n : ℝ) / L n) +
      β * ((J : ℝ) + q) / L n + β * H n / ((M - R : ℕ) : ℝ) +
      β * C * c * ((1 / (L n : ℝ) + (N : ℝ) * ((a n : ℝ) / L n)) /
        ((w n : ℝ) / L n))
  let credit := fun n => max (1 - V n) 0 ^ 2 /
    (2 * (2 * (K : ℝ) + 1))
  have hc : 0 ≤ c := by simpa using P.hop_mass.2.1 ∅
  have hθ : 0 ≤ c / (J + 1 : ℝ) := div_nonneg hc (by positivity)
  have hw : ∀ n, 0 < w n := fun n =>
    Nat.ceil_pos.mpr (mul_pos hlam (by exact_mod_cast (G n).inputLength_pos))
  have hpoint : ∀ n, credit n * P.prefixReciprocal J R M hM n ≤ (G n).relativeDeficit + F n := by
    intro n
    have ha0 : (G n).a0 ≤ a n := le_max_left _ _
    have ha : c * (G n).inputLength / (J + 1) ≤ (a n : ℝ) := by
      calc
        _ = (c / ((J : ℝ) + 1)) * (L n : ℝ) := by dsimp [L]; ring
        _ ≤ (Nat.ceil ((c / ((J : ℝ) + 1)) * (L n : ℝ)) : ℝ) := Nat.le_ceil _
        _ ≤ _ := Nat.cast_le.mpr (le_max_right _ _)
    have hp := (G n).prefix_reciprocal_deficit (O n) hKJ hRJ hM hRM (hw n) ha0 ha
    have he := PrefixError.finite_error_le (H := H n) (J := J) (q := q)
      (M := M) (R := R) (N := N) (a := a n)
      (G n).hd (G n).hb (hw n) hβ (Nat.cast_nonneg (bankCost M q)) (G n).runtime
    change (G n).relativeDeficit ≥ credit n * P.prefixReciprocal J R M hM n - _ at hp
    simp only [F, L, C, H, NearFullSequence.hops,
      AdmissibleGeometry.inputLength, Nat.cast_mul] at hp he ⊢
    linarith only [hp, he]
  have hsub := P.strictMono.tendsto_atTop
  have hL : Tendsto L atTop atTop := S.inputLength_tendsto.comp hsub
  have hd : Tendsto (fun n => (G n).d) atTop atTop := S.dimension_tendsto.comp hsub
  have ha0 : Tendsto (fun n => ((G n).a0 : ℝ) / L n) atTop (𝓝 0) :=
    S.outside_tendsto.comp hsub
  have hΔ : Tendsto (fun n => (G n).relativeDeficit) atTop (𝓝 0) :=
    S.deficit_tendsto.comp hsub
  have hwidth : Tendsto (fun n => (w n : ℝ) / L n) atTop (𝓝 lam) :=
    PrefixError.ceil_scaled_tendsto hL hlam.le
  have hsize : Tendsto (fun n => (a n : ℝ) / L n) atTop (𝓝 (c / (J + 1))) := by
    simpa only [a, Nat.cast_max] using PrefixError.max_ceil_scaled_tendsto hL ha0 hθ
  have hH : Tendsto H atTop (𝓝 (∑ i ∈ Ico R J, P.h i)) :=
    (P.finite_sums_tendsto (Ico R J)).1
  have hV : Tendsto V atTop (𝓝 (∑ i ∈ Ico K J, P.v i)) :=
    (P.finite_sums_tendsto (Ico K J)).2
  have hinvL : Tendsto (fun n => 1 / (L n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hL
  have hmove : Tendsto (fun n => (2 * C * c + 1) / (G n).d) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat _).comp hd
  have houter : Tendsto (fun n => β * ((J : ℝ) + q) / (L n : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat _).comp hL
  have hres : Tendsto
      (fun n => β * C * c *
        ((1 / (L n : ℝ) + (N : ℝ) * ((a n : ℝ) / L n)) / ((w n : ℝ) / L n)))
      atTop (𝓝 (β * N * C * c ^ 2 / (lam * (J + 1)))) := by
    convert ((hinvL.add (hsize.const_mul (N : ℝ))).div hwidth hlam.ne').const_mul
      (β * C * c) using 1
    congr 1
    field_simp
    ring
  have hF : Tendsto F atTop
      (𝓝 (β * (∑ i ∈ Ico R J, P.h i) / ((M - R : ℕ) : ℝ) + 2 * lam +
        β * N * C * c ^ 2 / (lam * (J + 1)))) := by
    convert (((hmove.add (hwidth.const_mul 2)).add houter).add
      ((hH.const_mul β).div_const ((M - R : ℕ) : ℝ))).add hres using 1
    congr 1
    ring
  have hcredit : Tendsto credit atTop
      (𝓝 (max (1 - ∑ i ∈ Ico K J, P.v i) 0 ^ 2 /
        (2 * (2 * (K : ℝ) + 1)))) :=
    (((tendsto_const_nhds.sub hV).max tendsto_const_nhds).pow 2).div_const _
  have hbnd := fun n => P.prefixReciprocal_bounds (J := J) hM hRM n
  simpa only [zero_add] using
    BoundedLimsup.mul_limsup_le_of_tendsto
      (fun n => (by positivity : (0 : ℝ) ≤ 1 / (2 * (M : ℝ) + 4) ^ q).trans (hbnd n).1)
      (fun n => (hbnd n).2) hcredit (hΔ.add hF) (Eventually.of_forall hpoint)

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

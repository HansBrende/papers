import SourceCovers.PrefixMovement
import LeanMachine.TailLiminf

set_option autoImplicit false

/-! The complete older-observable movement obstruction. Dimension lower
limits are taken before prefix lower limits; both use the same joint-profile
subsequence. The final radius lower limit is extended nonnegative. -/

namespace SourceCovers.NearFullSequence.JointProfile

open Classical Finset Filter LeanMachine
open scoped BigOperators Topology
noncomputable section

variable {c β : ℝ} {N : ℕ} {S : NearFullSequence c β N 2} (P : S.JointProfile)

def prefixMovement (J R M : ℕ) (hM : 2 ≤ M) (φ : ℝ → ℝ) (n : ℕ) : ℝ :=
  (S.geometry (P.subsequence n)).prefixMeanMovement (S.order (P.subsequence n)) J R M hM φ

/-- The inner dimension limit precedes the outer prefix limit. -/
def movementLimit (R M : ℕ) (hM : 2 ≤ M) (φ : ℝ → ℝ) : ℝ :=
  liminf (fun J => liminf (P.prefixMovement J R M hM φ) atTop) atTop

theorem movementLimit_bounds {R M : ℕ} {hM : 2 ≤ M} {φ : ℝ → ℝ} {B : ℝ}
    (hbnd : ∀ J n, 0 ≤ P.prefixMovement J R M hM φ n ∧
      P.prefixMovement J R M hM φ n ≤ B) :
    0 ≤ P.movementLimit R M hM φ ∧ P.movementLimit R M hM φ ≤ B :=
  BoundedLiminf.bounds (fun J => BoundedLiminf.bounds (hbnd J))

/-- Any bounded mean loss dominating the sharper quadratic loss satisfies
this finite-prefix limit. The bound is proved below for the actual movement. -/
theorem prefix_movement_limit {K R M J : ℕ}
    (hKJ : K ≤ J) (hRJ : R ≤ J) (hM : 2 ≤ M) (hRM : R < M)
    {φ : ℝ → ℝ} {B : ℝ}
    (hφ : ∀ z ≥ 0, AnchoredGapErosion.penalty (min z 1) ≤ φ z)
    (hbnd : ∀ n, 0 ≤ P.prefixMovement J R M hM φ n ∧
      P.prefixMovement J R M hM φ n ≤ B)
    {lam : ℝ} (hlam : 0 < lam) :
    max (1 - ∑ i ∈ Ico K J, P.v i) 0 ^ 2 /
        (4 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4)) -
      (β * (∑ i ∈ Ico R J, P.h i) / ((M - R : ℕ) : ℝ) + 2 * lam +
        β * N * (bankCost M 2 : ℝ) * c ^ 2 / (lam * (J + 1))) ≤
      liminf (P.prefixMovement J R M hM φ) atTop := by
  obtain ⟨w, a, F, hdata, hF⟩ := P.prefix_error_limit J R M hlam
  let credit := fun n => max (1 - ∑ i ∈ Ico K J, S.variation (P.subsequence n) i) 0 ^ 2 /
    (4 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4))
  have hcredit : Tendsto credit atTop
      (𝓝 (max (1 - ∑ i ∈ Ico K J, P.v i) 0 ^ 2 /
        (4 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4)))) :=
    (((tendsto_const_nhds.sub (P.finite_sums_tendsto (Ico K J)).2).max
      tendsto_const_nhds).pow 2).div_const _
  apply BoundedLiminf.le_of_tendsto hbnd (hcredit.sub hF)
  apply Eventually.of_forall
  intro n
  obtain ⟨hw, ha0, ha, he⟩ := hdata n
  have h := (S.geometry (P.subsequence n)).prefix_movement_deficit
    (S.order (P.subsequence n)) hKJ hRJ hM hRM hw ha0 ha
  have hm := (S.geometry (P.subsequence n)).prefixMeanMovement_mono
    (S.order (P.subsequence n)) J R M hM hφ
  change credit n - _ ≤ _ at h
  change _ ≤ P.prefixMovement J R M hM φ n at hm
  linarith only [h, hm, he]

/-- Independent cutoffs and any legal fixed modulus. No strictly positive
variation credit is needed to take either lower limit. -/
theorem movementLimit_lower {K R M : ℕ} (hM : 2 ≤ M) (hRM : R < M)
    {φ : ℝ → ℝ} {B : ℝ}
    (hφ : ∀ z ≥ 0, AnchoredGapErosion.penalty (min z 1) ≤ φ z)
    (hbnd : ∀ J n, 0 ≤ P.prefixMovement J R M hM φ n ∧
      P.prefixMovement J R M hM φ n ≤ B) :
    max (1 - P.variationTail K) 0 ^ 2 /
        (4 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4)) -
      β * P.hopTail R / ((M - R : ℕ) : ℝ) ≤ P.movementLimit R M hM φ := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let C : ℝ := β * N * (bankCost M 2 : ℝ) * c ^ 2
  have herror : Tendsto (fun J : ℕ => C / ((δ / 2) * (J + 1 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, div_div] using
      (tendsto_const_div_atTop_nhds_zero_nat (C / (δ / 2))).comp (tendsto_add_atTop_nat 1)
  have hcredit := ((((tendsto_const_nhds (x := (1 : ℝ))).sub
    (P.finite_tails_tendsto K).2).max (tendsto_const_nhds (x := (0 : ℝ)))).pow 2).div_const
      (4 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4))
  have hcost := ((((P.finite_tails_tendsto R).1.const_mul β).div_const
    ((M - R : ℕ) : ℝ)).add_const (2 * (δ / 2))).add herror
  have h := BoundedLiminf.le_of_tendsto (fun J => BoundedLiminf.bounds (hbnd J))
    (hcredit.sub hcost) (eventually_atTop.2 ⟨max K R, fun J hJ =>
      P.prefix_movement_limit ((le_max_left K R).trans hJ) ((le_max_right K R).trans hJ)
        hM hRM hφ (hbnd J) (by positivity : 0 < δ / 2)⟩)
  change _ ≤ P.movementLimit R M hM φ at h
  linarith

/-- Stronger form of Corollary 4.8: the average clipped quadratic penalty
must already pay this much, not just the average linear movement. -/
theorem necessary_movement_penalty {K R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) :
    max (1 - P.variationTail K) 0 ^ 2 /
        (4 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4)) -
      β * P.hopTail R / ((M - R : ℕ) : ℝ) ≤
      P.movementLimit R M hM (fun z => AnchoredGapErosion.penalty (min z 1)) :=
  P.movementLimit_lower hM hRM (fun _ _ => le_rfl) (fun J n =>
    (S.geometry (P.subsequence n)).prefixMeanPenalty_bounds
      (S.order (P.subsequence n)) (J := J) hM hRM)

/-- The unpenalized mean is uniformly bounded for each fixed modulus. -/
theorem completeMovement_bounds {R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) :
    0 ≤ P.movementLimit R M hM id ∧
      P.movementLimit R M hM id ≤ (bankCost M 1 : ℝ) * c :=
  P.movementLimit_bounds (fun J n =>
    (S.geometry (P.subsequence n)).prefixMeanMovement_bounds
      (S.order (P.subsequence n)) (J := J) hM hRM)

/-- Comparing the actual means before both limits recovers the linear loss
from the sharper quadratic loss, with all boundedness proved. -/
theorem movementPenalty_le_complete {R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) :
    P.movementLimit R M hM (fun z => AnchoredGapErosion.penalty (min z 1)) ≤
      P.movementLimit R M hM id := by
  have hp := fun J n => (S.geometry (P.subsequence n)).prefixMeanPenalty_bounds
    (S.order (P.subsequence n)) (J := J) hM hRM
  have he := fun J n => (S.geometry (P.subsequence n)).prefixMeanMovement_bounds
    (S.order (P.subsequence n)) (J := J) hM hRM
  have hcmp (J n : ℕ) := (S.geometry (P.subsequence n)).prefixMeanMovement_mono
    (S.order (P.subsequence n)) J R M hM
    (ψ := id) (fun z _ => (AnchoredGapErosion.penalty_le_self _).trans (min_le_left z 1))
  exact BoundedLiminf.mono (fun J => (BoundedLiminf.bounds (hp J)).1)
    (fun J => (BoundedLiminf.bounds (he J)).2)
    (Eventually.of_forall fun J => BoundedLiminf.mono
      (fun n => (hp J n).1) (fun n => (he J n).2) (Eventually.of_forall (hcmp J)))

/-- The original linear loss is a specialization of the same stronger
finite loss. Its bounds are derived from the complete older bank. -/
theorem necessary_complete_movement {K R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) :
    max (1 - P.variationTail K) 0 ^ 2 /
        (4 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4)) -
      β * P.hopTail R / ((M - R : ℕ) : ℝ) ≤ P.movementLimit R M hM id :=
  (P.necessary_movement_penalty hM hRM).trans (P.movementPenalty_le_complete hM hRM)

/-- The paper's modulus, for all natural `K,R`, including zero and `R < K`. -/
theorem necessary_complete_movement_default (K R : ℕ) :
    max (1 - P.variationTail K) 0 ^ 2 / (16 * (2 * (K : ℝ) + 1) * (R + 2 : ℝ)) -
      β * P.hopTail R / (R + 2 : ℝ) ≤ P.movementLimit R (2 * R + 2) (by omega) id := by
  have h := P.necessary_complete_movement (K := K) (R := R) (M := 2 * R + 2)
    (by omega) (by omega)
  rw [show 2 * R + 2 - R = R + 2 by omega] at h
  convert h using 1
  push_cast
  congr 2
  ring

/-- The final radius limit is in `ℝ≥0∞`, so divergence to infinity is allowed.
The positive-part form also covers `V_K ≥ 1`. -/
theorem scaled_complete_movement_liminf (K : ℕ) :
    ENNReal.ofReal (max (1 - P.variationTail K) 0 ^ 2 / (16 * (2 * (K : ℝ) + 1))) ≤
      liminf (fun R : ℕ => ENNReal.ofReal ((R + 2 : ℝ) *
        P.movementLimit R (2 * R + 2) (by omega) id)) atTop := by
  let C := max (1 - P.variationTail K) 0 ^ 2 / (16 * (2 * (K : ℝ) + 1))
  have hscaled (R : ℕ) : C - β * P.hopTail R ≤
      (R + 2 : ℝ) * P.movementLimit R (2 * R + 2) (by omega) id := by
    have h := mul_le_mul_of_nonneg_left (P.necessary_complete_movement_default K R)
      (by positivity : (0 : ℝ) ≤ R + 2)
    convert h using 1
    dsimp [C]
    field_simp
  have hconv : Tendsto (fun R => C - β * P.hopTail R) atTop (𝓝 C) := by
    simpa only [mul_zero, sub_zero] using
      tendsto_const_nhds.sub (P.tails_tendsto_zero.1.const_mul β)
  have h := liminf_le_liminf (f := atTop) (Eventually.of_forall fun R => ENNReal.ofReal_le_ofReal (hscaled R))
  rwa [(ENNReal.tendsto_ofReal hconv).liminf_eq] at h

end
end SourceCovers.NearFullSequence.JointProfile

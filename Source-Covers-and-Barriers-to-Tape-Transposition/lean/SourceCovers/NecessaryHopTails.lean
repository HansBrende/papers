import SourceCovers.NecessaryCover
import LeanMachine.TailMoments

set_option autoImplicit false

/-!
# Necessary tails from actual finite source certificates

Every cutoff is fixed before the dimension limit. Only the resulting
numerical profile is used when the cutoff then tends to infinity.
-/

namespace SourceCovers.NearFullSequence.JointProfile

open Classical Finset Filter LeanMachine
open scoped BigOperators Topology
noncomputable section

variable {c β : ℝ} {N q : ℕ} {S : NearFullSequence c β N q}
variable (P : S.JointProfile)

/-- The actual finite certificates force this bound on every joint profile.
The variation cutoff `K` and protected-hop cutoff `R` are independent. -/
theorem necessary_hop_tail {K R M : ℕ}
    (hM : 2 ≤ M) (hRM : R < M) :
    max (1 - P.variationTail K) 0 ^ 2 /
      (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4) ^ q) ≤
        β * P.hopTail R / ((M - R : ℕ) : ℝ) := by
  have hlo := (P.reciprocalCoverLimit_bounds hM hRM).1
  have h := mul_le_mul_of_nonneg_left hlo (by positivity :
    0 ≤ max (1 - P.variationTail K) 0 ^ 2 / (2 * (2 * (K : ℝ) + 1)))
  have hfinal := h.trans (P.weighted_reciprocal_cover (K := K) hM hRM)
  simpa only [div_mul_eq_div_mul_one_div] using hfinal

/-- Choosing `M = 2R+2` gives an explicit floor for every natural cutoff,
including zero; no comparison with `K` or sign premise on `1-V_K` is needed. -/
theorem tail_floor {K R : ℕ} (hβ : 0 < β) (hq : 1 ≤ q) :
    max (1 - P.variationTail K) 0 ^ 2 /
      (2 * β * 4 ^ q * (2 * (K : ℝ) + 1) * ((R : ℝ) + 2) ^ (q - 1)) ≤
        P.hopTail R := by
  have hbound := P.necessary_hop_tail (K := K) (R := R) (M := 2 * R + 2)
    (by omega) (by omega)
  have hR : 0 < (R : ℝ) + 2 := by positivity
  have hK : 0 < 2 * (K : ℝ) + 1 := by positivity
  have he : 2 * R + 2 - R = R + 2 := by omega
  have hbase : 2 * ((2 * R + 2 : ℕ) : ℝ) + 4 = 4 * ((R : ℝ) + 2) := by
    push_cast
    ring
  have hpow : ((R : ℝ) + 2) ^ q = ((R : ℝ) + 2) ^ (q - 1) * ((R : ℝ) + 2) := by
    conv_lhs => rw [← Nat.sub_add_cancel hq]
    rw [pow_succ]
  rw [he, hbase, Nat.cast_add, Nat.cast_ofNat, mul_pow, hpow] at hbound
  apply (div_le_iff₀ (by positivity)).mpr
  have h := (div_le_iff₀ (by positivity)).mp hbound
  convert h using 1
  field_simp

/-- Every joint profile has one positive floor valid at all scaled tails. -/
theorem exists_scaled_tail_floor (hβ : 0 < β) (hq : 1 ≤ q) :
    ∃ A > (0 : ℝ), ∀ R : ℕ, A ≤ (R + 2 : ℝ) ^ (q - 1) * P.hopTail R := by
  obtain ⟨K, hK⟩ := ((P.tails_tendsto_zero).2.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists
  let A := max (1 - P.variationTail K) 0 ^ 2 /
    (2 * β * 4 ^ q * (2 * (K : ℝ) + 1))
  have hpos : 0 < max (1 - P.variationTail K) 0 :=
    (sub_pos.mpr hK).trans_le (le_max_left _ _)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro R
  have hf : A / ((R : ℝ) + 2) ^ (q - 1) ≤ P.hopTail R := by
    simpa only [A, div_div] using P.tail_floor (K := K) (R := R) hβ hq
  have h := (div_le_iff₀ (by positivity : 0 < ((R : ℝ) + 2) ^ (q - 1))).mp hf
  simpa only [mul_comm] using h

/-- Polynomial tail floors contradict a finite critical moment. The case
`q=1` already contradicts the independently proved summability of `P.h`. -/
theorem not_summable_moment (hβ : 0 < β) (hq : 1 ≤ q) :
    ¬ Summable (fun i : ℕ => (i + 1 : ℝ) ^ (q - 1) * P.h i) := by
  obtain ⟨A, hA, hfloor⟩ := P.exists_scaled_tail_floor hβ hq
  exact TailMoments.not_summable_moment_of_tail_floor (q - 1) 2 (by norm_num)
    P.hop_mass.1 hA (Eventually.of_forall hfloor)

/-- The nonnegative critical moment diverges to positive infinity, in the
literal partial-sum sense used by the manuscript. -/
theorem moment_partial_sums_tendsto_atTop (hβ : 0 < β) (hq : 1 ≤ q) :
    Tendsto (fun J => ∑ i ∈ range J, (i + 1 : ℝ) ^ (q - 1) * P.h i)
      atTop atTop :=
  (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun i => mul_nonneg (by positivity) (P.hop_mass.1 i))).mp
      (P.not_summable_moment hβ hq)

end
end SourceCovers.NearFullSequence.JointProfile

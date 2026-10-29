import SourceCovers.UniformSharing
import LeanMachine.ExtendedTradeoff
import LeanMachine.TailMoments

set_option autoImplicit false

/-! Necessary global continuation density. Dimension lower limits precede
prefix lower limits, both allowing infinity on the same joint profile. -/

namespace SourceCovers.NearFullSequence.JointProfile

open Classical Finset Filter LeanMachine
open scoped BigOperators ENNReal Topology
noncomputable section

variable {c β : ℝ} {N : ℕ} {S : NearFullSequence c β N 2} (P : S.JointProfile)

/-- The actual mean maximal-seed count, with its dimension lower limit
taken on the common profile subsequence. No upper bound is imposed. -/
def seedLiminf (J R M : ℕ) (hM : 2 ≤ M) : ℝ≥0∞ :=
  liminf (fun n => ENNReal.ofReal ((S.geometry (P.subsequence n)).prefixMeanSeeds
    (S.order (P.subsequence n)) J R M hM)) atTop

def sharingPrefixCredit (K R J M : ℕ) : ℝ :=
  max (1 - ∑ i ∈ Ico K J, P.v i) 0 ^ 2 /
    (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4)) -
      β * (∑ i ∈ Ico R J, P.h i) / ((M - R : ℕ) : ℝ)

def sharingCredit (K R M : ℕ) : ℝ :=
  max (1 - P.variationTail K) 0 ^ 2 /
    (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4)) -
      β * P.hopTail R / ((M - R : ℕ) : ℝ)

theorem sharingPrefixCredit_tendsto (K R M : ℕ) :
    Tendsto (fun J => P.sharingPrefixCredit K R J M) atTop (𝓝 (P.sharingCredit K R M)) :=
  (((((tendsto_const_nhds (x := (1 : ℝ))).sub (P.finite_tails_tendsto K).2).max
    (tendsto_const_nhds (x := (0 : ℝ)))).pow 2).div_const _).sub
      (((P.finite_tails_tendsto R).1.const_mul β).div_const _)

/-- Divide by the positive finite width coefficient before the dimension
limit. This avoids a second subsequence and any boundedness premise. -/
theorem prefix_seed_liminf_lower_eventually {K R J M : ℕ} {η lam : ℝ}
    (hKJ : K ≤ J) (hRJ : R ≤ J) (hM : 2 ≤ M) (hRM : R < M)
    (hη : ∀ᶠ n in atTop, S.hops (P.subsequence n) J ≤ η) (hlam : 0 < lam) :
    ENNReal.ofReal ((P.sharingPrefixCredit K R J M - 2 * lam -
        β * N * (bankCost M 2 : ℝ) * c * η / lam) /
      (lam * ((2 * (M : ℝ) + 3) * (2 * (M : ℝ) + 4)))) ≤ P.seedLiminf J R M hM := by
  obtain ⟨n₀, hηn₀⟩ := hη.exists
  have hη0 : 0 ≤ η :=
    ((S.order (P.subsequence n₀)).hopProfile_nonneg _ J).trans hηn₀
  obtain ⟨w, a, F, hdata, _, hwlim, hF⟩ := P.prefix_error_limit_of_rate J R M hη0 hlam
  let B := (2 * (M : ℝ) + 3) * (2 * (M : ℝ) + 4)
  let credit := fun n => max (1 - ∑ i ∈ Ico K J, S.variation (P.subsequence n) i) 0 ^ 2 /
    (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4))
  have hcredit : Tendsto credit atTop
      (𝓝 (max (1 - ∑ i ∈ Ico K J, P.v i) 0 ^ 2 /
        (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4)))) :=
    (((tendsto_const_nhds.sub (P.finite_sums_tendsto (Ico K J)).2).max
      tendsto_const_nhds).pow 2).div_const _
  apply ExtendedTradeoff.ofReal_le_liminf
    (a := fun n => (credit n - ((S.geometry (P.subsequence n)).relativeDeficit + F n)) /
      (((w n : ℝ) / (S.geometry (P.subsequence n)).inputLength) * B))
  · convert (hcredit.sub hF).div (hwlim.mul_const B) (by dsimp [B]; positivity) using 1
    congr 1
    dsimp only [sharingPrefixCredit, B]
    ring
  · apply hη.mono
    intro n hηn
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨hw, ha0, ha, he⟩ := hdata n
    have h := (S.geometry (P.subsequence n)).prefix_sharing_deficit
      (S.order (P.subsequence n)) hKJ hRJ hM hRM hw ha0 hηn ha
    have hpos : 0 < ((w n : ℝ) / (S.geometry (P.subsequence n)).inputLength) * B := by
      have hL : (0 : ℝ) < (S.geometry (P.subsequence n)).inputLength := by
        exact_mod_cast (S.geometry (P.subsequence n)).inputLength_pos
      dsimp [B]
      positivity
    apply (div_le_iff₀ hpos).mpr
    change credit n ≤ _ at h
    dsimp only [B]
    nlinarith only [h, he]

/-- Only a bound on the limiting omitted coordinate is needed. Any positive
slack is eventually valid in dimension, and continuity removes that slack. -/
theorem prefix_seed_liminf_lower {K R J M : ℕ} {η lam : ℝ}
    (hKJ : K ≤ J) (hRJ : R ≤ J) (hM : 2 ≤ M) (hRM : R < M)
    (hη : P.h J ≤ η) (hlam : 0 < lam) :
    ENNReal.ofReal ((P.sharingPrefixCredit K R J M - 2 * lam -
        β * N * (bankCost M 2 : ℝ) * c * η / lam) /
      (lam * ((2 * (M : ℝ) + 3) * (2 * (M : ℝ) + 4)))) ≤ P.seedLiminf J R M hM := by
  have hηlim : Tendsto (fun n : ℕ => η + 1 / (n + 1 : ℝ)) atTop (𝓝 η) := by
    simpa only [add_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add η
  have hlim := ENNReal.tendsto_ofReal
    (((tendsto_const_nhds (x := P.sharingPrefixCredit K R J M - 2 * lam)).sub
      ((hηlim.const_mul (β * N * (bankCost M 2 : ℝ) * c)).div_const lam)).div_const
      (lam * ((2 * (M : ℝ) + 3) * (2 * (M : ℝ) + 4))))
  apply le_of_tendsto' hlim
  intro n
  apply P.prefix_seed_liminf_lower_eventually hKJ hRJ hM hRM ?_ hlam
  exact ((P.hops_tendsto J).eventually (Iio_mem_nhds
    (hη.trans_lt (lt_add_of_pos_right η (by positivity : 0 < 1 / (n + 1 : ℝ)))))).mono
      fun _ h => h.le

/-- General density bound: arbitrary legal modulus, independent cutoffs,
positive-part credit, and only a bound on the limiting hop profile. -/
theorem necessary_sharing_density {K R M : ℕ} {η : ℕ → ℝ}
    (hM : 2 ≤ M) (hRM : R < M)
    (hcost : 0 < β * N * (bankCost M 2 : ℝ) * c)
    (hη : Tendsto η atTop (𝓝 0)) (hηpos : ∀ J, 0 < η J)
    (hbound : ∀ᶠ J in atTop, P.h J ≤ η J) :
    ENNReal.ofReal (max (P.sharingCredit K R M) 0 ^ 2 /
      (4 * (β * N * (bankCost M 2 : ℝ) * c) *
        ((2 * (M : ℝ) + 3) * (2 * (M : ℝ) + 4)))) ≤
      liminf (fun J => ENNReal.ofReal (η J) * P.seedLiminf J R M hM) atTop := by
  apply ExtendedTradeoff.density_liminf (P.sharingPrefixCredit_tendsto K R M) hη
    (by norm_num : (0 : ℝ) < 2) (by positivity) hcost hηpos
  filter_upwards [eventually_ge_atTop (max K R), hbound] with J hJ hηJ
  intro lam hlam
  exact P.prefix_seed_liminf_lower ((le_max_left K R).trans hJ)
    ((le_max_right K R).trans hJ) hM hRM hηJ hlam

/-- The manuscript's credit, with a positive part also covering `V_K ≥ 1`. -/
theorem sharingCredit_default (K R : ℕ) :
    P.sharingCredit K R (2 * R + 2) =
      max (1 - P.variationTail K) 0 ^ 2 / (8 * (2 * (K : ℝ) + 1) * (R + 2 : ℝ)) -
        β * P.hopTail R / (R + 2 : ℝ) := by
  dsimp only [sharingCredit]
  rw [show 2 * R + 2 - R = R + 2 by omega]
  push_cast
  congr 2
  ring

/-- Once the variation tail is below one, the default credit is strictly
positive at every sufficiently large protected scale. -/
theorem sharingCredit_eventually_pos {K : ℕ} (hK : P.variationTail K < 1) :
    ∀ᶠ R in atTop, 0 < P.sharingCredit K R (2 * R + 2) := by
  let A := max (1 - P.variationTail K) 0 ^ 2 / (8 * (2 * (K : ℝ) + 1))
  have hA : 0 < A := by
    have : 0 < max (1 - P.variationTail K) 0 :=
      (sub_pos.mpr hK).trans_le (le_max_left _ _)
    positivity
  have hlim : Tendsto (fun R => β * P.hopTail R) atTop (𝓝 0) := by
    simpa only [mul_zero] using P.tails_tendsto_zero.1.const_mul β
  apply (hlim.eventually (Iio_mem_nhds hA)).mono
  intro R hR
  rw [P.sharingCredit_default]
  have he : max (1 - P.variationTail K) 0 ^ 2 /
      (8 * (2 * (K : ℝ) + 1) * (R + 2 : ℝ)) - β * P.hopTail R / (R + 2 : ℝ) =
        (A - β * P.hopTail R) / (R + 2 : ℝ) := by dsimp [A]; field_simp
  rw [he]
  exact div_pos (sub_pos.mpr hR) (by positivity)

/-- The positive parameter convention in the manuscript implies a positive
cost coefficient at every modulus. -/
theorem sharingCost_pos (hc : 0 < c) (hβ : 0 < β) (hN : 0 < N) (M : ℕ) :
    0 < β * N * (bankCost M 2 : ℝ) * c := by
  have hbank : 0 < bankCost M 2 := by dsimp [bankCost, coreCost]; positivity
  exact mul_pos (mul_pos (mul_pos hβ (by exact_mod_cast hN))
    (by exact_mod_cast hbank)) hc

/-- At a zero omitted-profile coordinate, any positive finite-prefix
credit forces infinitely many mean seeds in the dimension lower limit. -/
theorem seedLiminf_eq_top_of_zero {K R J M : ℕ}
    (hKJ : K ≤ J) (hRJ : R ≤ J) (hM : 2 ≤ M) (hRM : R < M)
    (hzero : P.h J = 0) (hcredit : 0 < P.sharingPrefixCredit K R J M) :
    P.seedLiminf J R M hM = ⊤ := by
  apply ExtendedTradeoff.eq_top_of_zero_cost hcredit (by norm_num : (0 : ℝ) < 2)
    (by positivity : 0 < (2 * (M : ℝ) + 3) * (2 * (M : ℝ) + 4))
  intro lam hlam
  simpa only [mul_zero, zero_div, sub_zero] using P.prefix_seed_liminf_lower
    hKJ hRJ hM hRM (by simp only [hzero, le_refl] : P.h J ≤ 0) hlam

/-- Normalize any positive diverging denominator, retaining an explicit
growth floor and allowing infinite inner lower limits. -/
theorem necessary_seed_growth {K R M : ℕ} {d : ℕ → ℝ} {H : ℝ}
    (hM : 2 ≤ M) (hRM : R < M)
    (hcost : 0 < β * N * (bankCost M 2 : ℝ) * c)
    (hH : 0 < H) (hd : ∀ J, 0 < d J) (hdlim : Tendsto d atTop atTop)
    (hbound : ∀ᶠ J in atTop, P.h J ≤ H / d J) :
    ENNReal.ofReal ((max (P.sharingCredit K R M) 0 ^ 2 /
      (4 * (β * N * (bankCost M 2 : ℝ) * c) *
        ((2 * (M : ℝ) + 3) * (2 * (M : ℝ) + 4)))) / H) ≤
      liminf (fun J => P.seedLiminf J R M hM / ENNReal.ofReal (d J)) atTop := by
  apply ExtendedTradeoff.normalize_rate hH hd
  apply P.necessary_sharing_density hM hRM hcost ?_ (fun J => div_pos hH (hd J)) hbound
  simpa only [div_eq_mul_inv, Pi.inv_apply, mul_zero] using
    hdlim.inv_tendsto_atTop.const_mul H

/-- Power growth is forced for every positive real exponent whose rate
bounds the limiting profile; no finite-dimensional envelope is needed. -/
theorem necessary_power_seed_growth {K R M : ℕ} {H p : ℝ}
    (hM : 2 ≤ M) (hRM : R < M)
    (hcost : 0 < β * N * (bankCost M 2 : ℝ) * c) (hH : 0 < H) (hp : 0 < p)
    (hbound : ∀ᶠ J in atTop, P.h J ≤ H / (J + 1 : ℝ) ^ p) :
    ENNReal.ofReal ((max (P.sharingCredit K R M) 0 ^ 2 /
      (4 * (β * N * (bankCost M 2 : ℝ) * c) *
        ((2 * (M : ℝ) + 3) * (2 * (M : ℝ) + 4)))) / H) ≤
      liminf (fun J => P.seedLiminf J R M hM / ENNReal.ofReal ((J + 1 : ℝ) ^ p)) atTop := by
  apply P.necessary_seed_growth hM hRM hcost hH (fun J => by positivity) ?_ hbound
  exact (tendsto_rpow_atTop hp).comp (by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))

/-- Sorted summability improves the no-envelope conclusion from a positive
linear growth floor to divergence after division by rank. -/
theorem necessary_superlinear_seed_growth {K R M : ℕ}
    (hM : 2 ≤ M) (hRM : R < M)
    (hcost : 0 < β * N * (bankCost M 2 : ℝ) * c)
    (hcredit : 0 < P.sharingCredit K R M) :
    Tendsto (fun J => P.seedLiminf J R M hM / ENNReal.ofReal (J + 1 : ℝ))
      atTop (𝓝 ⊤) := by
  apply tendsto_of_le_liminf_of_limsup_le ?_ le_top
  apply le_of_eq
  symm
  apply ExtendedTradeoff.eq_top_of_div_le
    (Q := max (P.sharingCredit K R M) 0 ^ 2 /
      (4 * (β * N * (bankCost M 2 : ℝ) * c) *
        ((2 * (M : ℝ) + 3) * (2 * (M : ℝ) + 4))))
    (by have := hcredit.trans_le (le_max_left (P.sharingCredit K R M) 0); positivity)
  intro H hH
  apply P.necessary_seed_growth hM hRM hcost hH (fun J => by positivity)
    (by simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  have hlim := TailMoments.rank_mul_tendsto_zero
    P.hop_mass.1 P.hop_antitone P.hop_mass.2.2.1
  apply (hlim.eventually (Iio_mem_nhds hH)).mono
  intro J hJ
  exact (le_div_iff₀ (by positivity : 0 < (J + 1 : ℝ))).mpr (by simpa [mul_comm] using hJ.le)

end
end SourceCovers.NearFullSequence.JointProfile

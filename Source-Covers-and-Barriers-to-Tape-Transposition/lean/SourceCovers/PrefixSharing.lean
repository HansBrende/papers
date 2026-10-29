import SourceCovers.GlobalSharing
import SourceCovers.PrefixErrorLimit

set_option autoImplicit false

/-! Actual global sharing for original-order prefixes, with an arbitrary
bound on the first omitted family instead of only the total-mass bound. -/

namespace SourceCovers.AdmissibleGeometry

open Classical Finset LeanMachine
open scoped BigOperators
noncomputable section

variable {c β : ℝ} {N : ℕ} (G : AdmissibleGeometry c β N 2) (O : SortedCore G.core)

def prefixMeanSeeds (J R M : ℕ) (hM : 2 ≤ M) : ℝ :=
  𝔼 ρ ∈ admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M,
    (sharedSeedCount (G.core_coloring.mono (O.selectedPrefix_subset J)) hM G.exceptions
      ((range G.inputLength).image G.t) ρ : ℝ)

theorem prefixMeanSeeds_nonneg (J R M : ℕ) (hM : 2 ≤ M) :
    0 ≤ G.prefixMeanSeeds O J R M hM :=
  expect_nonneg fun _ _ => Nat.cast_nonneg _

/-- The full paid finite sharing bound for actual original-order prefixes.
Neither low sharing nor a size envelope is assumed in the certificate itself. -/
theorem prefix_sharing_deficit {K R J M w a : ℕ} {η : ℝ}
    (hKJ : K ≤ J) (hRJ : R ≤ J) (hM : 2 ≤ M) (hRM : R < M) (hw : 0 < w)
    (ha0 : G.a0 ≤ a) (hη : O.hopProfile G.inputLength J ≤ η)
    (ha : η * G.inputLength ≤ (a : ℝ)) :
    max (1 - ∑ i ∈ Ico K J, O.variationProfile G.x G.inputLength i) 0 ^ 2 /
        (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4)) ≤
      G.relativeDeficit + G.prefixError O J R M w a +
        ((w : ℝ) / G.inputLength) * ((2 * (M : ℝ) + 3) * (2 * (M : ℝ) + 4)) *
          G.prefixMeanSeeds O J R M hM := by
  have hV := G.prefix_variation_le O hKJ
  have hτ := G.prefix_nonleaf_mass_le O hRJ
  have h := shared_support_count_deficit (J := J) (G.core_coloring.mono (O.selectedPrefix_subset J))
    hM G.exceptions (O.subprefix J R) (O.subprefix J K)
    (by rw [O.selectedPrefix_card]; exact min_le_left _ _) G.exceptions_card
    (O.subprefix_card_le J R) hRM (O.subprefix_card_le J K)
    G.work_walk G.full_coloring (G.prefix_outside_small_of_rate O ha0 hη ha)
    G.x G.t G.hd G.hb hw G.append_strict G.append_lt G.raw_range G.raw_step
    G.C G.correct_nonempty G.record G.output G.capacity G.locally_determined G.correct
    (by simpa only [inputLength, Nat.cast_mul] using hV) hτ
  simp only [relativeDeficit, deficit, prefixError, prefixMeanSeeds,
    expect_eq_sum_div_card, inputLength, Nat.cast_mul, Nat.cast_ofNat] at h ⊢
  simp only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] at h ⊢
  linarith only [h]

end
end SourceCovers.AdmissibleGeometry

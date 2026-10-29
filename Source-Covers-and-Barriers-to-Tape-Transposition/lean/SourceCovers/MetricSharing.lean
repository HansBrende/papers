import SourceCovers.UniformSharing
import LeanMachine.RawIntervalCover

set_option autoImplicit false

/-! Metric covers of the actual shared raw support. Minimum covers are
paid at every shift, preserving the complete residual-recovery bill. -/

namespace SourceCovers

/- Re-export the shared definitions and payment lemmas without copying proofs. -/
namespace RawIntervalCover
export LeanMachine.RawIntervalCover (number exists_min_cover blockUnion_card_le two_block_factor_sharp)
end RawIntervalCover

open Classical Finset Filter LeanMachine
open scoped BigOperators Topology
noncomputable section

namespace AdmissibleGeometry

variable {c β : ℝ} {N : ℕ} (G : AdmissibleGeometry c β N 2) (O : SortedCore G.core)

/-- The phase mean of the actual minimum raw-interval covering number. -/
def prefixMeanRawCover (J R M : ℕ) (hM : 2 ≤ M) (δ : ℝ) : ℝ :=
  𝔼 ρ ∈ admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M,
    (RawIntervalCover.number
      (sharedRawSupport (G.core_coloring.mono (O.selectedPrefix_subset J)) hM
        G.exceptions G.x ((range G.inputLength).image G.t) ρ) (δ * G.inputLength) : ℝ)

theorem prefixMeanRawCover_nonneg (J R M : ℕ) (hM : 2 ≤ M) (δ : ℝ) :
    0 ≤ G.prefixMeanRawCover O J R M hM δ := expect_nonneg fun _ _ => Nat.cast_nonneg _

/-- A two-block payment per covering interval, at any legal modulus and
independent cutoffs. The full original two-exception error is retained. -/
theorem prefix_metric_deficit {K R J M w a : ℕ} {η δ : ℝ}
    (hKJ : K ≤ J) (hRJ : R ≤ J) (hM : 2 ≤ M) (hRM : R < M) (hw : 0 < w)
    (hδ : 0 ≤ δ) (hwidth : δ * G.inputLength ≤ (w : ℝ))
    (ha0 : G.a0 ≤ a) (hη : O.hopProfile G.inputLength J ≤ η)
    (ha : η * G.inputLength ≤ (a : ℝ)) :
    max (1 - ∑ i ∈ Ico K J, O.variationProfile G.x G.inputLength i) 0 ^ 2 /
        (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4)) ≤
      G.relativeDeficit + G.prefixError O J R M w a +
        2 * ((w : ℝ) / G.inputLength) * G.prefixMeanRawCover O J R M hM δ := by
  have hV := G.prefix_variation_le O hKJ
  have hτ := G.prefix_nonleaf_mass_le O hRJ
  have h := shared_support_paid_deficit_of_payment (J := J)
    (G.core_coloring.mono (O.selectedPrefix_subset J)) hM G.exceptions
    (O.subprefix J R) (O.subprefix J K)
    (by rw [O.selectedPrefix_card]; exact min_le_left _ _) G.exceptions_card
    (O.subprefix_card_le J R) hRM (O.subprefix_card_le J K)
    G.work_walk G.full_coloring (G.prefix_outside_small_of_rate O ha0 hη ha)
    G.x G.t G.hd G.hb hw G.append_strict G.append_lt G.raw_range G.raw_step
    G.C G.correct_nonempty G.record G.output G.capacity G.locally_determined G.correct
    (by simpa only [inputLength, Nat.cast_mul] using hV) hτ
    (fun ρ => 2 * (w : ℝ) * RawIntervalCover.number
      (sharedRawSupport (G.core_coloring.mono (O.selectedPrefix_subset J)) hM
        G.exceptions G.x ((range G.inputLength).image G.t) ρ) (δ * G.inputLength))
    (fun ρ _ θ => by
      exact_mod_cast (RawIntervalCover.blockUnion_card_le hw θ _
        (mul_nonneg hδ (Nat.cast_nonneg G.inputLength)) hwidth).trans (min_le_right ..))
  have hcost : (bankCost M 1 : ℝ) ≤ bankCost M 2 := by
    exact_mod_cast bankCost_mono M (by omega : 1 ≤ 2)
  have hmotion := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcost (by norm_num : (0 : ℝ) ≤ 2))
      (Nat.cast_nonneg (G.T - 1)))
    (show (0 : ℝ) ≤ G.d * (G.d * G.d * G.b) by positivity)
  simp only [relativeDeficit, deficit, prefixError, prefixMeanRawCover,
    expect_eq_sum_div_card, inputLength, Nat.cast_mul, Nat.cast_ofNat, ← mul_sum] at h ⊢
  simp only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] at h hmotion ⊢
  linarith only [h, hmotion]

/-- Covers and omitted-family rates refer to the same original order.
All bounds and allowed cutoffs are supplied before dimension. -/
def HasMetricCoverBounds (radii : Set ℕ) (cutoffs : ℕ → Set ℕ)
    (η : ℕ → ℝ) (δ n : ℕ → ℕ → ℝ) : Prop :=
  ∀ R ∈ radii, ∀ J ∈ cutoffs R, R ≤ J →
    0 < δ R J ∧ O.hopProfile G.inputLength J ≤ η J ∧
      G.prefixMeanRawCover O J R (2 * R + 2) (by omega) (δ R J) ≤ n R J

end AdmissibleGeometry

namespace NearFullSequence.JointProfile

variable {c β : ℝ} {N : ℕ} {S : NearFullSequence c β N 2} (P : S.JointProfile)

/-- Dimension first: widths are rounded at the fixed metric radius.
The mean cover number need not converge. -/
theorem prefix_metric_limit {K R J M : ℕ} {η δ n : ℝ}
    (hKJ : K ≤ J) (hRJ : R ≤ J) (hM : 2 ≤ M) (hRM : R < M)
    (hη : ∀ ν, S.hops (P.subsequence ν) J ≤ η)
    (hn : ∀ ν, (S.geometry (P.subsequence ν)).prefixMeanRawCover
      (S.order (P.subsequence ν)) J R M hM δ ≤ n) (hδ : 0 < δ) :
    max (1 - ∑ i ∈ Ico K J, P.v i) 0 ^ 2 /
        (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4)) ≤
      β * (∑ i ∈ Ico R J, P.h i) / ((M - R : ℕ) : ℝ) +
        2 * δ + 2 * δ * n + β * N * (bankCost M 2 : ℝ) * c * η / δ := by
  have hη0 : 0 ≤ η :=
    ((S.order (P.subsequence 0)).hopProfile_nonneg _ J).trans (hη 0)
  obtain ⟨w, a, F, hdata, hwidth, hwlim, hF⟩ := P.prefix_error_limit_of_rate J R M hη0 hδ
  let credit := fun ν => max (1 - ∑ i ∈ Ico K J, S.variation (P.subsequence ν) i) 0 ^ 2 /
    (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4))
  have hcredit : Tendsto credit atTop
      (𝓝 (max (1 - ∑ i ∈ Ico K J, P.v i) 0 ^ 2 /
        (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4)))) :=
    (((tendsto_const_nhds.sub (P.finite_sums_tendsto (Ico K J)).2).max
      tendsto_const_nhds).pow 2).div_const _
  have hlim := le_of_tendsto_of_tendsto' hcredit (hF.add ((hwlim.const_mul 2).mul_const n))
    (fun ν => by
      obtain ⟨hw, ha0, ha, he⟩ := hdata ν
      have h := (S.geometry (P.subsequence ν)).prefix_metric_deficit
        (S.order (P.subsequence ν)) hKJ hRJ hM hRM hw hδ.le (hwidth ν) ha0 (hη ν) ha
      have hcover := mul_le_mul_of_nonneg_left (hn ν)
        (by positivity : 0 ≤ 2 * ((w ν : ℝ) / (S.geometry (P.subsequence ν)).inputLength))
      exact h.trans (add_le_add (add_le_add le_rfl he) hcover))
  convert hlim using 1
  ring

/-- Only simultaneous smallness at arbitrarily late common cutoffs is
needed; convergence on every cutoff and `δ < 1` are unnecessary. -/
theorem metric_tail_lower {K R M : ℕ} {s : Set ℕ} {η δ n : ℕ → ℝ}
    (hM : 2 ≤ M) (hRM : R < M)
    (hsmall : ∀ ε > 0, ∀ J₀ : ℕ, ∃ J ≥ J₀, J ∈ s ∧
      δ J < ε ∧ δ J * n J < ε ∧ η J / δ J < ε)
    (hbound : ∀ J ∈ s, R ≤ J → 0 < δ J ∧ ∀ ν,
      S.hops (P.subsequence ν) J ≤ η J ∧
        (S.geometry (P.subsequence ν)).prefixMeanRawCover
          (S.order (P.subsequence ν)) J R M hM (δ J) ≤ n J) :
    max (1 - P.variationTail K) 0 ^ 2 /
        (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4)) ≤
      β * P.hopTail R / ((M - R : ℕ) : ℝ) := by
  have hβ : 0 ≤ β := recordCapacity_nonneg (S.geometry 0).capacity
  have hc : 0 ≤ c := by simpa using P.hop_mass.2.1 ∅
  let C := β * N * (bankCost M 2 : ℝ) * c
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hden : 0 < 4 + C := by linarith
  have hcredit := ((((tendsto_const_nhds (x := (1 : ℝ))).sub
    (P.finite_tails_tendsto K).2).max (tendsto_const_nhds (x := (0 : ℝ)))).pow 2).div_const
      (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4))
  apply sub_nonpos.mp
  apply le_of_forall_pos_le_add
  intro ε hε
  rw [zero_add]
  apply le_of_tendsto_of_frequently
    (hcredit.sub (((P.finite_tails_tendsto R).1.const_mul β).div_const ((M - R : ℕ) : ℝ)))
  apply frequently_atTop.2
  intro J₀
  obtain ⟨J, hJ, hJs, hδs, hns, hηs⟩ :=
    hsmall (ε / (4 + C)) (div_pos hε hden) (max J₀ (max K R))
  have hKJ := (le_max_left K R).trans ((le_max_right J₀ (max K R)).trans hJ)
  have hRJ := (le_max_right K R).trans ((le_max_right J₀ (max K R)).trans hJ)
  obtain ⟨hδ, hb⟩ := hbound J hJs hRJ
  have h := P.prefix_metric_limit hKJ hRJ hM hRM (fun ν => (hb ν).1) (fun ν => (hb ν).2) hδ
  have he : 2 * δ J + 2 * δ J * n J + C * η J / δ J ≤ ε := by
    calc
      _ = 2 * δ J + 2 * (δ J * n J) + C * (η J / δ J) := by ring
      _ ≤ 2 * (ε / (4 + C)) + 2 * (ε / (4 + C)) + C * (ε / (4 + C)) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hδs.le (by norm_num))
          (mul_le_mul_of_nonneg_left hns.le (by norm_num))) (mul_le_mul_of_nonneg_left hηs.le hC)
      _ = ε := by field_simp; ring
  refine ⟨J, (le_max_left J₀ (max K R)).trans hJ, ?_⟩
  dsimp only [C] at he
  linarith only [h, he]

include P in
theorem false_of_metric_cover_bounds {radii : Set ℕ} {cutoffs : ℕ → Set ℕ}
    {η : ℕ → ℝ} {δ n : ℕ → ℕ → ℝ}
    (hradii : ∀ R₀ : ℕ, ∃ R ≥ R₀, R ∈ radii)
    (hsmall : ∀ R ∈ radii, ∀ ε > 0, ∀ J₀ : ℕ, ∃ J ≥ J₀, J ∈ cutoffs R ∧
      δ R J < ε ∧ δ R J * n R J < ε ∧ η J / δ R J < ε)
    (hbound : ∀ ν, (S.geometry ν).HasMetricCoverBounds (S.order ν) radii cutoffs η δ n) :
    False := by
  apply P.false_of_one_exception_tail_bounds hradii
  intro K R hR
  apply P.metric_tail_lower (K := K) (M := 2 * R + 2) (by omega) (by omega) (hsmall R hR)
  intro J hJ hRJ
  exact ⟨(hbound (P.subsequence 0) R hR J hJ hRJ).1,
    fun ν => (hbound (P.subsequence ν) R hR J hJ hRJ).2⟩

end NearFullSequence.JointProfile

/-- Uniform metric sharing, with all raw-cover data fixed before dimension.
The statement retains the equivalent code-cardinality conclusion. -/
theorem metric_sharing_uniform_deficit {c β : ℝ} {N : ℕ}
    {radii : Set ℕ} {cutoffs : ℕ → Set ℕ} {η : ℕ → ℝ} {δ n : ℕ → ℕ → ℝ}
    (hradii : ∀ R₀ : ℕ, ∃ R ≥ R₀, R ∈ radii)
    (hsmall : ∀ R ∈ radii, ∀ ε > 0, ∀ J₀ : ℕ, ∃ J ≥ J₀, J ∈ cutoffs R ∧
      δ R J < ε ∧ δ R J * n R J < ε ∧ η J / δ R J < ε) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ G : AdmissibleGeometry c β N 2,
      ∀ O : SortedCore G.core, G.HasMetricCoverBounds O radii cutoffs η δ n →
      d₀ ≤ G.d → (G.a0 : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  apply uniform_deficit_of_no_ordered_nearFull
    (fun G O => G.HasMetricCoverBounds O radii cutoffs η δ n)
  intro S hbound
  obtain ⟨P⟩ := S.exists_jointProfile
  exact P.false_of_metric_cover_bounds hradii hsmall hbound

/-- Proposition 5.4 with the manuscript's three joint limits on each common
unbounded set of cutoffs. All three use the same restricted filter. -/
theorem metric_sharing_uniform_deficit_of_limits {c β : ℝ} {N : ℕ}
    {radii : Set ℕ} {cutoffs : ℕ → Set ℕ} {η : ℕ → ℝ} {δ n : ℕ → ℕ → ℝ}
    (hradii : ∀ R₀ : ℕ, ∃ R ≥ R₀, R ∈ radii)
    (hcutoffs : ∀ R ∈ radii, ∀ J₀ : ℕ, ∃ J ≥ J₀, J ∈ cutoffs R)
    (hδ : ∀ R ∈ radii, Tendsto (δ R) (atTop ⊓ 𝓟 (cutoffs R)) (𝓝 0))
    (hn : ∀ R ∈ radii,
      Tendsto (fun J => δ R J * n R J) (atTop ⊓ 𝓟 (cutoffs R)) (𝓝 0))
    (hη : ∀ R ∈ radii,
      Tendsto (fun J => η J / δ R J) (atTop ⊓ 𝓟 (cutoffs R)) (𝓝 0)) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ G : AdmissibleGeometry c β N 2,
      ∀ O : SortedCore G.core, G.HasMetricCoverBounds O radii cutoffs η δ n →
      d₀ ≤ G.d → (G.a0 : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  apply metric_sharing_uniform_deficit hradii
  intro R hR ε hε J₀
  have hev := eventually_inf_principal.mp
    (((hδ R hR).eventually (Iio_mem_nhds hε)).and
      (((hn R hR).eventually (Iio_mem_nhds hε)).and
        ((hη R hR).eventually (Iio_mem_nhds hε))))
  obtain ⟨J₁, hJ₁⟩ := eventually_atTop.mp hev
  obtain ⟨J, hJ, hJs⟩ := hcutoffs R hR (max J₀ J₁)
  exact ⟨J, (le_max_left J₀ J₁).trans hJ, hJs,
    hJ₁ J ((le_max_right J₀ J₁).trans hJ) hJs⟩

end
end SourceCovers

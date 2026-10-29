import SourceCovers.PrefixSharing
import SourceCovers.UniformCover
import LeanMachine.VanishingTradeoff
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

/-! Uniform exclusion by dimension-independent global sharing bounds.
The same original hop order and the same good cutoffs are used throughout. -/

namespace SourceCovers

open Classical Finset Filter LeanMachine
open scoped BigOperators Topology
noncomputable section

namespace AdmissibleGeometry

/-- A dimension-independent sharing budget, required only at the specified
common cutoffs. The first omitted coordinate uses the same original order. -/
def HasSharingBounds {c β : ℝ} {N : ℕ} (G : AdmissibleGeometry c β N 2)
    (O : SortedCore G.core) (radii : Set ℕ) (cutoffs : ℕ → Set ℕ)
    (η : ℕ → ℝ) (g : ℕ → ℕ → ℝ) : Prop :=
  ∀ R ∈ radii, ∀ J ∈ cutoffs R, R ≤ J →
    O.hopProfile G.inputLength J ≤ η J ∧
      G.prefixMeanSeeds O J R (2 * R + 2) (by omega) ≤ g R J

end AdmissibleGeometry

namespace NearFullSequence.JointProfile

variable {c β : ℝ} {N : ℕ} {S : NearFullSequence c β N 2} (P : S.JointProfile)

/-- The dimension limit is taken with the width ratio and all cutoffs fixed.
The mean seed count need not converge: a uniform upper bound suffices. -/
theorem prefix_sharing_limit {K R J M : ℕ} {η g lam : ℝ}
    (hKJ : K ≤ J) (hRJ : R ≤ J) (hM : 2 ≤ M) (hRM : R < M)
    (hη : ∀ n, S.hops (P.subsequence n) J ≤ η)
    (hg : ∀ n, (S.geometry (P.subsequence n)).prefixMeanSeeds
      (S.order (P.subsequence n)) J R M hM ≤ g)
    (hlam : 0 < lam) :
    max (1 - ∑ i ∈ Ico K J, P.v i) 0 ^ 2 /
        (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4)) ≤
      β * (∑ i ∈ Ico R J, P.h i) / ((M - R : ℕ) : ℝ) +
        lam * (2 + ((2 * (M : ℝ) + 3) * (2 * (M : ℝ) + 4)) * g) +
        β * N * (bankCost M 2 : ℝ) * c * η / lam := by
  have hη0 : 0 ≤ η :=
    ((S.order (P.subsequence 0)).hopProfile_nonneg _ J).trans (hη 0)
  obtain ⟨w, a, F, hdata, _, hwlim, hF⟩ := P.prefix_error_limit_of_rate J R M hη0 hlam
  let credit := fun n => max (1 - ∑ i ∈ Ico K J, S.variation (P.subsequence n) i) 0 ^ 2 /
    (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4))
  have hcredit : Tendsto credit atTop
      (𝓝 (max (1 - ∑ i ∈ Ico K J, P.v i) 0 ^ 2 /
        (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4)))) :=
    (((tendsto_const_nhds.sub (P.finite_sums_tendsto (Ico K J)).2).max
      tendsto_const_nhds).pow 2).div_const _
  have hlim := le_of_tendsto_of_tendsto' hcredit
    (hF.add ((hwlim.mul_const ((2 * (M : ℝ) + 3) * (2 * (M : ℝ) + 4))).mul_const g))
    (fun n => by
      obtain ⟨hw, ha0, ha, he⟩ := hdata n
      have h := (S.geometry (P.subsequence n)).prefix_sharing_deficit
        (S.order (P.subsequence n)) hKJ hRJ hM hRM hw ha0 (hη n) ha
      have hshare := mul_le_mul_of_nonneg_left (hg n)
        (by positivity : 0 ≤ ((w n : ℝ) / (S.geometry (P.subsequence n)).inputLength) *
          ((2 * (M : ℝ) + 3) * (2 * (M : ℝ) + 4)))
      exact h.trans (add_le_add (add_le_add le_rfl he) hshare))
  convert hlim using 1
  ring

/-- Arbitrarily late good cutoffs force the same positive variation credit
to be paid by the hop tail. Both cutoffs and the modulus are independent. -/
theorem sharing_tail_lower {K R M : ℕ} {s : Set ℕ} {η g : ℕ → ℝ}
    (hM : 2 ≤ M) (hRM : R < M) (hη : Tendsto η atTop (𝓝 0))
    (hsmall : ∀ ε > 0, ∀ J₀ : ℕ, ∃ J ≥ J₀, J ∈ s ∧ η J * g J < ε)
    (hbound : ∀ J ∈ s, R ≤ J → ∀ n,
      S.hops (P.subsequence n) J ≤ η J ∧
        (S.geometry (P.subsequence n)).prefixMeanSeeds
          (S.order (P.subsequence n)) J R M hM ≤ g J) :
    max (1 - P.variationTail K) 0 ^ 2 /
        (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4)) ≤
      β * P.hopTail R / ((M - R : ℕ) : ℝ) := by
  have hβ : 0 ≤ β := recordCapacity_nonneg (S.geometry 0).capacity
  have hc : 0 ≤ c := by simpa using P.hop_mass.2.1 ∅
  have hcredit := ((((tendsto_const_nhds (x := (1 : ℝ))).sub
    (P.finite_tails_tendsto K).2).max (tendsto_const_nhds (x := (0 : ℝ)))).pow 2).div_const
      (2 * (2 * (K : ℝ) + 1) * (2 * (M : ℝ) + 4))
  apply sub_nonpos.mp
  apply VanishingTradeoff.limit_le_zero
    (s := s ∩ Set.Ici (max K R)) (g := g) (A := 2)
    (B := (2 * (M : ℝ) + 3) * (2 * (M : ℝ) + 4))
    (C := β * N * (bankCost M 2 : ℝ) * c)
    (hcredit.sub (((P.finite_tails_tendsto R).1.const_mul β).div_const
      ((M - R : ℕ) : ℝ))) hη (by norm_num) (by positivity) (by positivity)
  · intro J hJ
    exact ((S.geometry (P.subsequence 0)).prefixMeanSeeds_nonneg
      (S.order (P.subsequence 0)) J R M hM).trans
        (hbound J hJ.1 ((le_max_right K R).trans hJ.2) 0).2
  · intro ε hε J₀
    obtain ⟨J, hJ, hJs, hprod⟩ := hsmall ε hε (max J₀ (max K R))
    exact ⟨J, (le_max_left _ _).trans hJ,
      ⟨hJs, (le_max_right _ _).trans hJ⟩, hprod⟩
  · intro J hJ lam hlam
    have h := P.prefix_sharing_limit ((le_max_left K R).trans hJ.2)
      ((le_max_right K R).trans hJ.2) hM hRM
      (fun n => (hbound J hJ.1 ((le_max_right K R).trans hJ.2) n).1)
      (fun n => (hbound J hJ.1 ((le_max_right K R).trans hJ.2) n).2) hlam
    linarith only [h]

include P in
/-- A positive one-exception gap credit cannot be paid by vanishing hop
tails at an unbounded set of protected scales. Shared by both raw-payment criteria. -/
theorem false_of_one_exception_tail_bounds {radii : Set ℕ}
    (hradii : ∀ R₀ : ℕ, ∃ R ≥ R₀, R ∈ radii)
    (hbound : ∀ K R, R ∈ radii →
      max (1 - P.variationTail K) 0 ^ 2 /
        (2 * (2 * (K : ℝ) + 1) * (2 * ((2 * R + 2 : ℕ) : ℝ) + 4)) ≤
      β * P.hopTail R / ((2 * R + 2 - R : ℕ) : ℝ)) : False := by
  obtain ⟨K, hK⟩ := (P.tails_tendsto_zero.2.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists
  let A := max (1 - P.variationTail K) 0 ^ 2 / (8 * (2 * (K : ℝ) + 1))
  have hA : 0 < A := by
    have : 0 < max (1 - P.variationTail K) 0 :=
      (sub_pos.mpr hK).trans_le (le_max_left _ _)
    positivity
  have hev : ∀ᶠ R in atTop, β * P.hopTail R < A := by
    have hlim : Tendsto (fun R => β * P.hopTail R) atTop (𝓝 0) := by
      simpa only [mul_zero] using P.tails_tendsto_zero.1.const_mul β
    exact hlim.eventually (Iio_mem_nhds hA)
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hev
  obtain ⟨R, hRR, hR⟩ := hradii R₀
  have h := hbound K R hR
  rw [show 2 * R + 2 - R = R + 2 by omega] at h
  have hscaled := mul_le_mul_of_nonneg_right h (by positivity : (0 : ℝ) ≤ R + 2)
  have hpaid : A ≤ β * P.hopTail R := by
    convert hscaled using 1 <;>
      simp only [A, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] <;> field_simp
    ring
  exact (not_lt_of_ge hpaid) (hR₀ R hRR)

include P in
/-- Any unbounded collection of protected scales suffices. A full sequence
of small sharing products, a positive rate, and positive cost coefficients
are all unnecessary. -/
theorem false_of_sharing_bounds {radii : Set ℕ} {cutoffs : ℕ → Set ℕ}
    {η : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    (hradii : ∀ R₀ : ℕ, ∃ R ≥ R₀, R ∈ radii)
    (hη : Tendsto η atTop (𝓝 0))
    (hsmall : ∀ R ∈ radii, ∀ ε > 0, ∀ J₀ : ℕ,
      ∃ J ≥ J₀, J ∈ cutoffs R ∧ η J * g R J < ε)
    (hbound : ∀ n, (S.geometry n).HasSharingBounds (S.order n) radii cutoffs η g) :
    False := by
  apply P.false_of_one_exception_tail_bounds hradii
  intro K R hR
  exact P.sharing_tail_lower (K := K) (R := R)
    (M := 2 * R + 2) (by omega) (by omega) hη (hsmall R hR)
    (fun J hJ hRJ n => hbound (P.subsequence n) R hR J hJ hRJ)

include P in
/-- The paper's zero-liminf formulation is exactly the common-cutoff
criterion with all cutoffs allowed. Lower limits are in `ℝ≥0∞`. -/
theorem false_of_sharing_liminf {radii : Set ℕ} {η : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    (hradii : ∀ R₀ : ℕ, ∃ R ≥ R₀, R ∈ radii) (hη : Tendsto η atTop (𝓝 0))
    (hsmall : ∀ R ∈ radii, liminf (fun J => ENNReal.ofReal (η J * g R J)) atTop = 0)
    (hbound : ∀ n, (S.geometry n).HasSharingBounds
      (S.order n) radii (fun _ => Set.univ) η g) : False := by
  apply P.false_of_sharing_bounds hradii hη ?_ hbound
  intro R hR ε hε J₀
  obtain ⟨J, hJ, hprod⟩ := TailLiminf.liminf_ofReal_eq_zero_iff.mp (hsmall R hR) ε hε J₀
  exact ⟨J, hJ, Set.mem_univ _, hprod⟩

end NearFullSequence.JointProfile

/-- The uniform sharing criterion on arbitrary common sets of good cutoffs.
All index sets and budgets are fixed before dimension. The code-size bound
is included, and sign assumptions are derived from any nonempty class. -/
theorem sharing_uniform_deficit {c β : ℝ} {N : ℕ}
    {radii : Set ℕ} {cutoffs : ℕ → Set ℕ} {η : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    (hradii : ∀ R₀ : ℕ, ∃ R ≥ R₀, R ∈ radii)
    (hη : Tendsto η atTop (𝓝 0))
    (hsmall : ∀ R ∈ radii, ∀ ε > 0, ∀ J₀ : ℕ,
      ∃ J ≥ J₀, J ∈ cutoffs R ∧ η J * g R J < ε) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ G : AdmissibleGeometry c β N 2,
      ∀ O : SortedCore G.core, G.HasSharingBounds O radii cutoffs η g →
      d₀ ≤ G.d → (G.a0 : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  apply uniform_deficit_of_no_ordered_nearFull
    (fun G O => G.HasSharingBounds O radii cutoffs η g)
  intro S hbound
  obtain ⟨P⟩ := S.exists_jointProfile
  exact P.false_of_sharing_bounds hradii hη hsmall hbound

/-- Theorem H with the stated zero lower limits. Nonnegative, rather than
strictly positive, omitted-size bounds suffice whenever the class is nonempty. -/
theorem liminf_sharing_uniform_deficit {c β : ℝ} {N : ℕ}
    {radii : Set ℕ} {η : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    (hradii : ∀ R₀ : ℕ, ∃ R ≥ R₀, R ∈ radii) (hη : Tendsto η atTop (𝓝 0))
    (hsmall : ∀ R ∈ radii, liminf (fun J => ENNReal.ofReal (η J * g R J)) atTop = 0) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ G : AdmissibleGeometry c β N 2,
      ∀ O : SortedCore G.core,
      G.HasSharingBounds O radii (fun _ => Set.univ) η g →
      d₀ ≤ G.d → (G.a0 : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  apply uniform_deficit_of_no_ordered_nearFull
    (fun G O => G.HasSharingBounds O radii (fun _ => Set.univ) η g)
  intro S hbound
  obtain ⟨P⟩ := S.exists_jointProfile
  exact P.false_of_sharing_liminf hradii hη hsmall hbound

/-- The universal sorted-count rate yields the no-envelope criterion.
The only geometric hypothesis here is the actual mean seed bound. -/
theorem sublinear_sharing_uniform_deficit {c β : ℝ} {N : ℕ}
    {radii : Set ℕ} {g : ℕ → ℕ → ℝ}
    (hradii : ∀ R₀ : ℕ, ∃ R ≥ R₀, R ∈ radii)
    (hsmall : ∀ R ∈ radii,
      liminf (fun J => ENNReal.ofReal (g R J / (J + 1 : ℝ))) atTop = 0) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ G : AdmissibleGeometry c β N 2,
      ∀ O : SortedCore G.core,
      (∀ R ∈ radii, ∀ J, R ≤ J →
        G.prefixMeanSeeds O J R (2 * R + 2) (by omega) ≤ g R J) →
      d₀ ≤ G.d → (G.a0 : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  apply uniform_deficit_of_no_ordered_nearFull
    (fun G O => ∀ R ∈ radii, ∀ J, R ≤ J →
      G.prefixMeanSeeds O J R (2 * R + 2) (by omega) ≤ g R J)
  intro S hbound
  obtain ⟨P⟩ := S.exists_jointProfile
  have hc : 0 ≤ c := by simpa using P.hop_mass.2.1 ∅
  apply P.false_of_sharing_liminf (η := fun J => c / (J + 1 : ℝ)) hradii
  · simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat c).comp (tendsto_add_atTop_nat 1)
  · intro R hR
    simpa only [div_mul_eq_mul_div, mul_div_assoc] using
      TailLiminf.liminf_ofReal_const_mul_eq_zero hc (hsmall R hR)
  · intro n R hR J _ hRJ
    exact ⟨(S.geometry n).hopProfile_le_rank (S.order n) J, hbound n R hR J hRJ⟩

/-- A power-envelope version for every real exponent `p > 0`, not only
`p > 1`: summability comes from the actual joint profile, not the envelope.
Zero amplitude and arbitrarily late sub-power sharing are permitted. -/
theorem power_sharing_uniform_deficit {c β : ℝ} {N : ℕ}
    {radii : Set ℕ} {g : ℕ → ℕ → ℝ} {H p : ℝ}
    (hradii : ∀ R₀ : ℕ, ∃ R ≥ R₀, R ∈ radii) (hH : 0 ≤ H) (hp : 0 < p)
    (hsmall : ∀ R ∈ radii,
      liminf (fun J => ENNReal.ofReal (g R J / (J + 1 : ℝ) ^ p)) atTop = 0) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ G : AdmissibleGeometry c β N 2,
      ∀ O : SortedCore G.core,
      (∀ J, O.hopProfile G.inputLength J ≤ H / (J + 1 : ℝ) ^ p) →
      (∀ R ∈ radii, ∀ J, R ≤ J →
        G.prefixMeanSeeds O J R (2 * R + 2) (by omega) ≤ g R J) →
      d₀ ≤ G.d → (G.a0 : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  have hη : Tendsto (fun J : ℕ => H / (J + 1 : ℝ) ^ p) atTop (𝓝 0) := by
    have hden : Tendsto (fun J : ℕ => (J + 1 : ℝ) ^ p) atTop atTop :=
      (tendsto_rpow_atTop hp).comp
      (by simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
    simpa only [div_eq_mul_inv, Pi.inv_apply, mul_zero] using
      hden.inv_tendsto_atTop.const_mul H
  obtain ⟨ε, hε, d₀, hgap⟩ := liminf_sharing_uniform_deficit
    (c := c) (β := β) (N := N) (g := g) hradii hη (fun R hR => by
      simpa only [div_mul_eq_mul_div, mul_div_assoc] using
        TailLiminf.liminf_ofReal_const_mul_eq_zero hH (hsmall R hR))
  exact ⟨ε, hε, d₀, fun G O henv hshare =>
    hgap G O (fun R hR J _ hRJ => ⟨henv J, hshare R hR J hRJ⟩)⟩

end
end SourceCovers

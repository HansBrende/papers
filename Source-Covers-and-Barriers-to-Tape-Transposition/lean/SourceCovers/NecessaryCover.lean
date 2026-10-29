import SourceCovers.PrefixLimit
import SourceCovers.CoverDistribution
import LeanMachine.InverseSquareTail

set_option autoImplicit false

/-!
# Necessary reciprocal-cover complexity

Take the dimension upper limit first, along the supplied joint-profile
subsequence, then the prefix upper limit. Actual averages stay in `[0,1]`.
The distinguished and protected cutoffs are independent, and the modulus
may be any fixed `M ≥ 2` with `R < M`.
-/

namespace SourceCovers.NearFullSequence.JointProfile

open Classical Finset Filter LeanMachine
open scoped BigOperators Topology
noncomputable section

variable {c β : ℝ} {N q : ℕ} {S : NearFullSequence c β N q} (P : S.JointProfile)

theorem prefixReciprocal_limsup_bounds {J R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) :
    1 / (2 * (M : ℝ) + 4) ^ q ≤ limsup (P.prefixReciprocal J R M hM) atTop ∧
      limsup (P.prefixReciprocal J R M hM) atTop ≤ 1 := by
  have h := fun n => P.prefixReciprocal_bounds (J := J) hM hRM n
  exact ⟨BoundedLimsup.le_limsup (fun n => (h n).2)
    (Eventually.of_forall fun n => (h n).1),
    BoundedLimsup.limsup_le_one (fun n =>
      (by positivity : (0 : ℝ) ≤ 1 / (2 * (M : ℝ) + 4) ^ q).trans (h n).1)
      (fun n => (h n).2)⟩

/-- Dimension upper limit, followed by prefix upper limit, with fixed modulus. -/
def reciprocalCoverLimit (R M : ℕ) (hM : 2 ≤ M) : ℝ :=
  limsup (fun J => limsup (P.prefixReciprocal J R M hM) atTop) atTop

theorem reciprocalCoverLimit_bounds {R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) :
    1 / (2 * (M : ℝ) + 4) ^ q ≤ P.reciprocalCoverLimit R M hM ∧
      P.reciprocalCoverLimit R M hM ≤ 1 := by
  have h := fun J => P.prefixReciprocal_limsup_bounds (J := J) hM hRM
  exact ⟨BoundedLimsup.le_limsup (fun J => (h J).2)
    (Eventually.of_forall fun J => (h J).1),
    BoundedLimsup.limsup_le_one (fun J =>
      (by positivity : (0 : ℝ) ≤ 1 / (2 * (M : ℝ) + 4) ^ q).trans (h J).1)
      (fun J => (h J).2)⟩

/-- Keep the coefficient until after both limits, even if it vanishes.
No comparison between the cutoffs or positivity of the limiting credit is needed. -/
theorem weighted_reciprocal_cover {K R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) :
    max (1 - P.variationTail K) 0 ^ 2 / (2 * (2 * (K : ℝ) + 1)) *
        P.reciprocalCoverLimit R M hM ≤ β * P.hopTail R / ((M - R : ℕ) : ℝ) := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hε : 0 < δ / 2 := by positivity
  let C : ℝ := β * N * (bankCost M q : ℝ) * c ^ 2
  have herror : Tendsto (fun J : ℕ => C / ((δ / 2) * (J + 1 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, div_div] using
      (tendsto_const_div_atTop_nhds_zero_nat (C / (δ / 2))).comp
        (tendsto_add_atTop_nat 1)
  have hcredit := ((((tendsto_const_nhds (x := (1 : ℝ))).sub
    (P.finite_tails_tendsto K).2).max (tendsto_const_nhds (x := (0 : ℝ)))).pow 2).div_const
      (2 * (2 * (K : ℝ) + 1))
  have hcost := ((((P.finite_tails_tendsto R).1.const_mul β).div_const
    ((M - R : ℕ) : ℝ)).add_const (2 * (δ / 2))).add herror
  have hbnd := fun J => P.prefixReciprocal_limsup_bounds (J := J) hM hRM
  have h := BoundedLimsup.mul_limsup_le_of_tendsto
    (fun J => (by positivity : (0 : ℝ) ≤ 1 / (2 * (M : ℝ) + 4) ^ q).trans (hbnd J).1)
    (fun J => (hbnd J).2) hcredit hcost
    (eventually_atTop.2 ⟨max K R, fun J hJ => P.prefix_reciprocal_limit
      ((le_max_left K R).trans hJ) ((le_max_right K R).trans hJ) hM hRM hε⟩)
  simpa only [reciprocalCoverLimit, add_zero, show 2 * (δ / 2) = δ by ring] using h

/-- Divide only by the positive limiting coefficient. This works for any
fixed legal modulus and independent natural cutoffs, including `R = 0`. -/
theorem necessary_reciprocal_cover {K R M : ℕ} (hM : 2 ≤ M) (hRM : R < M)
    (hV : P.variationTail K < 1) :
    P.reciprocalCoverLimit R M hM ≤
      2 * β * (2 * (K : ℝ) + 1) * P.hopTail R /
        ((1 - P.variationTail K) ^ 2 * ((M - R : ℕ) : ℝ)) := by
  have hv : 0 < 1 - P.variationTail K := sub_pos.mpr hV
  have h := P.weighted_reciprocal_cover (K := K) hM hRM
  rw [max_eq_left hv.le] at h
  have hc : 0 < (1 - P.variationTail K) ^ 2 / (2 * (2 * (K : ℝ) + 1)) := by positivity
  have hb := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using h)
  convert hb using 1
  field_simp

/-- The manuscript's `M = 2R+2` specialization, with no `R ≥ K` condition. -/
theorem necessary_reciprocal_cover_default {K R : ℕ} (hV : P.variationTail K < 1) :
    P.reciprocalCoverLimit R (2 * R + 2) (by omega) ≤
      2 * β * (2 * (K : ℝ) + 1) * P.hopTail R /
        ((1 - P.variationTail K) ^ 2 * (R + 2 : ℝ)) := by
  simpa only [show 2 * R + 2 - R = R + 2 by omega, Nat.cast_add, Nat.cast_ofNat] using
    P.necessary_reciprocal_cover (K := K) (R := R) (M := 2 * R + 2) (by omega) (by omega) hV

/-- The actual fraction of legal phase-column pairs with cover weight at
most a fixed threshold, along the same subsequence and original ordering. -/
def prefixCoverBelow (J R M : ℕ) (hM : 2 ≤ M) (s : ℝ) (n : ℕ) : ℝ :=
  let G := S.geometry (P.subsequence n)
  let O := S.order (P.subsequence n)
  meanCoverBelow (G.core_coloring.mono (O.selectedPrefix_subset J)) hM G.exceptions
    G.x G.t G.d G.b (admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M) s

theorem prefixCoverBelow_bounds (J R M : ℕ) (hM : 2 ≤ M) (s : ℝ) (n : ℕ) :
    0 ≤ P.prefixCoverBelow J R M hM s n ∧ P.prefixCoverBelow J R M hM s n ≤ 1 :=
  meanCoverBelow_bounds _ _ _ _ _ _ _ _ _

/-- Ordered upper limits of the finite cover probabilities. -/
def coverProbabilityLimit (R M : ℕ) (hM : 2 ≤ M) (s : ℝ) : ℝ :=
  limsup (fun J => limsup (P.prefixCoverBelow J R M hM s) atTop) atTop

theorem coverProbabilityLimit_bounds (R M : ℕ) (hM : 2 ≤ M) (s : ℝ) :
    0 ≤ P.coverProbabilityLimit R M hM s ∧ P.coverProbabilityLimit R M hM s ≤ 1 := by
  have h0 := fun J => BoundedLimsup.limsup_nonneg
    (fun n => (P.prefixCoverBelow_bounds J R M hM s n).1)
    (fun n => (P.prefixCoverBelow_bounds J R M hM s n).2)
  have h1 := fun J => BoundedLimsup.limsup_le_one
    (fun n => (P.prefixCoverBelow_bounds J R M hM s n).1)
    (fun n => (P.prefixCoverBelow_bounds J R M hM s n).2)
  exact ⟨BoundedLimsup.limsup_nonneg h0 h1, BoundedLimsup.limsup_le_one h0 h1⟩

/-- The finite reciprocal bound passes through both upper limits. -/
theorem coverProbabilityLimit_le_reciprocal {R M : ℕ} (hM : 2 ≤ M) (hRM : R < M)
    {s : ℝ} (hs : 0 ≤ s) :
    P.coverProbabilityLimit R M hM s ≤ s * P.reciprocalCoverLimit R M hM := by
  have hQ := fun J n => P.prefixReciprocal_bounds (J := J) hM hRM n
  have hQ0 := fun J n =>
    (by positivity : (0 : ℝ) ≤ 1 / (2 * (M : ℝ) + 4) ^ q).trans (hQ J n).1
  have hB := fun J n => P.prefixCoverBelow_bounds J R M hM s n
  have hpoint (J n : ℕ) :
      P.prefixCoverBelow J R M hM s n ≤ s * P.prefixReciprocal J R M hM n := by
    let G := S.geometry (P.subsequence n)
    let O := S.order (P.subsequence n)
    exact meanCoverBelow_le_mul_meanReciprocalCover
      (G.core_coloring.mono (O.selectedPrefix_subset J)) hM G.exceptions G.x G.t
      G.hd G.hb G.append_lt _ (fun _ hρ => admissiblePhase_lt hρ) hs
  have hinner (J : ℕ) := BoundedLimsup.limsup_le_mul_limsup
    (fun n => (hB J n).1)
    (hQ0 J) (fun n => (hQ J n).2) hs (Eventually.of_forall (hpoint J))
  exact BoundedLimsup.limsup_le_mul_limsup
    (fun J => BoundedLimsup.limsup_nonneg (fun n => (hB J n).1) (fun n => (hB J n).2))
    (fun J => BoundedLimsup.limsup_nonneg (hQ0 J) (fun n => (hQ J n).2))
    (fun J => BoundedLimsup.limsup_le_one (hQ0 J) (fun n => (hQ J n).2))
    hs (Eventually.of_forall hinner)

/-- A finite envelope in the supplied original ordering passes to the
limiting hop profile; no convergence of finite tails is asserted. -/
theorem hop_le_of_pointwise {g : ℕ → ℝ} (hg : ∀ n i, S.hops n i ≤ g i) :
    ∀ i, P.h i ≤ g i := fun i =>
  le_of_tendsto' (P.hops_tendsto i) (fun n => hg (P.subsequence n) i)

/-- The limiting inverse-square envelope suffices; a common finite envelope
is only one way to obtain it. The threshold may be any nonnegative real. -/
theorem inverse_square_cover_probability {K R : ℕ} {H s : ℝ}
    (hH : 0 ≤ H) (hs : 0 ≤ s) (hR : 0 < R) (hV : P.variationTail K ≤ 1 / 2)
    (hh : ∀ i, P.h i ≤ H / (i + 1 : ℝ) ^ 2) :
    P.coverProbabilityLimit R (2 * R + 2) (by omega) s ≤
      8 * β * (2 * (K : ℝ) + 1) * H * s / ((R : ℝ) * (R + 2)) := by
  have hβ : 0 ≤ β := recordCapacity_nonneg (S.geometry 0).capacity
  have htail : P.hopTail R ≤ H / R :=
    InverseSquareTail.tail_le hH P.hop_mass.1 hh hR
  have hv : P.variationTail K < 1 := by linarith
  have hv2 : (1 / 4 : ℝ) ≤ (1 - P.variationTail K) ^ 2 := by nlinarith
  have hQ := (P.necessary_reciprocal_cover_default (R := R) hv).trans
    (div_le_div₀ (by positivity : (0 : ℝ) ≤ 2 * β * (2 * (K : ℝ) + 1) * (H / R))
      (mul_le_mul_of_nonneg_left htail (by positivity))
      (by positivity : (0 : ℝ) < (1 / 4) * (R + 2 : ℝ))
      (mul_le_mul_of_nonneg_right hv2 (by positivity)))
  have h := (P.coverProbabilityLimit_le_reciprocal (M := 2 * R + 2)
    (by omega) (by omega) hs).trans (mul_le_mul_of_nonneg_left hQ hs)
  convert h using 1
  field_simp
  ring

end
end SourceCovers.NearFullSequence.JointProfile

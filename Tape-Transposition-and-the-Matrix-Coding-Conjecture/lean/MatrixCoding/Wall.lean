import MatrixCoding.FiniteWholeRowPayments
import MatrixCoding.NormalizedRateTransfer

/-!
# The open whole-row target for adaptive transposition

THIS IS THE FILE TO IMPORT WHEN TRYING TO PROVE OR REFUTE THE TARGET.
The target is `LeanBacklog.Wall.Conjecture`, a proposition, not an admitted
theorem. Prove that proposition, or prove its negation. No assertion of it
is imported into the verified exclusion theorem below.

All alphabets are the canonical b(d)-bit alphabet, b(d)=max(1,ceil(log₂ d)).
For each resource triple k≥5,G≥1,c≥4 and each size threshold, choose one
larger dimension d, density θ>0, reverse cutoff R and deficit δ. Choices
may vary with d. There is no common positive deficit assumption.

The tested codes are arbitrary finite sets of d×d arrays. Their helper
relation is symmetric and reflexive, of width at most W+R+1. Column j is
determined by rows ρ(j), AND row j is determined by columns ρ(j), with the
same ρ. No linearity, code symmetry or decoder invariance is assumed.

Definitions, all fixed and independent of a code:
  L = d² b(d), r = ceil(d b(d)/G),
  D = genieDepth(k,1,12,θ), W = 2(G+1)(2k+3)^D,
  K = c+4+5(k−3)(cG+2),
  M = (4kG+1) r floor(θ ceil(cL/r)),
  h = 0 if R≥d, else min(d, floor(Wd/(R+1))), X = 2dh−h².
The hypothesis is a code bound |C|≤2^((1−δ)L) together with
  δL > 2(Kd+M) + b(d)X.
M and X retain integer rounding and the overlap of fixed rows/columns.
Their Lean definitions are `cutBudget` and `crossBudget`.

Proved here:
  wall.md's common deficit → previous criterion → Conjecture → ¬(T).
The first two arrows prove weakening, NOT strict non-equivalence for the
actual capacities. No converse or strict-separation theorem is known.

Reproduce from Tape-Transposition-and-the-Matrix-Coding-Conjecture/lean:
  lake build MatrixCoding.Wall
  lake env lean MatrixCoding/Wall.lean
The old lean-backlog/Wall.lean is a compatibility import of this file, so
agents working from the backlog use exactly the same open proposition.

To work on the open problem, add your own theorem of either type:
  LeanBacklog.Wall.Conjecture
  ¬ LeanBacklog.Wall.Conjecture
The exclusion theorem has an explicit hypothesis and contains no placeholder.
-/

namespace LeanBacklog.Wall

open Finset Transpose Transpose.Tape Transpose.Tape.Impl
open LeanBacklog.RowSpread LeanBacklog.BlockTCC

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The question actually posed in wall.md: one positive asymptotic deficit
for all fixed windows, with dimension thresholds allowed to depend on window. -/
def CommonDeficit : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ UniformWholeRowRateCanonicalBits (1-δ)

/-- OPEN. This is the standalone target to prove or refute. The bound is
uniform over all codes/relations at the selected dimension, not over d. -/
def Conjecture : Prop :=
  ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c → ∀ d₀ : ℕ,
    ∃ (d R : ℕ) (θ δ : ℝ), max d₀ 1 ≤ d ∧ 0 < θ ∧
      NormalizedTwoSidedWholeRowCardinalityBound d (endWindow k G θ+R+1)
        (Fin (entryBits d) → Bool) ((1-δ)*(d:ℝ)^2) ∧
      (2*(adaptiveAllowance k G c*d+cutBudget k G c d θ):ℕ) +
        (entryBits d*crossBudget d (endWindow k G θ) R:ℕ) <
          δ*(d*d*entryBits d:ℕ)

/-- The previously published hypothesis implies the sharper finite target. -/
theorem of_previous (h : AdaptiveNormalizedCriterion) : Conjecture := by
  intro k G c hk hG hc d₀
  obtain ⟨d, R, θ, δ, hd, hθ, hbound, hgap⟩ := h k G c hk hG hc d₀
  refine ⟨d, R, θ, δ, hd, hθ, hbound, ?_⟩
  have hdpos : 0 < (d:ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hg := mul_lt_mul_of_pos_left hgap (show 0 < 2*(d:ℝ) by positivity)
  have hm := cutBudget_le_envelope (k := k) (c := c) (d := d) hG hθ.le
  have hx := crossBudget_le_envelope d (endWindow k G θ) R
  have hx' := mul_le_mul_of_nonneg_left hx (show (0:ℝ) ≤ entryBits d by positivity)
  dsimp [endSurplus] at hg
  push_cast at hg hm hx' ⊢
  nlinarith only [hg, hm, hx']

/-- The original wall hypothesis implies the previous finite criterion.
This checks the quantifier comparison; it does not assert either premise. -/
theorem commonDeficit_implies_previous (h : CommonDeficit) : AdaptiveNormalizedCriterion := by
  obtain ⟨δ₀, hδ₀, hbound⟩ := h
  intro k G c hk hG hc d₀
  let B : ℝ := ((4*k*G+1:ℕ):ℝ)
  have hcpos : (0:ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have hB : 0 < B := by dsimp [B]; positivity
  let θ := δ₀/(16*(B*c))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθeq : B*c*θ = δ₀/16 := by
    have he : (16*(B*c))*θ = δ₀ := by
      dsimp [θ]; exact mul_div_cancel₀ _ (by positivity)
    nlinarith only [he]
  let W := endWindow k G θ
  obtain ⟨R, hR⟩ := exists_symmetryPayment_lt W (show 0 < δ₀/4 by positivity)
  let ε := (δ₀/2-symmetryPayment W R)/2
  let γ := ε-B*c*θ
  have hγ : 0 < γ := by dsimp [γ, ε]; linarith
  let K : ℝ := adaptiveAllowance k G c
  obtain ⟨n, hn⟩ := exists_nat_gt ((K+B*θ)/γ)
  obtain ⟨d₁, hd₁⟩ := hbound (W+R+1) (δ₀/2) (by positivity)
  let d := max (max (max d₀ 1) n) d₁
  have hd0 : max d₀ 1 ≤ d := (le_max_left _ _).trans (le_max_left _ _)
  have hdn : (n:ℝ) ≤ d := by
    exact_mod_cast (show n ≤ d from (le_max_right _ _).trans (le_max_left _ _))
  have hprod := (div_lt_iff₀ hγ).mp (lt_of_lt_of_le hn hdn)
  have hsave : K < (d:ℝ)*ε-B*θ*((c:ℝ)*d+1) := by
    dsimp [γ] at hprod
    nlinarith only [hprod]
  have hnonneg : 0 ≤ (d:ℝ)*ε-B*θ*((c:ℝ)*d+1) :=
    le_trans (by dsimp [K]; positivity) hsave.le
  have hbits : (1:ℝ) ≤ entryBits d := by
    exact_mod_cast (show 1 ≤ entryBits d by unfold entryBits; omega)
  have hpay := mul_le_mul_of_nonneg_right hbits hnonneg
  refine ⟨d, R, θ, δ₀/2, hd0, hθ, ?_, ?_⟩
  · convert (hd₁ d (le_max_right _ _)).twoSided.normalized using 1
    ring
  · change K < (entryBits d:ℝ)*((d:ℝ)*ε-B*θ*((c:ℝ)*d+1))
    linarith

/-- Verified direction of the comparison with wall.md. Strictness is open. -/
theorem of_commonDeficit (h : CommonDeficit) : Conjecture :=
  of_previous (commonDeficit_implies_previous h)

/-- A proof of the standalone target excludes ALL adaptive linear-time
transposers, using the existing frozen predicate. No open theorem is invoked. -/
theorem excludes_adaptive (h : Conjecture) : ¬ LinearTimeTransposable := by
  rintro ⟨M, c, hM⟩
  obtain ⟨d, R, θ, δ, hd, hθ, hbound, hgap⟩ := h
    (M.k+1+(1+3)) (cellBits (bufTM M)) (2*c+4) (by omega)
    (cellBits_pos _) (by omega) (coarseSize M c)
  have hsize : coarseSize M c ≤ d := (le_max_left _ _).trans hd
  have hdpos : 1 ≤ d := (le_max_right _ _).trans hd
  obtain ⟨Dg, F, code, hDg, hT, hlarge, hsolve, hend⟩ :=
    codes_coentLinear_at hsize (hM d hdpos)
  have hnormalized := normalized_bound_finite hbound (by simp)
  have hcode := hnormalized.oneSided (by simp)
  have hbill := end_invoice_finite hDg (cellBits_pos _) hdpos hT hend hθ
    (capProfile_profileCap Dg d (cellBits (bufTM M))) hlarge hsolve hcode
  have hk : M.k+1+(1+3)-4 = M.k+1 := by omega
  simp only [adaptiveAllowance, hk] at hgap
  push_cast at hbill hgap
  nlinarith only [hbill, hgap]

#print axioms CommonDeficit
#print axioms Conjecture
#print axioms of_previous
#print axioms commonDeficit_implies_previous
#print axioms of_commonDeficit
#print axioms excludes_adaptive

end LeanBacklog.Wall

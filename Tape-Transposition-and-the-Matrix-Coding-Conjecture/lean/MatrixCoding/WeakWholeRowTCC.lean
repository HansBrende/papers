import MatrixCoding.BlockEndRows
import MatrixCoding.BlockCodeInvoice
import MatrixCoding.NormalizedCodeTransfer
import Transpose.Tape.Statements.Coding

/-!
# A finite, cofinal whole-row criterion excluding adaptive machines

No common deficit, fixed window, or all-large-dimension bound is assumed.
At arbitrarily large selected dimensions the deficit need only beat the
explicit cut payment and the one coentropy constant supplied by Paper 1.
The normalized version asks only about symmetric, reflexive, two-sided
codes, at the canonical bit alphabet. Both criteria remain open hypotheses.
-/

namespace LeanBacklog.BlockTCC

open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth
open RowSpread

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Continuous final output puts each row in at most G+1 grain slots. -/
noncomputable def endWindow (k G : ℕ) (θ : ℝ) : ℕ :=
  (G+1) * (2 * (2*k+3) ^ blockDepth k θ)

/-- Net saved bits, divided by d. The final-slot overhead is db, not L;
cut-root outputs cost one bit each, giving 4kG+1 rather than (4k+1)G. -/
noncomputable def endSurplus (k G c d : ℕ) (θ δ : ℝ) : ℝ :=
  (entryBits d : ℝ) * ((d:ℝ)*δ - ((4*k*G+1:ℕ):ℝ)*θ*((c:ℝ)*d+1))

/-- Finite output-at-end invoice, with arbitrary coentropy and deficit. -/
theorem end_invoice {k d G c coent : ℕ} {Dg : TSDiagram k} {θ δ : ℝ}
    (hDg : Dg.Valid (d*d*entryBits d)) (hG : 1 ≤ G) (hd : 1 ≤ d)
    (hT : Dg.T ≤ c*(d*d*entryBits d))
    (hend : ∀ t ≤ Dg.T, Dg.out t = d*d*entryBits d - (Dg.T-t))
    (hθ : 0 < θ)
    {cap : ℕ × ℕ → ℕ} (hcap : Dg.CapProfile d G cap)
    {F : Set (Fin (d*d*entryBits d) → Bool)} {code : NetCode}
    (hlarge : 2^(d*d*entryBits d) ≤ 2^coent * F.ncard)
    (hsolve : Dg.Solves d G cap F code)
    (hbound : WholeRowCardinalityBound d (endWindow k G θ)
      (Fin (entryBits d) → Bool) ((1-δ)*(d:ℝ)^2)) :
    (d:ℝ)*endSurplus k G c d θ δ ≤ coent := by
  let b := entryBits d
  let r := TSDiagram.blockSize G d
  let N := Dg.nodes r
  have hb : 1 ≤ b := by dsimp [b, entryBits]; omega
  have hL : 1 ≤ d*d*b := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hW : 0 < d*b := by positivity
  have hr : 1 ≤ r := one_le_blockSize hG hd
  have hNr : (N:ℝ)*r ≤ (c:ℝ)*(d*d*b:ℕ) + d*b := by
    have hNr' : N*r ≤ Dg.T+r := (nodes_mul_le r).trans (Nat.sub_le _ _)
    have ht : Dg.T+r ≤ c*(d*d*b)+d*b := Nat.add_le_add hT (blockSize_le hG)
    exact_mod_cast hNr'.trans ht
  have hN : 1 ≤ N := by
    have ht := one_le_T hDg hL
    have hnr := T_le_nodes_mul (D := Dg) hr
    dsimp only [N]
    nlinarith
  obtain ⟨Γ, rank, _, hΓ, hrank_le, hrank⟩ :=
    exists_block_cut Dg (fun t => (hDg.1 t).2) hr hN hθ
  have hinvoice := robust_invoice_sharp (M := G+1) hDg hG hd Γ rank hrank_le hrank
    hcap hlarge hsolve hbound
  have hE := badOutputRows_atEnd_eq_empty hDg hr hW (blockSize_mul_ge hG) hend
  change badOutputRows Dg d (entryBits d) (TSDiagram.blockSize G d) (G+1) = ∅ at hE
  simp only [hE, card_empty, Nat.mul_zero, Nat.zero_mul, Nat.cast_zero, add_zero] at hinvoice
  have hcut : (((4*k*G+1)*r*Γ.card:ℕ):ℝ) ≤
      ((4*k*G+1:ℕ):ℝ)*θ*((c:ℝ)*(d*d*b:ℕ)+d*b) := by
    have hmul := mul_le_mul_of_nonneg_left hΓ
      (show (0:ℝ) ≤ ((4*k*G+1:ℕ):ℝ)*r by positivity)
    have hmul' := mul_le_mul_of_nonneg_left hNr
      (show (0:ℝ) ≤ ((4*k*G+1:ℕ):ℝ)*θ by positivity)
    push_cast at hmul hmul' ⊢
    nlinarith only [hmul, hmul']
  change (d*d*b:ℕ) ≤ (coent:ℕ) + ((4*k*G+1)*r*Γ.card:ℕ) +
    (b:ℝ)*((1-δ)*(d:ℝ)^2) at hinvoice
  change (d:ℝ)*((b:ℝ)*((d:ℝ)*δ-((4*k*G+1:ℕ):ℝ)*θ*((c:ℝ)*d+1))) ≤ coent
  push_cast at hinvoice hcut ⊢
  nlinarith only [hinvoice, hcut]

/-- The coentropy allowance on the buffered machine image. The offset four
undoes the four auxiliary tapes added after the coarse trace was chosen. -/
def adaptiveAllowance (k G c : ℕ) : ℕ := coarseConst (k-4) c G

/-- Pointwise bounds at cofinally many dimensions suffice. The selected
dimension, cut density and deficit may all depend on k,G,c and the lower
size threshold. No quantifier over machines or diagrams occurs here. -/
def AdaptiveWholeRowCriterion : Prop :=
  ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c → ∀ d₀ : ℕ,
    ∃ (d : ℕ) (θ δ : ℝ), max d₀ 1 ≤ d ∧ 0 < θ ∧
      WholeRowCardinalityBound d (endWindow k G θ)
        (Fin (entryBits d) → Bool) ((1-δ)*(d:ℝ)^2) ∧
      (adaptiveAllowance k G c:ℝ) < endSurplus k G c d θ δ

/-- A convenient stronger premise: for each resource triple, one window
and a deficit exceeding its cut price, on cofinally many dimensions.
The deficit may deteriorate arbitrarily between resource triples. -/
theorem criterion_of_fixedWindow
    (h : ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c →
      ∃ θ δ : ℝ, 0 < θ ∧ ((4*k*G+1:ℕ):ℝ)*c*θ < δ ∧
        ∀ d₀ : ℕ, ∃ d ≥ d₀,
          WholeRowCardinalityBound d (endWindow k G θ)
            (Fin (entryBits d) → Bool) ((1-δ)*(d:ℝ)^2)) :
    AdaptiveWholeRowCriterion := by
  intro k G c hk hG hc d₀
  obtain ⟨θ, δ, hθ, hmargin, hb⟩ := h k G c hk hG hc
  let B : ℝ := ((4*k*G+1:ℕ):ℝ)
  let K : ℝ := adaptiveAllowance k G c
  let γ := δ-B*c*θ
  have hγ : 0 < γ := sub_pos.mpr hmargin
  obtain ⟨n, hn⟩ := exists_nat_gt ((K+B*θ)/γ)
  obtain ⟨d, hd, hbound⟩ := hb (max (max d₀ 1) n)
  have hdn : (n:ℝ) ≤ d := by exact_mod_cast (le_max_right _ _).trans hd
  have hprod := (div_lt_iff₀ hγ).mp (lt_of_lt_of_le hn hdn)
  have hsave : K < (d:ℝ)*δ-B*θ*((c:ℝ)*d+1) := by
    dsimp [γ] at hprod
    nlinarith only [hprod]
  have hnonneg : 0 ≤ (d:ℝ)*δ-B*θ*((c:ℝ)*d+1) :=
    le_trans (by dsimp [K]; positivity) hsave.le
  have hbits : (1:ℝ) ≤ entryBits d := by
    exact_mod_cast (show 1 ≤ entryBits d by unfold entryBits; omega)
  have hpay := mul_le_mul_of_nonneg_right hbits hnonneg
  refine ⟨d, θ, δ, (le_max_left _ _).trans hd, hθ, hbound, ?_⟩
  change K < (entryBits d:ℝ)*((d:ℝ)*δ-B*θ*((c:ℝ)*d+1))
  linarith

/-- The conclusion is the original adaptive-machine predicate. This
criterion does not claim the full robust block conjecture. -/
theorem not_linearTimeTransposable_of_criterion
    (h : AdaptiveWholeRowCriterion) : ¬ LinearTimeTransposable := by
  rintro ⟨M, c, hM⟩
  obtain ⟨d, θ, δ, hd, hθ, hbound, hgap⟩ := h
    (M.k+1+(1+3)) (cellBits (bufTM M)) (2*c+4) (by omega)
    (cellBits_pos _) (by omega) (coarseSize M c)
  have hsize : coarseSize M c ≤ d := (le_max_left _ _).trans hd
  have hdpos : 1 ≤ d := (le_max_right _ _).trans hd
  obtain ⟨Dg, F, code, hDg, hT, hlarge, hsolve, hend⟩ :=
    codes_coentLinear_at hsize (hM d hdpos)
  have hbill := end_invoice hDg (cellBits_pos _) hdpos hT hend hθ
    (capProfile_profileCap Dg d (cellBits (bufTM M))) hlarge hsolve hbound
  have hk : M.k+1+(1+3)-4 = M.k+1 := by omega
  simp only [adaptiveAllowance, hk] at hgap
  have hdreal : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hstrict := mul_lt_mul_of_pos_left hgap hdreal
  push_cast at hbill
  nlinarith only [hbill, hstrict]

/-- Only symmetric reflexive helper relations and two-sided nonlinear codes
are tested. R is a reverse-degree cutoff, paid before the factor-two transfer.
It too may vary with the selected dimension. -/
def AdaptiveNormalizedCriterion : Prop :=
  ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c → ∀ d₀ : ℕ,
    ∃ (d R : ℕ) (θ δ : ℝ), max d₀ 1 ≤ d ∧ 0 < θ ∧
      NormalizedTwoSidedWholeRowCardinalityBound d (endWindow k G θ + R + 1)
        (Fin (entryBits d) → Bool) ((1-δ)*(d:ℝ)^2) ∧
      (adaptiveAllowance k G c:ℝ) <
        endSurplus k G c d θ ((δ-symmetryPayment (endWindow k G θ) R)/2)

theorem AdaptiveNormalizedCriterion.oneSided (h : AdaptiveNormalizedCriterion) :
    AdaptiveWholeRowCriterion := by
  intro k G c hk hG hc d₀
  obtain ⟨d, R, θ, δ, hd, hθ, hbound, hgap⟩ := h k G c hk hG hc d₀
  refine ⟨d, θ, (δ-symmetryPayment (endWindow k G θ) R)/2, hd, hθ, ?_, hgap⟩
  convert (hbound.twoSided (R := R) (by simp)).oneSided (by simp) using 1
  ring

theorem not_linearTimeTransposable_of_normalizedCriterion
    (h : AdaptiveNormalizedCriterion) : ¬ LinearTimeTransposable :=
  not_linearTimeTransposable_of_criterion h.oneSided

#print axioms endWindow
#print axioms endSurplus
#print axioms end_invoice
#print axioms adaptiveAllowance
#print axioms AdaptiveWholeRowCriterion
#print axioms criterion_of_fixedWindow
#print axioms not_linearTimeTransposable_of_criterion
#print axioms AdaptiveNormalizedCriterion
#print axioms AdaptiveNormalizedCriterion.oneSided
#print axioms not_linearTimeTransposable_of_normalizedCriterion

end LeanBacklog.BlockTCC

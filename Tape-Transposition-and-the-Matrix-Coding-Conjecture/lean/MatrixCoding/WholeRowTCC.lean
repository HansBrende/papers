import MatrixCoding.BlockCodeInvoice
import MatrixCoding.NormalizedRateTransfer
import Transpose.Tape.Statements.Coding

/-!
# A common whole-row deficit implies the robust Tape Coding Conjecture

The constants and helper window are fixed before the matrix size. The
network code may be nonlinear, nonuniform, and correct only on a set of
co-entropy O(d * entryBits d). The conclusion is the first paper's actual
robust block conjecture; its existing consumer excludes adaptive machines.
The positive whole-row deficit remains an explicit, open hypothesis.
-/

namespace LeanBacklog.BlockTCC

open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth
open RowSpread

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem robustNoCode_of_commonDeficit {δ : ℝ} (hδ : 0 < δ)
    (hbound : UniformWholeRowRateCanonicalBits (1 - δ)) : RobustNoCode_TM := by
  intro k G c C₀ hG
  let ε : ℝ := δ / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * ((c:ℝ)*G+1) / ε)
  have hMbudget : 2 * ((c:ℝ)*G+1) ≤ ε * M := by
    have := (div_lt_iff₀ hε).mp hM
    nlinarith
  have hMpos : (0:ℝ) < M := by
    by_contra hn
    have := mul_nonpos_of_nonneg_of_nonpos hε.le (not_lt.mp hn)
    nlinarith [show (0:ℝ) ≤ (c:ℝ)*G by positivity]
  let Q : ℕ := (4*k+1)*G*(c+1)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  let θ : ℝ := ε / Q
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθeq : ((4*k+1:ℕ):ℝ) * G * θ * ((c:ℝ)+1) = ε := by
    have he : (Q:ℝ) * θ = ε := by dsimp [θ]; exact mul_div_cancel₀ ε (by positivity)
    dsimp [Q] at he
    push_cast at he ⊢
    nlinarith only [he]
  let D := blockDepth k θ
  let w := M * (2 * (2*k+3)^D)
  obtain ⟨d₀, hd₀⟩ := hbound w ε hε
  obtain ⟨d₁, hd₁⟩ := exists_nat_gt ((C₀:ℝ) / ε)
  refine ⟨max d₀ (max d₁ 1), ?_⟩
  intro d hd Dg hDg hT F hlarge code hsolve
  have hdpos : 1 ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hd
  have hdreal : (1:ℝ) ≤ d := by exact_mod_cast hdpos
  let b := entryBits d
  let r := TSDiagram.blockSize G d
  let N := Dg.nodes r
  have hb : 1 ≤ b := by dsimp [b, entryBits]; omega
  have hL : 1 ≤ d*d*b := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hW : 0 < d*b := by positivity
  have hLreal : (0:ℝ) < (d*d*b : ℕ) := by exact_mod_cast hL
  have hr : 1 ≤ r := one_le_blockSize hG hdpos
  have hrW : r ≤ d*b := blockSize_le hG
  have hrL : r ≤ d*d*b := hrW.trans (by nlinarith)
  have hNr : (N:ℝ)*r ≤ ((c:ℝ)+1)*(d*d*b : ℕ) := by
    have hNr' : N*r ≤ Dg.T + r := (nodes_mul_le r).trans (Nat.sub_le _ _)
    have ht : Dg.T + r ≤ (c+1)*(d*d*b) := by nlinarith [hT, hrL]
    exact_mod_cast hNr'.trans ht
  have hN : 1 ≤ N := by
    have ht := one_le_T hDg hL
    have hnr := T_le_nodes_mul (D := Dg) hr
    dsimp only [N]
    nlinarith
  have hNupper : (N:ℝ) ≤ ((c:ℝ)*G+1)*d :=
    Transpose.Tape.numSlots_le_of hdpos (blockSize_mul_ge hG) (by exact_mod_cast hT)
  obtain ⟨Γ, rank, _, hΓ, hrank_le, hrank⟩ :=
    exists_block_cut Dg (fun t => (hDg.1 t).2) hr hN hθ
  have hinvoice := robust_invoice hDg hG hdpos Γ rank hrank_le hrank
    (capProfile_profileCap Dg d G) hlarge hsolve
    (hd₀ d (le_trans (le_max_left _ _) hd))
  have hcut : (((4*k+1)*(r*G)*Γ.card : ℕ):ℝ) ≤ ε*(d*d*b : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_left hΓ
      (show (0:ℝ) ≤ ((4*k+1:ℕ):ℝ)*G*r by positivity)
    have hmul' := mul_le_mul_of_nonneg_left hNr
      (show (0:ℝ) ≤ ((4*k+1:ℕ):ℝ)*G*θ by positivity)
    have he : (((4*k+1:ℕ):ℝ)*G*θ) * (((c:ℝ)+1)*(d*d*b : ℕ)) =
        ε*(d*d*b : ℕ) := by rw [← mul_assoc, hθeq]
    push_cast at hmul hmul' he ⊢
    nlinarith only [hmul, hmul', he]
  let E := badOutputRows Dg d b r M
  have hE : (E.card:ℝ) ≤ ε*d := by
    have he : (M:ℝ)*E.card ≤ 2*N := by
      exact_mod_cast badOutputRows_bill hDg hr hrW hW M
    have hm := mul_le_mul_of_nonneg_right hMbudget (show (0:ℝ) ≤ d by positivity)
    have he' : (M:ℝ)*E.card ≤ (M:ℝ)*(ε*d) := by nlinarith only [he, hNupper, hm]
    exact (mul_le_mul_iff_right₀ hMpos).mp he'
  have hEbill : ((d*E.card*b : ℕ):ℝ) ≤ ε*(d*d*b : ℕ) := by
    have := mul_le_mul_of_nonneg_left hE (show (0:ℝ) ≤ d*b by positivity)
    push_cast at this ⊢
    nlinarith only [this]
  have hCo : (C₀:ℝ) ≤ ε*d := by
    have hd' : (d₁:ℝ) ≤ d := by
      exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hd
    have h := (div_lt_iff₀ hε).mp hd₁
    nlinarith
  have hCobill : ((C₀*d*b : ℕ):ℝ) ≤ ε*(d*d*b : ℕ) := by
    have := mul_le_mul_of_nonneg_right hCo (show (0:ℝ) ≤ d*b by positivity)
    push_cast at this ⊢
    nlinarith only [this]
  change (d*d*b : ℕ) ≤ (C₀*d*b : ℕ) +
    ((4*k+1)*(r*G)*Γ.card : ℕ) + (d*E.card*b : ℕ) +
    (b:ℝ)*((1-δ+ε)*(d:ℝ)^2) at hinvoice
  have htotal : (d*d*b : ℕ) ≤ 3*ε*(d*d*b : ℕ) +
      (b:ℝ)*((1-δ+ε)*(d:ℝ)^2) := by linarith
  have hδL : 0 < δ*(d*d*b : ℕ) := mul_pos hδ hLreal
  dsimp only [ε] at htotal
  push_cast at htotal hδL
  nlinarith only [htotal, hδL]

/-- The plain all-input block conjecture follows from the robust one. -/
theorem noCode_of_commonDeficit {δ : ℝ} (hδ : 0 < δ)
    (hbound : UniformWholeRowRateCanonicalBits (1 - δ)) : NoCode_TM :=
  Transpose.Tape.noCode_of_robustNoCode (robustNoCode_of_commonDeficit hδ hbound)

/-- This is the frozen adaptive-machine target, not just oblivious motion. -/
theorem not_linearTimeTransposable_of_commonDeficit {δ : ℝ} (hδ : 0 < δ)
    (hbound : UniformWholeRowRateCanonicalBits (1 - δ)) : ¬ LinearTimeTransposable :=
  Transpose.Tape.not_linearTimeTransposable_of_robustNoCode
    (robustNoCode_of_commonDeficit hδ hbound)

/-- The previously checked symmetric, reflexive, two-sided normalization
can be used unchanged, with its factor-two loss in the positive deficit. -/
theorem robustNoCode_of_normalizedTwoSidedDeficit {δ : ℝ} (hδ : 0 < δ)
    (hbound : UniformNormalizedTwoSidedWholeRowRateCanonicalBits (1 - δ)) :
    RobustNoCode_TM := by
  apply robustNoCode_of_commonDeficit (δ := δ/2) (by positivity)
  convert hbound.oneSided using 1; ring

#print axioms robustNoCode_of_commonDeficit
#print axioms noCode_of_commonDeficit
#print axioms not_linearTimeTransposable_of_commonDeficit
#print axioms robustNoCode_of_normalizedTwoSidedDeficit

end LeanBacklog.BlockTCC

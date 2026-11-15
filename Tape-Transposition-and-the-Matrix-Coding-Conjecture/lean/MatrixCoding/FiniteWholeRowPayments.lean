import MatrixCoding.WeakWholeRowTCC

/-!
# Integer cut and normalization payments

The final wall target uses these finite payments instead of their previous
real envelopes. No capacity assertion is made in this module.
-/

namespace LeanBacklog.BlockTCC

open Finset Transpose Transpose.Tape Transpose.Tape.Impl
open RowSpread LeanMachine.SymmetricHelpers

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Maximum number of grain slots under T ≤ cL, including the final partial slot. -/
def slotBound (G c d : ℕ) : ℕ :=
  numSlots (TSDiagram.blockSize G d) (c*(d*d*entryBits d))

/-- Integral capacity invoice for the cut provided at density θ. -/
noncomputable def cutBudget (k G c d : ℕ) (θ : ℝ) : ℕ :=
  (4*k*G+1)*TSDiagram.blockSize G d*⌊θ*(slotBound G c d:ℝ)⌋₊

theorem cut_price_le_budget {k G c d : ℕ} {Dg : TSDiagram k} {θ : ℝ}
    (hθ : 0 ≤ θ) (hT : Dg.T ≤ c*(d*d*entryBits d)) (Γ : Finset ℕ)
    (hΓ : (Γ.card:ℝ) ≤ θ*Dg.nodes (TSDiagram.blockSize G d)) :
    (4*k*G+1)*TSDiagram.blockSize G d*Γ.card ≤ cutBudget k G c d θ := by
  have hN : Dg.nodes (TSDiagram.blockSize G d) ≤ slotBound G c d :=
    numSlots_mono _ hT
  have hN' : (Dg.nodes (TSDiagram.blockSize G d):ℝ) ≤ slotBound G c d := by
    exact_mod_cast hN
  exact Nat.mul_le_mul_left _ (Nat.le_floor (hΓ.trans (mul_le_mul_of_nonneg_left hN' hθ)))

/-- The integer bill improves the earlier envelope, uniformly in the parameters. -/
theorem cutBudget_le_envelope {k G c d : ℕ} {θ : ℝ}
    (hG : 1 ≤ G) (hθ : 0 ≤ θ) :
    (cutBudget k G c d θ:ℝ) ≤
      ((4*k*G+1:ℕ):ℝ)*θ*((c:ℝ)*(d*d*entryBits d:ℕ)+d*entryBits d) := by
  let r := TSDiagram.blockSize G d
  have hslot : slotBound G c d*r ≤ c*(d*d*entryBits d)+d*entryBits d := by
    calc
      _ ≤ c*(d*d*entryBits d)+r-1 := Nat.div_mul_le_self _ _
      _ ≤ c*(d*d*entryBits d)+r := Nat.sub_le _ _
      _ ≤ _ := Nat.add_le_add_left (blockSize_le hG) _
  have hs : (slotBound G c d:ℝ)*r ≤ (c:ℝ)*(d*d*entryBits d:ℕ)+d*entryBits d := by
    exact_mod_cast hslot
  have hf := Nat.floor_le (show 0 ≤ θ*(slotBound G c d:ℝ) by positivity)
  have hf' := mul_le_mul_of_nonneg_left hf
    (show (0:ℝ) ≤ ((4*k*G+1:ℕ):ℝ)*r by positivity)
  have hs' := mul_le_mul_of_nonneg_left hs
    (show (0:ℝ) ≤ ((4*k*G+1:ℕ):ℝ)*θ by positivity)
  change (((4*k*G+1)*r*⌊θ*(slotBound G c d:ℝ)⌋₊:ℕ):ℝ) ≤ _
  push_cast at hf' hs' ⊢
  nlinarith only [hf', hs']

/-- Heavy helpers are absent at R≥d; otherwise use the integral incidence budget. -/
def heavyBound (d w R : ℕ) : ℕ :=
  if d ≤ R then 0 else min d (w*d/(R+1))

/-- Exact size of the row/column cross at the maximum possible heavy count. -/
def crossBudget (d w R : ℕ) : ℕ :=
  2*d*heavyBound d w R - (heavyBound d w R)^2

theorem heavyBound_le_dim (d w R : ℕ) : heavyBound d w R ≤ d := by
  unfold heavyBound
  split_ifs <;> omega

theorem heavyBound_incidence (d w R : ℕ) : heavyBound d w R*(R+1) ≤ w*d := by
  unfold heavyBound
  split_ifs
  · simp
  · exact (Nat.mul_le_mul_right (R+1) (min_le_right _ _)).trans (Nat.div_mul_le_self _ _)

theorem heavy_card_le_bound {d w R : ℕ} (ρ : Fin d → Finset (Fin d))
    (hwidth : ∀ j, (ρ j).card ≤ w) : (heavyHelpers ρ R).card ≤ heavyBound d w R := by
  classical
  unfold heavyBound
  split_ifs with hR
  · have he : heavyHelpers ρ R = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hrev : (reverseHelpers ρ j).card ≤ d := by simpa using card_le_univ (reverseHelpers ρ j)
      have := (mem_heavyHelpers ρ R j).mp hj
      omega
    simp [he]
  · apply le_min
    · simpa using card_le_univ (heavyHelpers ρ R)
    · apply (Nat.le_div_iff_mul_le (by omega)).mpr
      simpa using heavyHelpers_card_mul_succ_le ρ w R hwidth

theorem crossBudget_add_square (d w R : ℕ) :
    crossBudget d w R + (heavyBound d w R)^2 = 2*d*heavyBound d w R := by
  unfold crossBudget
  apply Nat.sub_add_cancel
  have h := heavyBound_le_dim d w R
  nlinarith

theorem fixedCross_card_le_budget {d w R : ℕ} (ρ : Fin d → Finset (Fin d))
    (hwidth : ∀ j, (ρ j).card ≤ w) :
    (fixedCross (heavyHelpers ρ R)).card ≤ crossBudget d w R := by
  have hH := heavy_card_le_bound ρ hwidth (R := R)
  have hh := heavyBound_le_dim d w R
  have he := fixedCross_card_add_square (heavyHelpers ρ R)
  simp only [Fintype.card_fin] at he
  have hb := crossBudget_add_square d w R
  have hmul := Nat.mul_le_mul_left (heavyBound d w R - (heavyHelpers ρ R).card)
    (show heavyBound d w R + (heavyHelpers ρ R).card ≤ 2*d by omega)
  have hsub := Nat.sub_add_cancel hH
  nlinarith only [he, hb, hmul, hsub]

theorem crossBudget_le_envelope (d w R : ℕ) :
    (crossBudget d w R:ℝ) ≤ symmetryPayment w R*(d:ℝ)^2 := by
  have he := crossBudget_add_square d w R
  have hi := heavyBound_incidence d w R
  have hc : (crossBudget d w R:ℝ) ≤ 2*(d:ℝ)*heavyBound d w R := by
    exact_mod_cast (show crossBudget d w R ≤ 2*d*heavyBound d w R by omega)
  have hi' : (heavyBound d w R:ℝ)*((R:ℝ)+1) ≤ (w:ℝ)*d := by exact_mod_cast hi
  have hR : (0:ℝ) < (R:ℝ)+1 := by positivity
  rw [symmetryPayment, div_mul_eq_mul_div, le_div_iff₀ hR]
  have hc' := mul_le_mul_of_nonneg_right hc hR.le
  have hi'' := mul_le_mul_of_nonneg_left hi' (show (0:ℝ) ≤ 2*d by positivity)
  nlinarith only [hc', hi'']

/-- Paid symmetry with the exact finite cross envelope. -/
theorem normalized_bound_finite {d w R : ℕ} {α : Type*} [Fintype α] {a : ℝ}
    (h : NormalizedTwoSidedWholeRowCardinalityBound d (w+R+1) α a)
    (hα : 0 < Fintype.card α) :
    TwoSidedWholeRowCardinalityBound d w α (a+(crossBudget d w R:ℕ)) := by
  intro ρ C hwidth hC
  have hcount := twoSided_card_le_of_fixedCross ρ C hC (heavyHelpers ρ R)
    ((Fintype.card α:ℝ)^a) (fun D hD =>
      h _ D (normalizedHelpers_card_le ρ w R hwidth)
        (normalizedHelpers_symmetric ρ _) (normalizedHelpers_reflexive ρ _) hD)
  have hq : (0:ℝ) < Fintype.card α := by exact_mod_cast hα
  have hq1 : (1:ℝ) ≤ Fintype.card α := by exact_mod_cast (show 1 ≤ Fintype.card α by omega)
  calc
    (C.card:ℝ) ≤ (Fintype.card α:ℝ)^(fixedCross (heavyHelpers ρ R)).card *
      (Fintype.card α:ℝ)^a := hcount
    _ = (Fintype.card α:ℝ)^(((fixedCross (heavyHelpers ρ R)).card:ℝ)+a) := by
      rw [Real.rpow_add hq, Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq1 (by
      have hp : ((fixedCross (heavyHelpers ρ R)).card:ℝ) ≤ crossBudget d w R := by
        exact_mod_cast fixedCross_card_le_budget ρ hwidth
      linarith)

/-- The finite output-at-end invoice keeps the integral cut bill. -/
theorem end_invoice_finite {k d G c coent : ℕ} {Dg : TSDiagram k} {θ a : ℝ}
    (hDg : Dg.Valid (d*d*entryBits d)) (hG : 1 ≤ G) (hd : 1 ≤ d)
    (hT : Dg.T ≤ c*(d*d*entryBits d))
    (hend : ∀ t ≤ Dg.T, Dg.out t = d*d*entryBits d - (Dg.T-t))
    (hθ : 0 < θ) {cap : ℕ × ℕ → ℕ} (hcap : Dg.CapProfile d G cap)
    {F : Set (Fin (d*d*entryBits d) → Bool)} {code : NetCode}
    (hlarge : 2^(d*d*entryBits d) ≤ 2^coent*F.ncard)
    (hsolve : Dg.Solves d G cap F code)
    (hbound : WholeRowCardinalityBound d (endWindow k G θ)
      (Fin (entryBits d) → Bool) a) :
    (d*d*entryBits d:ℕ) ≤ (coent:ℕ)+(cutBudget k G c d θ:ℕ)+(entryBits d:ℝ)*a := by
  let r := TSDiagram.blockSize G d
  have hb : 1 ≤ entryBits d := by unfold entryBits; omega
  have hL : 1 ≤ d*d*entryBits d := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hW : 0 < d*entryBits d := by positivity
  have hr : 1 ≤ r := one_le_blockSize hG hd
  have hN : 1 ≤ Dg.nodes r := by
    have ht := one_le_T hDg hL
    have hnr := T_le_nodes_mul (D := Dg) hr
    nlinarith
  obtain ⟨Γ, rank, _, hΓ, hrank_le, hrank⟩ :=
    exists_block_cut Dg (fun t => (hDg.1 t).2) hr hN hθ
  have hinvoice := robust_invoice_sharp (M := G+1) hDg hG hd Γ rank hrank_le hrank
    hcap hlarge hsolve hbound
  have hE := badOutputRows_atEnd_eq_empty hDg hr hW (blockSize_mul_ge hG) hend
  change badOutputRows Dg d (entryBits d) (TSDiagram.blockSize G d) (G+1) = ∅ at hE
  simp only [hE, card_empty, Nat.mul_zero, Nat.zero_mul, Nat.cast_zero, add_zero] at hinvoice
  have hp : (((4*k*G+1)*r*Γ.card:ℕ):ℝ) ≤ cutBudget k G c d θ := by
    exact_mod_cast cut_price_le_budget hθ.le hT Γ hΓ
  linarith

#print axioms slotBound
#print axioms cutBudget
#print axioms cut_price_le_budget
#print axioms cutBudget_le_envelope
#print axioms heavyBound
#print axioms crossBudget
#print axioms heavyBound_le_dim
#print axioms heavyBound_incidence
#print axioms heavy_card_le_bound
#print axioms crossBudget_add_square
#print axioms fixedCross_card_le_budget
#print axioms crossBudget_le_envelope
#print axioms normalized_bound_finite
#print axioms end_invoice_finite

end LeanBacklog.BlockTCC

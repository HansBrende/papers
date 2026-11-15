import BlockCodeTransfer

/-!
# The robust block-code invoice

The input set can have positive co-entropy and the code can be arbitrary
and nonlinear. Only its values on the solving set enter the observation
count. The exceptional input columns (transposed output rows) are paid in the
canonical alphabet.
-/

namespace LeanBacklog.BlockTCC

open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth
open RowSpread TapeStorageRates.PaidInputs
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The exact cut-output price is one bit per output, not G bits. -/
theorem robust_invoice_sharp {k d G D M coent : ℕ} {Dg : TSDiagram k} {a : ℝ}
    (hDg : Dg.Valid (d * d * entryBits d)) (hG : 1 ≤ G) (hd : 1 ≤ d)
    (Γ : Finset ℕ) (rank : ℕ → ℕ)
    (hrank_le : ∀ v, rank v ≤ D)
    (hrank : ∀ e ∈ Dg.edges (TSDiagram.blockSize G d),
      e.1 ∉ Γ → e.2 ∉ Γ → rank e.1 < rank e.2)
    {cap : ℕ × ℕ → ℕ} (hcap : Dg.CapProfile d G cap)
    {F : Set (Fin (d * d * entryBits d) → Bool)} {code : NetCode}
    (hlarge : 2 ^ (d * d * entryBits d) ≤ 2 ^ (coent) * F.ncard)
    (hsolve : Dg.Solves d G cap F code)
    (hbound : WholeRowCardinalityBound d (M * (2 * (2 * k + 3) ^ D))
      (Fin (entryBits d) → Bool) a) :
    (d * d * entryBits d : ℕ) ≤ (coent : ℕ) +
      ((4 * k * G + 1) * TSDiagram.blockSize G d * Γ.card : ℕ) +
      (d * (badOutputRows Dg d (entryBits d) (TSDiagram.blockSize G d) M).card * entryBits d : ℕ) +
      (entryBits d : ℝ) * a := by
  classical
  let b := entryBits d
  let r := TSDiagram.blockSize G d
  let E := badOutputRows Dg d b r M
  let ρ := blockHelpers Dg d b r D M
  let obs := observe Dg d b r cap Γ code
  let m := (∑ e ∈ cutEdges Dg r Γ, cap e) + (cutOutputs Dg (d*d*b) r Γ).card
  let A : ℝ := (Fintype.card (Fin b → Bool) : ℝ) ^ (d * E.card) *
    (Fintype.card (Fin b → Bool) : ℝ) ^ a
  have hr : 1 ≤ r := one_le_blockSize hG hd
  have hwidth : ∀ j, (ρ j).card ≤ M * (2 * (2 * k + 3) ^ D) :=
    card_blockHelpers hDg hr (blockSize_le hG) D M
  have hcount := card_le_of_real_fibre_bound F.toFinset obs A (fun z => ?_)
  · have hp : (2 : ℝ) ^ (d*d*b : ℕ) ≤
        (2 : ℝ) ^ (coent : ℕ) * ((2 : ℝ)^m *
          (((2 : ℝ)^b)^(d*E.card) * ((2 : ℝ)^b)^a)) := by
      have hlarge' : (2 : ℝ) ^ (d*d*b : ℕ) ≤
          (2 : ℝ) ^ (coent : ℕ) * (F.toFinset.card : ℝ) := by
        exact_mod_cast (show 2 ^ (d*d*b) ≤ 2 ^ (coent) * F.toFinset.card by
          simpa only [Set.ncard_eq_toFinset_card'] using hlarge)
      apply hlarge'.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [card_blockRecord, m, A, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat] using hcount
    have hexp : (d*d*b : ℕ) ≤ (coent : ℕ) + (m : ℝ) +
        (d*E.card*b : ℕ) + (b:ℝ)*a := by
      apply (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp
      convert hp using 1 <;> simp only [Real.rpow_add (by norm_num : (0:ℝ) < 2),
        Real.rpow_natCast, Nat.cast_mul, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      <;> ring
    have hm : m ≤ (4*k*G+1)*r*Γ.card := by
      have he := cut_edge_price hDg hr hcap Γ
      have ho := card_cut_outputs hDg hr Γ
      change (cutOutputs Dg (d*d*b) r Γ).card ≤ r * Γ.card at ho
      change (∑ e ∈ cutEdges Dg r Γ, cap e) ≤ 4*k*(r*G)*Γ.card at he
      dsimp only [m]
      nlinarith
    have hm' : (m:ℝ) ≤ ((4*k*G+1)*r*Γ.card : ℕ) := by exact_mod_cast hm
    change (d*d*b : ℕ) ≤ (coent : ℕ) +
      ((4*k*G+1)*r*Γ.card : ℕ) + (d*E.card*b : ℕ) + (b:ℝ)*a
    linarith
  · let C := F.toFinset.filter fun x => obs x = z
    have hCF : ∀ x ∈ C, x ∈ F := fun x hx => Set.mem_toFinset.mp (mem_filter.mp hx).1
    have hf (x) (hx : x ∈ C) : obs x = z := (mem_filter.mp hx).2
    have hcode := fibre_wholeRow (M := M) hDg hr Γ rank hrank_le hrank hsolve C hCF
      (fun x hx y hy => (hf x hx).trans (hf y hy).symm)
    have hh := hbound.except ρ E (C.image entryWord) hwidth hcode
    simpa only [card_image_of_injective C entryWord_injective] using hh

/-- The original, slightly coarser invoice remains available. -/
theorem robust_invoice {k d G D M coent : ℕ} {Dg : TSDiagram k} {a : ℝ}
    (hDg : Dg.Valid (d * d * entryBits d)) (hG : 1 ≤ G) (hd : 1 ≤ d)
    (Γ : Finset ℕ) (rank : ℕ → ℕ)
    (hrank_le : ∀ v, rank v ≤ D)
    (hrank : ∀ e ∈ Dg.edges (TSDiagram.blockSize G d),
      e.1 ∉ Γ → e.2 ∉ Γ → rank e.1 < rank e.2)
    {cap : ℕ × ℕ → ℕ} (hcap : Dg.CapProfile d G cap)
    {F : Set (Fin (d * d * entryBits d) → Bool)} {code : NetCode}
    (hlarge : 2 ^ (d * d * entryBits d) ≤ 2 ^ coent * F.ncard)
    (hsolve : Dg.Solves d G cap F code)
    (hbound : WholeRowCardinalityBound d (M * (2 * (2 * k + 3) ^ D))
      (Fin (entryBits d) → Bool) a) :
    (d * d * entryBits d : ℕ) ≤ (coent : ℕ) +
      ((4 * k + 1) * (TSDiagram.blockSize G d * G) * Γ.card : ℕ) +
      (d * (badOutputRows Dg d (entryBits d) (TSDiagram.blockSize G d) M).card * entryBits d : ℕ) +
      (entryBits d : ℝ) * a := by
  have h := robust_invoice_sharp hDg hG hd Γ rank hrank_le hrank hcap hlarge hsolve hbound
  have hprice : (4*k*G+1)*TSDiagram.blockSize G d*Γ.card ≤
      (4*k+1)*(TSDiagram.blockSize G d*G)*Γ.card := by
    nlinarith [Nat.mul_le_mul_left (TSDiagram.blockSize G d*Γ.card) hG]
  have hprice' : (((4*k*G+1)*TSDiagram.blockSize G d*Γ.card:ℕ):ℝ) ≤
      ((4*k+1)*(TSDiagram.blockSize G d*G)*Γ.card:ℕ) := by exact_mod_cast hprice
  linarith

#print axioms robust_invoice_sharp
#print axioms robust_invoice

end LeanBacklog.BlockTCC

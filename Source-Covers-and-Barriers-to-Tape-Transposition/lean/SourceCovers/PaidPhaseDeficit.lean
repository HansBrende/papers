import SourceCovers.PaidBankRecovery
import SourceCovers.PaidSourceGeometry
import SourceCovers.PaidSourceBank

set_option autoImplicit false

/-!
# The full paid bound for one actual rank phase

The complete bank, original selected dependencies, initial paid lowers,
residual boundary load, and variation bound are derived from the actual
family geometry. Geometric credit may be any lower bound on its raw gaps.
-/

namespace SourceCovers

open Classical Finset BoundedNesting LeanMachine LeanMachine.SourceBank
open Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators
noncomputable section

/-- Gap area depends on the finite source set, not its nonemptiness witness. -/
theorem rawGapArea_congr (L : ℕ) {S S' : Finset ℕ}
    (hS : S.Nonempty) (hS' : S'.Nonempty) (heq : S = S') :
    GapErosion.pointArea (range S.card) (CyclicSelection.gap L S hS) L =
      GapErosion.pointArea (range S'.card) (CyclicSelection.gap L S' hS') L := by
  subst S'
  rfl

variable {k T d b M ρ w N a : ℕ} {xs : Fin k → ℕ → ℤ}
    {K : Finset (ActualFamily xs T)}
    (hc : HasSpanColoring K 2) (hM : 2 ≤ M) (hρ : ρ < M)
    (E : Finset (ActualFamily xs T))
    (hwalk : ∀ h, IsWalk (xs h))
    (hcolor : HasSpanColoring (univ : Finset (ActualFamily xs T)) N)
    (hsize : ∀ G : ActualFamily xs T, G ∉ K ∪ E → G.hops.card ≤ a)
    {Record : Type*} [Fintype Record]
    {C : Finset (Fin (d * d * b) → Bool)}
    {record : (Fin (d * d * b) → Bool) → ℕ → Record}
    {output : ℕ → Record → Bool} {β : ℝ} {x t : ℕ → ℕ}
    (hd : 0 < d) (hb : 0 < b) (hw : 0 < w)
    (hx : ∀ s ≤ T - 1, x s < d * d * b)
    (ht : StrictMonoOn t (Set.Iio (d * d * b)))
    (hn : ∀ r < d * d * b, t r ≤ T - 1)
    (hC : C.Nonempty)
    (hR : Real.log (Fintype.card Record : ℝ) / Real.log 2 ≤ β)
    (hlocal : CausalRecovery.LocallyDetermined (actualParents xs T) (fun s => {x s})
      (T - 1) (C : Set (Fin (d * d * b) → Bool)) zbit record)
    (hcorrect : ∀ z ∈ C, ∀ i : Fin (d * d * b),
      output (tpos d b i.val) (record z (t (tpos d b i.val))) = z i)
    (Hcredit : ℕ → ℝ)
    (hcredit : ∀ j < d,
      let S := rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x
        (columnFirst t (d * b) j)
      Hcredit j ≤ GapErosion.pointArea (range S.card)
        (CyclicSelection.gap (d * d * b) S
          ⟨x (columnFirst t (d * b) j), exactSourceBank_raw_root hc hM hρ E x _⟩)
        (d * d * b))

include hc hM hρ hwalk hcolor hsize hd hb hw hx ht hn hC hR hlocal hcorrect hcredit

/-- The stronger one-phase bound retains the actual complete-bank variation.
Every dependency and paid time comes from the actual family geometry. -/
theorem phase_paid_deficit_variation :
    let V := cost (exactSourceBank (ρ := ρ) hc hM E) (fun s => (x s : ℝ)) (T - 1)
    (d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2 ≥
      (d : ℝ) * b * (∑ j ∈ range d, Hcredit j) -
        2 * V / d - 2 * ((w : ℝ) - 1) - ((d : ℝ) * b - b + 1) / 2 -
        β * ((initialPayment K E M ρ).card + ((1 + N * a : ℕ) : ℝ) * V / w) := by
  let B := exactSourceBank (ρ := ρ) hc hM E
  let Y := indexedRawBank B x
  let : Nonempty (Fin B.length) := exactSourceBank_nonempty hc hM hρ E
  have hselected : ∀ v ≤ T - 1, ∀ u ∈ actualParents xs T v,
      u ∈ selectedParents K E v → u ∉ initialPayment K E M ρ →
      residualBankValues Y u ⊆ residualBankValues Y v := by
    intro v _ u _ hu hunpaid
    simpa only [Y, indexedRawBank_values, B] using
      initial_selected_raw_values_closed hc hM hρ E hwalk hu hunpaid x
  have hH : ∀ e < T - 1,
      ((ResidualGeometry.live
        (residualParents (actualParents xs T) (selectedParents K E))
        (T - 1) (initialPayment K E M ρ) e).card : ℝ) ≤ ((1 + N * a : ℕ) : ℝ) := by
    intro e _
    exact_mod_cast residual_live_card_le K E hcolor hsize
      (T - 1) (initialPayment K E M ρ) e
  obtain ⟨_, _, _, hdef⟩ := exists_paidBank_deficit
    hd hb hw ht hn (indexedRawBank_range hc hM hρ E x hx) hC hR
    (fun _ _ _ hu => actualParents_earlier hu) hselected
    (fun s _ => indexedRawBank_root hc hM hρ E x s) hlocal hcorrect hH
  have hcredit' : ∀ j < d, Hcredit j ≤ frozenArea Y t d b j := by
    intro j hj
    apply (hcredit j hj).trans_eq
    exact rawGapArea_congr _ _ _ (indexedRawBank_values B x _).symm
  have hsum := mul_le_mul_of_nonneg_left
    (sum_le_sum (fun j hj => hcredit' j (mem_range.mp hj)))
    (show (0 : ℝ) ≤ d * b by positivity)
  simp only [indexedRawBank_variation, B] at hdef
  dsimp only
  linarith

/-- The manuscript's one-phase paid bound, with the explicit source-bank
constant and the sharper cyclic stripe error. -/
theorem phase_paid_deficit {q : ℕ} (hE : E.card ≤ q)
    (hunit : ∀ e < T - 1, dist (x e : ℝ) (x (e + 1) : ℝ) ≤ 1) :
    (d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2 ≥
      (d : ℝ) * b * (∑ j ∈ range d, Hcredit j) -
        2 * ((bankCost M q : ℝ) * ((T - 1 : ℕ) : ℝ)) / d -
        2 * ((w : ℝ) - 1) - ((d : ℝ) * b - b + 1) / 2 -
        β * ((initialPayment K E M ρ).card +
          ((1 + N * a : ℕ) : ℝ) * ((bankCost M q : ℝ) * ((T - 1 : ℕ) : ℝ)) / w) := by
  have hdef := phase_paid_deficit_variation hc hM hρ E hwalk hcolor hsize
    hd hb hw hx ht hn hC hR hlocal hcorrect Hcredit hcredit
  dsimp only at hdef
  have hV := exactSourceBank_raw_variation hc hM hρ E hE (fun s => (x s : ℝ)) hunit
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hV (by norm_num : (0 : ℝ) ≤ 2)) (Nat.cast_nonneg d)
  have hg := mul_le_mul_of_nonneg_left
    (add_le_add_left (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg (1 + N * a)))
      (Nat.cast_nonneg w)) ((initialPayment K E M ρ).card : ℝ))
    (recordCapacity_nonneg hR)
  linarith

end
end SourceCovers

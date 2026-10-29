import SourceCovers.SharedSupport
import SourceCovers.PaidSharedRecovery
import SourceCovers.OrbitCountDeficit

set_option autoImplicit false

/-! Global shared support is paid once. Full two-exception residual recovery
is retained while one-exception source geometry supplies the gap credit. -/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.SourceBank Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K : Finset (ActualFamily xs T)}

private theorem olderBank_gap (hc : HasSpanColoring K 2) {M ρ d b r : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T))
    (x t : ℕ → ℕ) (hd : 0 < d) (hb : 0 < b)
    (hn : ∀ z < d * d * b, t z < T) (hx : ∀ s ≤ T - 1, x s < d * d * b)
    (D : Finset (CoreFamily K)) (hD : D.card ≤ r) {α : ℝ}
    (hV : (∑ G ∈ univ \ D, ∑ e ∈ G.val.edges,
      dist (x e : ℝ) (x (e + 1) : ℝ)) ≤ α * (d * d * b))
    {j : ℕ} (hj : j < d)
    [Nonempty (Fin (exactSourceBank (ρ := ρ) hc hM (olderException E).toList.toFinset).length)] :
    max (1 - α) 0 ^ 2 / (2 * (2 * (r : ℝ) + 1) * (2 * (M : ℝ) + 4)) ≤
      frozenArea (indexedRawBank (exactSourceBank (ρ := ρ) hc hM
        (olderException E).toList.toFinset) x) t d b j := by
  have hg := phaseCoreCover_gap hc hM hρ (olderException E).toList.toFinset
    x t hd hb hn hx D hD hV hj
  have hκ := (fractionalCoreCover_exactSourceBank_bounds hc hM hρ
    (olderException E).toList.toFinset x (hn _
      ((column_indices hd hb hj).1.trans_lt (column_indices hd hb hj).2))).2
  have hk : phaseCoreCover hc hM (olderException E).toList.toFinset x t d b ρ j ≤
      2 * (M : ℝ) + 4 := by
    apply hκ.2.trans
    have hcard : (olderException E).toList.toFinset.card ≤ 1 := by
      cases olderException E <;> simp
    exact_mod_cast (show (2 * M + 4) ^ (olderException E).toList.toFinset.card ≤
        2 * M + 4 from by
      simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1 ≤ 2 * M + 4) hcard)
  have hden : 0 < 2 * (2 * (r : ℝ) + 1) *
      phaseCoreCover hc hM (olderException E).toList.toFinset x t d b ρ j :=
    mul_pos (by positivity) (lt_of_lt_of_le zero_lt_one hκ.1)
  have h := (div_le_div_of_nonneg_left (sq_nonneg _) hden
    (mul_le_mul_of_nonneg_left hk (by positivity))).trans hg
  apply h.trans_eq
  exact rawGapArea_congr _ _ _ (indexedRawBank_values _ _ _).symm

section Phase

variable (hc : HasSpanColoring K 2) {M ρ d b w r N a : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) (hE : E.card ≤ 2)
    (hwalk : ∀ h, BoundedNesting.IsWalk (xs h))
    (hcolor : HasSpanColoring (univ : Finset (ActualFamily xs T)) N)
    (hsize : ∀ G : ActualFamily xs T, G ∉ K ∪ E → G.hops.card ≤ a)
    (x t : ℕ → ℕ) (hd : 0 < d) (hb : 0 < b) (hw : 0 < w)
    (ht : StrictMonoOn t (Set.Iio (d * d * b)))
    (hn : ∀ z < d * d * b, t z < T)
    (hx : ∀ s ≤ T - 1, x s < d * d * b)
    (hstep : ∀ e < T - 1, dist (x e : ℝ) (x (e + 1) : ℝ) ≤ 1)
    {Record : Type*} [Fintype Record]
    (C : Finset (Fin (d * d * b) → Bool)) (hC : C.Nonempty)
    (record : (Fin (d * d * b) → Bool) → ℕ → Record) (output : ℕ → Record → Bool)
    {β α : ℝ} (hcapacity : Real.log (Fintype.card Record : ℝ) / Real.log 2 ≤ β)
    (hlocal : CausalRecovery.LocallyDetermined (actualParents xs T) (fun s => {x s})
      (T - 1) (C : Set (Fin (d * d * b) → Bool)) zbit record)
    (hcorrect : ∀ z ∈ C, ∀ u : Fin (d * d * b),
      output (tpos d b u.val) (record z (t (tpos d b u.val))) = z u)
    (D : Finset (CoreFamily K)) (hD : D.card ≤ r)
    (hV : (∑ G ∈ univ \ D, ∑ e ∈ G.val.edges,
      dist (x e : ℝ) (x (e + 1) : ℝ)) ≤ α * (d * d * b))

include hM hρ hE hwalk hcolor hsize hd hb hw ht hn hx hstep hC hcapacity hlocal hcorrect hD hV

/-- A single phase retains the actual shared raw support and the smaller
one-exception movement constant. The residual bill uses both exceptions. -/
theorem phase_shared_deficit :
    (d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2 ≥
      (d * d * b : ℝ) * (max (1 - α) 0 ^ 2 /
        (2 * (2 * (r : ℝ) + 1) * (2 * (M : ℝ) + 4))) -
      2 * ((bankCost M 1 : ℝ) * ((T - 1 : ℕ) : ℝ)) / d -
      2 * ((w : ℝ) - 1) - ((d : ℝ) * b - b + 1) / 2 -
      β * ((initialPayment K E M ρ).card + (1 + (N : ℝ) * a) *
        ((bankCost M 2 : ℝ) * ((T - 1 : ℕ) : ℝ)) / w) -
      w * (sharedRawSupport hc hM E x ((range (d * d * b)).image t) ρ).card := by
  let B := exactSourceBank (ρ := ρ) hc hM E
  let O := exactSourceBank (ρ := ρ) hc hM (olderException E).toList.toFinset
  let Y := indexedRawBank B x
  let Y₀ := indexedRawBank O x
  let roots := (range (d * d * b)).image t
  let S := sharedRawSupport hc hM E x roots ρ
  let : Nonempty (Fin O.length) := exactSourceBank_nonempty hc hM hρ _
  have hselected : ∀ v ≤ T - 1, ∀ u ∈ actualParents xs T v,
      u ∈ selectedParents K E v → u ∉ initialPayment K E M ρ →
      residualBankValues Y u ⊆ residualBankValues Y v := by
    intro v _ u _ hu hunpaid
    simpa only [Y, indexedRawBank_values, B] using
      initial_selected_raw_values_closed hc hM hρ E hwalk hu hunpaid x
  have hload : ∀ e < T - 1,
      ((ResidualGeometry.live (residualParents (actualParents xs T) (selectedParents K E))
        (T - 1) (initialPayment K E M ρ) e).card : ℝ) ≤ ((1 + N * a : ℕ) : ℝ) := by
    intro e _
    exact_mod_cast residual_live_card_le K E hcolor hsize (T - 1) (initialPayment K E M ρ) e
  have hcover (z : Fin (d * d * b)) : residualBankValues Y (t (tpos d b z.val)) ⊆
      residualBankValues Y₀ (t (tpos d b z.val)) ∪ S := by
    simp only [Y, Y₀, indexedRawBank_values]
    exact exactSourceBank_shared_cover hc hM hρ E hE x roots
      (mem_image_of_mem t (mem_range.mpr (tpos_lt z.isLt)))
  obtain ⟨θ, _, _, hdef⟩ := exists_paidBank_shared_deficit hd hb hw ht
    (fun z hz => by have := hn z hz; omega) (indexedRawBank_range hc hM hρ E x hx)
    (indexedRawBank_range hc hM hρ (olderException E).toList.toFinset x hx) hC hcapacity
    (fun _ _ _ hu => actualParents_earlier hu) hselected
    (fun s _ => indexedRawBank_root hc hM hρ E x s) hlocal hcorrect hload S hcover
  have hsum := mul_le_mul_of_nonneg_left
    (sum_le_sum (fun j hj => olderBank_gap hc hM hρ E x t hd hb hn hx D hD hV (mem_range.mp hj)))
    (show (0 : ℝ) ≤ d * b by positivity)
  have hsum' : (d * d * b : ℝ) * (max (1 - α) 0 ^ 2 /
      (2 * (2 * (r : ℝ) + 1) * (2 * (M : ℝ) + 4))) ≤
        (d : ℝ) * b * ∑ j ∈ range d, frozenArea Y₀ t d b j := by
    simpa only [sum_const, card_range, nsmul_eq_mul, Nat.cast_mul,
      mul_left_comm, mul_assoc] using hsum
  have hVO := exactSourceBank_raw_variation hc hM hρ (olderException E).toList.toFinset
    (show (olderException E).toList.toFinset.card ≤ 1 by cases olderException E <;> simp)
    (fun s => (x s : ℝ)) hstep
  have hVB := exactSourceBank_raw_variation hc hM hρ E hE (fun s => (x s : ℝ)) hstep
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hVO (by norm_num : (0 : ℝ) ≤ 2)) (Nat.cast_nonneg d)
  have hp := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hVB (Nat.cast_nonneg (1 + N * a))) (Nat.cast_nonneg w))
    (recordCapacity_nonneg hcapacity)
  have hraw : ((ShiftedGrid.blockUnion (d * d * b) w θ S).card : ℝ) ≤ w * S.card := by
    exact_mod_cast (ShiftedGrid.blockUnion_card_le hw θ S).trans (min_le_right ..)
  simp only [indexedRawBank_variation, B, O, Nat.cast_add, Nat.cast_mul,
    Nat.cast_one] at hdef hm hp
  dsimp only [S, roots] at hraw
  linarith

end Phase

end
end SourceCovers

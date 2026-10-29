import SourceCovers.SharedSupportDeficit

set_option autoImplicit false

/-! Finite global sharing, averaged over the original legal phases. No
runtime bound, small-sharing assumption, or limiting geometry is required. -/

namespace SourceCovers

open Classical Finset LeanMachine Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K : Finset (ActualFamily xs T)}
    (hc : HasSpanColoring K 2) {M d b w J R r N a : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (P D : Finset (CoreFamily K))
    (hK : K.card ≤ J) (hE : E.card ≤ 2) (hP : P.card ≤ R) (hR : R < M)
    (hD : D.card ≤ r) (hwalk : ∀ h, BoundedNesting.IsWalk (xs h))
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
    {β α τ : ℝ} (hcapacity : Real.log (Fintype.card Record : ℝ) / Real.log 2 ≤ β)
    (hlocal : CausalRecovery.LocallyDetermined (actualParents xs T) (fun s => {x s})
      (T - 1) (C : Set (Fin (d * d * b) → Bool)) zbit record)
    (hcorrect : ∀ z ∈ C, ∀ u : Fin (d * d * b),
      output (tpos d b u.val) (record z (t (tpos d b u.val))) = z u)
    (hV : (∑ G ∈ univ \ D, ∑ e ∈ G.val.edges,
      dist (x e : ℝ) (x (e + 1) : ℝ)) ≤ α * (d * d * b))
    (hτ : ((∑ G ∈ coreNonleaves K \ P, G.val.hops.card : ℕ) : ℝ) ≤ τ)

include hK hE hP hR hD hwalk hcolor hsize hd hb hw ht hn hx hstep hC
  hcapacity hlocal hcorrect hV hτ

/-- Average any raw-revelation payment that is valid at every shift.
Protection and distinguished-family budgets remain independent. -/
theorem shared_support_paid_deficit_of_payment (p : ℕ → ℝ)
    (hpay : ∀ ρ ∈ admissiblePhases K P M, ∀ θ,
      ((ShiftedGrid.blockUnion (d * d * b) w θ
        (sharedRawSupport hc hM E x ((range (d * d * b)).image t) ρ)).card : ℝ) ≤ p ρ) :
    ((d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2) / (d * d * b) ≥
      max (1 - α) 0 ^ 2 / (2 * (2 * (r : ℝ) + 1) * (2 * (M : ℝ) + 4)) -
        ((∑ ρ ∈ admissiblePhases K P M, p ρ) /
            (admissiblePhases K P M).card) / (d * d * b) -
        (2 * bankCost M 1 * ((T - 1 : ℕ) : ℝ) / (d * (d * d * b)) +
          2 * ((w : ℝ) - 1) / (d * d * b) +
          ((d : ℝ) * b - b + 1) / (2 * (d * d * b)) +
          β / (d * d * b) * (J + 2 + τ / ((M - R : ℕ) : ℝ) +
            (1 + (N : ℝ) * a) * bankCost M 2 * ((T - 1 : ℕ) : ℝ) / w)) := by
  let A := admissiblePhases K P M
  let V₁ : ℝ := bankCost M 1 * ((T - 1 : ℕ) : ℝ)
  let V₂ : ℝ := bankCost M 2 * ((T - 1 : ℕ) : ℝ)
  let c : ℝ := 2 * V₁ / d + 2 * ((w : ℝ) - 1) + ((d : ℝ) * b - b + 1) / 2 +
    β * ((1 + (N : ℝ) * a) * V₂ / w)
  let f := fun ρ => (d * d * b : ℝ) *
    (max (1 - α) 0 ^ 2 / (2 * (2 * (r : ℝ) + 1) * (2 * (M : ℝ) + 4))) -
      p ρ
  have hpayment := initialPayment_average_of_budgets K E P hK hE hP hR hτ
  have hA : A.Nonempty := card_pos.mp hpayment.1
  have hpoint : ∀ ρ ∈ A, f ρ - c - β * (initialPayment K E M ρ).card ≤
      (d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2 := by
    intro ρ hρ
    have h := phase_shared_deficit_of_payment hc hM (admissiblePhase_lt hρ) E hE hwalk hcolor hsize
      x t hd hb hw ht hn hx hstep C hC record output hcapacity hlocal hcorrect D hD hV
      (p ρ) (hpay ρ hρ)
    convert h using 1
    dsimp [f, c, V₁, V₂]
    ring
  have havg := PaidAveraging.mean_credit_sub_cost_le hA (recordCapacity_nonneg hcapacity)
    hpoint hpayment.2
  have hL : (0 : ℝ) < d * d * b := by positivity
  have hnorm := div_le_div_of_nonneg_right havg hL.le
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hA0 : (A.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hA).ne'
  convert hnorm using 1
  dsimp only [f, c, V₁, V₂]
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
  field_simp
  ring

/-- The actual raw-support count is the original per-coordinate payment.
Its proof now reuses the same averaged theorem as interval covers. -/
theorem shared_support_paid_deficit :
    ((d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2) / (d * d * b) ≥
      max (1 - α) 0 ^ 2 / (2 * (2 * (r : ℝ) + 1) * (2 * (M : ℝ) + 4)) -
        w * ((∑ ρ ∈ admissiblePhases K P M,
          ((sharedRawSupport hc hM E x ((range (d * d * b)).image t) ρ).card : ℝ)) /
            (admissiblePhases K P M).card) / (d * d * b) -
        (2 * bankCost M 1 * ((T - 1 : ℕ) : ℝ) / (d * (d * d * b)) +
          2 * ((w : ℝ) - 1) / (d * d * b) +
          ((d : ℝ) * b - b + 1) / (2 * (d * d * b)) +
          β / (d * d * b) * (J + 2 + τ / ((M - R : ℕ) : ℝ) +
            (1 + (N : ℝ) * a) * bankCost M 2 * ((T - 1 : ℕ) : ℝ) / w)) := by
  have h := shared_support_paid_deficit_of_payment hc hM E P D hK hE hP hR hD hwalk hcolor hsize
    x t hd hb hw ht hn hx hstep C hC record output hcapacity hlocal hcorrect hV hτ
    (fun ρ => (w : ℝ) * (sharedRawSupport hc hM E x ((range (d * d * b)).image t) ρ).card)
    (fun ρ _ θ => by
      exact_mod_cast (ShiftedGrid.blockUnion_card_le hw θ
        (sharedRawSupport hc hM E x ((range (d * d * b)).image t) ρ)).trans (min_le_right ..))
  simpa only [← mul_sum, mul_div_assoc] using h

/-- Proposition 5.1. Counting maximal older seeds is a direct relaxation of
the raw-support theorem. At `M = 2R + 2` its constants are `ell + 1` and
`B_R = ell(ell + 1)`, with the original complete two-exception error. -/
theorem shared_support_count_deficit :
    ((d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2) / (d * d * b) ≥
      max (1 - α) 0 ^ 2 / (2 * (2 * (r : ℝ) + 1) * (2 * (M : ℝ) + 4)) -
        w * ((2 * (M : ℝ) + 3) * (2 * (M : ℝ) + 4)) *
          ((∑ ρ ∈ admissiblePhases K P M,
            (sharedSeedCount hc hM E ((range (d * d * b)).image t) ρ : ℝ)) /
              (admissiblePhases K P M).card) / (d * d * b) -
        (2 * bankCost M 2 * ((T - 1 : ℕ) : ℝ) / (d * (d * d * b)) +
          2 * ((w : ℝ) - 1) / (d * d * b) +
          ((d : ℝ) * b - b + 1) / (2 * (d * d * b)) +
          β / (d * d * b) * (J + 2 + τ / ((M - R : ℕ) : ℝ) +
            (1 + (N : ℝ) * a) * bankCost M 2 * ((T - 1 : ℕ) : ℝ) / w)) := by
  have h := shared_support_paid_deficit hc hM E P D hK hE hP hR hD hwalk hcolor hsize
    x t hd hb hw ht hn hx hstep C hC record output hcapacity hlocal hcorrect hV hτ
  have hsum := sum_le_sum (s := admissiblePhases K P M) (fun ρ hρ =>
    (show ((sharedRawSupport hc hM E x ((range (d * d * b)).image t) ρ).card : ℝ) ≤
        ((2 * (M : ℝ) + 3) * (2 * (M : ℝ) + 4)) *
          sharedSeedCount hc hM E ((range (d * d * b)).image t) ρ by
      exact_mod_cast sharedRawSupport_card_le hc hM (admissiblePhase_lt hρ) E x
        ((range (d * d * b)).image t)))
  rw [← mul_sum] at hsum
  have hraw := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg (admissiblePhases K P M).card))
    (Nat.cast_nonneg w))
    (show (0 : ℝ) ≤ d * d * b by positivity)
  have hcost : (bankCost M 1 : ℝ) ≤ bankCost M 2 := by
    exact_mod_cast bankCost_mono M (by omega : 1 ≤ 2)
  have hmotion := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcost (by norm_num : (0 : ℝ) ≤ 2))
      (Nat.cast_nonneg (T - 1))) (show (0 : ℝ) ≤ d * (d * d * b) by positivity)
  simp only [mul_div_assoc, mul_assoc] at hraw h hmotion ⊢
  linarith only [h, hraw, hmotion]

end
end SourceCovers

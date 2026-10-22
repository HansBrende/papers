import TransposeFollowup.ContractingStageClock

/-! Exceptional work is counted in actual global ticks. Discarding deep
regular stages costs only the previously proved geometric tail. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology MeasureTheory
set_option autoImplicit false

def exceptionalTicks {B J T : ℕ} {rho a C P : ℝ}
    (clock : ContractingStageClock B J rho a C P T)
    (good : List (Fin B) × Fin J → Bool) : ℕ :=
  (Finset.univ.filter (fun t : Fin T => good (clock.label t) ≠ true)).card

/-- Exceptional work charged per node gives a global physical-time budget.
The existing tree charge theorem counts each exceptional tick exactly once. -/
theorem exceptionalTicks_node_budget {B J T : ℕ} {rho a C P eta : ℝ}
    (clock : ContractingStageClock B J rho a C P T)
    (hr : 0 ≤ rho) (hr1 : rho < 1) (heta : 0 ≤ eta) (hP : 0 < P)
    (good : List (Fin B) × Fin J → Bool)
    (hnode : ∀ w, (((Finset.univ.filter (fun t : Fin T => good (clock.label t) ≠ true)).filter
      (fun t => (clock.label t).1=w)).card : ℝ) ≤ eta*clock.V w) :
    (exceptionalTicks clock good : ℝ)/P ≤ eta*C/(1-rho) := by
  have h := assigned_tick_bound clock.nonneg hr hr1 heta clock.children
    (Finset.univ.filter (fun t : Fin T => good (clock.label t) ≠ true))
    (fun t => (clock.label t).1) 0 hnode (fun _ _ => Nat.zero_le _)
  simp only [pow_zero,mul_one] at h
  apply (div_le_iff₀ hP).mpr
  calc
    (exceptionalTicks clock good : ℝ) ≤ eta*clock.V []/(1-rho) := h
    _ ≤ eta*(C*P)/(1-rho) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left clock.root heta) (sub_pos.mpr hr1).le
    _ = eta*C/(1-rho)*P := by ring

theorem regular_shallow_stage_omission {B J T : ℕ} {rho a C P : ℝ}
    (clock : ContractingStageClock B J rho a C P T)
    (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a) (hP : 0 < P)
    (good : List (Fin B) × Fin J → Bool) (h : ℕ) :
    volume.real (Ico 0 ((T : ℝ)/P) \
      stageRegion (fun p => (clock.A p.1 p.2 : ℝ)/P) (fun p => (clock.E p.1 p.2 : ℝ)/P)
        {p | p.1.length < h ∧ good p=true}) ≤
      (exceptionalTicks clock good : ℝ)/P+a*C*rho^h/(1-rho) := by
  let bad := Finset.univ.filter (fun t : Fin T => good (clock.label t) ≠ true)
  let deep := Finset.univ.filter (fun t : Fin T => h ≤ (clock.label t).1.length)
  let missed := Finset.univ.filter (fun t : Fin T =>
    clock.label t ∉ {p | p.1.length < h ∧ good p=true})
  have hcard : missed.card ≤ bad.card+deep.card := by
    apply (Finset.card_le_card (show missed ⊆ bad ∪ deep from ?_)).trans (Finset.card_union_le _ _)
    intro t ht
    have ht' := (Finset.mem_filter.mp ht).2
    by_cases hg : good (clock.label t)=true
    · apply Finset.mem_union.mpr (Or.inr ?_)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
        by_contra hd
        exact ht' ⟨by omega,hg⟩⟩
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg⟩))
  have hdeep : (deep.card : ℝ)/P ≤ a*C*rho^h/(1-rho) := by
    have hc := stage_clock_physical_omission_of_root_bound clock.nonneg hr hr1 ha hP
      clock.children clock.root clock.label clock.A clock.E clock.bounded clock.partition clock.budget h
    rw [stageRegion_scaled_omission_volume clock.label (fun p => clock.A p.1 p.2)
      (fun p => clock.E p.1 p.2) (fun p => clock.bounded p.1 p.2)
      (fun p t => clock.partition p.1 p.2 t) _ hP] at hc
    simpa only [deep,Set.mem_ofPred_eq,Nat.not_lt] using hc
  rw [stageRegion_scaled_omission_volume clock.label (fun p => clock.A p.1 p.2)
    (fun p => clock.E p.1 p.2) (fun p => clock.bounded p.1 p.2)
    (fun p t => clock.partition p.1 p.2 t) _ hP]
  have hcalc : (missed.card : ℝ)/P ≤ (bad.card : ℝ)/P+a*C*rho^h/(1-rho) := by
    calc
      (missed.card : ℝ)/P ≤ ((bad.card : ℝ)+(deep.card : ℝ))/P :=
        div_le_div_of_nonneg_right (by exact_mod_cast hcard) hP.le
      _ = (bad.card : ℝ)/P+(deep.card : ℝ)/P := add_div _ _ _
      _ ≤ (bad.card : ℝ)/P+a*C*rho^h/(1-rho) := add_le_add le_rfl hdeep
  simpa only [missed,bad,exceptionalTicks,Set.mem_ofPred_eq] using hcalc

end TransposeFollowup.RegularMotion

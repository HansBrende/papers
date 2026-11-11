import AdaptiveTransfer.FragmentAncestors
import BoundedNesting.Owner
import MergeDepth.Realization

/-! Native dependency paths constrained to a closed integer band. No
one-sided-excursion premise is needed: a unit walk may leave either side
arbitrarily often, and actual last-visit edges skip each excursion. -/
namespace AdaptiveTransfer.TransferBandPaths
open Finset BoundedNesting MergeDepth

private theorem last_visit_step {k T a u : ℕ} {xs : Fin k → ℕ → ℤ} (h : Fin k)
    (hu : u < T) (hex : ∃ r, a ≤ r ∧ r < u ∧ xs h r = xs h u) :
    ∃ p, a ≤ p ∧ p < u ∧ DepStep xs T u p ∧ xs h p = xs h u := by
  classical
  let S := (Ico a u).filter fun r => xs h r = xs h u
  have hS : S.Nonempty := by
    obtain ⟨r, ha, hr, he⟩ := hex
    exact ⟨r, mem_filter.mpr ⟨mem_Ico.mpr ⟨ha, hr⟩, he⟩⟩
  let p := S.max' hS
  have hp := mem_filter.mp (max'_mem S hS)
  have hlast : ∀ r, p < r → r < u → xs h r ≠ xs h u := by
    intro r hpr hru he
    have hr : r ∈ S := mem_filter.mpr ⟨mem_Ico.mpr ⟨by have := (mem_Ico.mp hp.1).1; omega, hru⟩, he⟩
    have hh : r ≤ p := le_max' S r hr
    omega
  refine ⟨p, (mem_Ico.mp hp.1).1, (mem_Ico.mp hp.1).2, ?_, hp.2⟩
  exact AdaptiveTransfer.depStep_of_last_visit h hu (mem_Ico.mp hp.1).2 hp.2.symm (fun r hpr hru => (hlast r hpr hru).symm)

/-- Either the immediate predecessor remains in the band or the last prior
visit to the current boundary gives an actual original dependency edge. -/
theorem band_predecessor {k T a u : ℕ} {xs : Fin k → ℕ → ℤ} (h : Fin k)
    (hx : IsWalk (xs h)) (hau : a < u) (huT : u < T) {L R : ℤ}
    (ha : L ≤ xs h a ∧ xs h a ≤ R) (hu : L ≤ xs h u ∧ xs h u ≤ R) :
    ∃ p, a ≤ p ∧ p < u ∧ DepStep xs T u p ∧ L ≤ xs h p ∧ xs h p ≤ R := by
  have hpred : u - 1 + 1 = u := by omega
  have hstep := hx.step (u - 1)
  rw [hpred] at hstep
  by_cases hp : L ≤ xs h (u - 1) ∧ xs h (u - 1) ≤ R
  · exact ⟨u - 1, by omega, by omega, Or.inl ⟨hpred, huT⟩, hp⟩
  have hex : ∃ r, a ≤ r ∧ r < u ∧ xs h r = xs h u := by
    by_cases hlo : xs h (u - 1) < L
    · have he : xs h u = L := by omega
      obtain ⟨r, har, hru, hr, _⟩ := exists_down_crossing hx (c := L - 1) (u - 1 - a) a
        (by omega) (by rw [Nat.add_sub_of_le (by omega : a ≤ u - 1)]; omega)
      refine ⟨r, har, by omega, ?_⟩
      omega
    · have he : xs h u = R := by omega
      obtain ⟨r, har, hru, hr, _⟩ := exists_up_crossing hx (c := R) (u - 1 - a) a
        ha.2 (by rw [Nat.add_sub_of_le (by omega : a ≤ u - 1)]; omega)
      exact ⟨r, har, by omega, hr.trans he.symm⟩
  obtain ⟨p, hap, hpu, hdep, he⟩ := last_visit_step h huT hex
  exact ⟨p, hap, hpu, hdep, he ▸ hu⟩

/-- Any two time-ordered visits inside a closed integer band admit a
backward path inside the band. It uses actual work last-visit/state edges,
includes both endpoints, and permits the singleton case. -/
theorem exists_band_path {k T : ℕ} {xs : Fin k → ℕ → ℤ} (h : Fin k)
    (hx : IsWalk (xs h)) (a u : ℕ) (hau : a ≤ u) (huT : u < T) {L R : ℤ}
    (ha : L ≤ xs h a ∧ xs h a ≤ R) (hu : L ≤ xs h u ∧ xs h u ≤ R) :
    ∃ ρ : List ℕ, IsDepPath xs T (u :: ρ) ∧ (u :: ρ).getLastD u = a ∧
      ∀ r ∈ u :: ρ, a ≤ r ∧ r ≤ u ∧ L ≤ xs h r ∧ xs h r ≤ R := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    by_cases he : a = u
    · subst a
      refine ⟨[], trivial, rfl, ?_⟩
      intro r hr
      have hr' : r = u := by simpa using hr
      subst r
      exact ⟨le_rfl, le_rfl, hu⟩
    · obtain ⟨p, hap, hpu, hdep, hp⟩ := band_predecessor h hx (by omega) huT ha hu
      obtain ⟨ρ, hρ, hlast, hband⟩ := ih p hpu hap (hpu.trans huT) hp
      refine ⟨p :: ρ, ⟨hdep, hρ⟩, ?_, ?_⟩
      · simpa only [List.getLastD_cons] using hlast
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨hau, le_rfl, hu⟩
        · obtain ⟨har, hrp, hpos⟩ := hband r hr
          exact ⟨har, hrp.trans hpu.le, hpos⟩

end AdaptiveTransfer.TransferBandPaths

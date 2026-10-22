import TransposeFollowup.ExcursionPulse

/-! Explicit page walks from a finite nested schedule. The input records only
event times and their separation/order. The walk itself is the sum of pulses;
its local shape, depth, unit steps and eventual reset are derived below. -/

namespace TransposeFollowup

open Classical Transpose.Tape
open scoped BigOperators
set_option autoImplicit false

structure NestedPulseSchedule (E : Type*) (k S : ℕ) where
  gap_pos : 0 < S
  page : E → Fin k
  opening : E → ℕ
  closing : E → ℕ
  self_gap : ∀ e, opening e + S ≤ closing e
  nested : ∀ e f, e ≠ f → page e = page f →
    (opening e + S ≤ opening f ∧ closing f + S ≤ closing e) ∨
    (opening f + S ≤ opening e ∧ closing e + S ≤ closing f)

namespace NestedPulseSchedule

variable {E : Type*} [Fintype E] {k S : ℕ}
    (D : NestedPulseSchedule E k S)

noncomputable def outerSet (e : E) : Finset E :=
  Finset.univ.filter (fun f => D.page f = D.page e ∧ D.opening f < D.opening e)

theorem mem_outerSet (e f : E) :
    f ∈ D.outerSet e ↔ D.page f = D.page e ∧ D.opening f < D.opening e := by
  simp [outerSet]

noncomputable def depth (e : E) : ℕ := (D.outerSet e).card

noncomputable def walk (L : ℕ) (p : Fin k) (t : ℕ) : ℤ :=
  ∑ e : E, if D.page e = p then excursionPulse L (D.opening e) (D.closing e) t else 0

theorem outer_gap {e f : E} (hf : f ∈ D.outerSet e) :
    D.opening f + S ≤ D.opening e ∧ D.closing e + S ≤ D.closing f := by
  obtain ⟨hp, ho⟩ := (D.mem_outerSet e f).mp hf
  have hne : f ≠ e := by intro h; subst f; omega
  rcases D.nested f e hne hp with h | h
  · exact h
  · have := D.gap_pos; omega

theorem depth_strict {e f : E} (hp : D.page e = D.page f)
    (ho : D.opening e < D.opening f) : D.depth e < D.depth f := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro g hg
    obtain ⟨hgp, hgo⟩ := (D.mem_outerSet e g).mp hg
    exact (D.mem_outerSet f g).mpr ⟨hgp.trans hp, hgo.trans ho⟩
  · intro heq
    have he : e ∈ D.outerSet f := (D.mem_outerSet f e).mpr ⟨hp, ho⟩
    rw [← heq] at he
    exact (lt_irrefl _) ((D.mem_outerSet e e).mp he).2

theorem other_boundary {L t : ℕ} (hL : L ≤ S) {e f : E} (hne : f ≠ e)
    (ht : (D.opening e ≤ t ∧ t ≤ D.opening e + L) ∨
      (D.closing e ≤ t ∧ t ≤ D.closing e + L)) :
    (if D.page f = D.page e then excursionPulse L (D.opening f) (D.closing f) t else 0) =
      if f ∈ D.outerSet e then (L : ℤ) else 0 := by
  have he := D.self_gap e
  have hf := D.self_gap f
  have hs := D.gap_pos
  by_cases hp : D.page f = D.page e
  · rw [ite_eq_left hp]
    rcases D.nested f e hne hp with hg | hg
    · have hm : f ∈ D.outerSet e := (D.mem_outerSet e f).mpr ⟨hp, by omega⟩
      rw [ite_eq_left hm]
      apply excursionPulse_plateau <;> rcases ht with ht | ht <;> omega
    · have hm : f ∉ D.outerSet e := by
        intro hm
        have := ((D.mem_outerSet e f).mp hm).2
        omega
      rw [ite_eq_right hm]
      rcases ht with ht | ht
      · exact excursionPulse_before (by omega) (by omega)
      · exact excursionPulse_after (by omega) (by omega)
  · have hm : f ∉ D.outerSet e := fun hf => hp ((D.mem_outerSet e f).mp hf).1
    simp only [ite_eq_right hp, ite_eq_right hm]

theorem walk_boundary {L t : ℕ} (hL : L ≤ S) (e : E)
    (ht : (D.opening e ≤ t ∧ t ≤ D.opening e + L) ∨
      (D.closing e ≤ t ∧ t ≤ D.closing e + L)) :
    D.walk L (D.page e) t = (D.depth e : ℤ) * L +
      excursionPulse L (D.opening e) (D.closing e) t := by
  have hnot : e ∉ D.outerSet e := by simp [mem_outerSet]
  calc
    D.walk L (D.page e) t = ∑ f : E,
      ((if f = e then excursionPulse L (D.opening e) (D.closing e) t else 0) +
        (if f ∈ D.outerSet e then (L : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro f _
      by_cases hfe : f = e
      · subst f
        simp [hnot]
      · simp only [ite_eq_right hfe, zero_add]
        exact D.other_boundary hL hfe ht
    _ = excursionPulse L (D.opening e) (D.closing e) t + (D.depth e : ℤ) * L := by
      rw [Finset.sum_add_distrib]
      simp [depth]
    _ = _ := add_comm _ _

theorem walk_rise {L t : ℕ} (hL : L ≤ S) (e : E)
    (ha : D.opening e ≤ t) (ht : t ≤ D.opening e + L) :
    D.walk L (D.page e) t = (D.depth e : ℤ) * L + (t - D.opening e : ℕ) := by
  rw [D.walk_boundary hL e (Or.inl ⟨ha, ht⟩), excursionPulse_rise (by have := D.self_gap e; omega) ha ht]

theorem walk_fall {L t : ℕ} (hL : L ≤ S) (e : E)
    (hc : D.closing e ≤ t) (ht : t ≤ D.closing e + L) :
    D.walk L (D.page e) t = ((D.depth e : ℤ) + 1) * L - (t - D.closing e : ℕ) := by
  rw [D.walk_boundary hL e (Or.inr ⟨hc, ht⟩), excursionPulse_fall (by have := D.self_gap e; omega) hc ht]
  ring

theorem walk_middle {L t : ℕ} (hL : L ≤ S) (e : E)
    (ha : D.opening e + L ≤ t) (hc : t ≤ D.closing e) :
    ((D.depth e : ℤ) + 1) * L ≤ D.walk L (D.page e) t := by
  have hnot : e ∉ D.outerSet e := by simp [mem_outerSet]
  have hsum : (∑ f : E, ((if f = e then (L : ℤ) else 0) +
      (if f ∈ D.outerSet e then (L : ℤ) else 0))) ≤ D.walk L (D.page e) t := by
    apply Finset.sum_le_sum
    intro f _
    by_cases hfe : f = e
    · subst f
      simp only [ite_eq_right hnot, add_zero]
      exact le_of_eq (excursionPulse_plateau ha hc).symm
    · simp only [ite_eq_right hfe, zero_add]
      by_cases hm : f ∈ D.outerSet e
      · obtain ⟨hp, _⟩ := (D.mem_outerSet e f).mp hm
        have hg := D.outer_gap hm
        simp only [ite_eq_left hm, ite_eq_left hp]
        exact le_of_eq (excursionPulse_plateau (by omega) (by omega)).symm
      · simp only [ite_eq_right hm]
        split_ifs
        · exact excursionPulse_nonneg (by have := D.self_gap f; omega)
        · exact le_refl _
  have heq : (∑ f : E, ((if f = e then (L : ℤ) else 0) +
      (if f ∈ D.outerSet e then (L : ℤ) else 0))) = ((D.depth e : ℤ) + 1) * L := by
    rw [Finset.sum_add_distrib]
    simp [depth]
    ring
  rwa [heq] at hsum

theorem walk_zero (L : ℕ) (p : Fin k) : D.walk L p 0 = 0 := by
  apply Finset.sum_eq_zero
  intro e _
  split_ifs
  · exact excursionPulse_before (by have := D.self_gap e; omega) (Nat.zero_le _)
  · rfl

theorem walk_reset {L T : ℕ} (hend : ∀ e, D.closing e + L ≤ T) (p : Fin k)
    {t : ℕ} (ht : T ≤ t) : D.walk L p t = 0 := by
  apply Finset.sum_eq_zero
  intro e _
  split_ifs
  · exact excursionPulse_after (by have := D.self_gap e; omega) ((hend e).trans ht)
  · rfl

omit [Fintype E] in
theorem changes_unique {L t : ℕ} (hL : L ≤ S) {e f : E} (hp : D.page e = D.page f)
    (he : excursionPulse L (D.opening e) (D.closing e) (t + 1) ≠
      excursionPulse L (D.opening e) (D.closing e) t)
    (hf : excursionPulse L (D.opening f) (D.closing f) (t + 1) ≠
      excursionPulse L (D.opening f) (D.closing f) t) : e = f := by
  by_contra hne
  have he' := excursionPulse_change he
  have hf' := excursionPulse_change hf
  have hselfe := D.self_gap e
  have hselff := D.self_gap f
  rcases D.nested e f hne hp with hg | hg <;>
    rcases he' with he' | he' <;> rcases hf' with hf' | hf' <;> omega

theorem walk_unitSteps {L : ℕ} (hL : L ≤ S) (p : Fin k) : UnitSteps (D.walk L p) := by
  intro t
  let move (e : E) : ℤ := if D.page e = p then
    excursionPulse L (D.opening e) (D.closing e) (t + 1) -
      excursionPulse L (D.opening e) (D.closing e) t else 0
  have hdiff : D.walk L p (t + 1) - D.walk L p t = ∑ e : E, move e := by
    dsimp [walk]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    dsimp [move]
    split_ifs <;> ring
  rw [hdiff]
  by_cases hm : ∃ e : E, D.page e = p ∧
      excursionPulse L (D.opening e) (D.closing e) (t + 1) ≠
        excursionPulse L (D.opening e) (D.closing e) t
  · obtain ⟨e, hp, he⟩ := hm
    have hs : (∑ f : E, move f) = move e := by
      apply Finset.sum_eq_single e
      · intro f _ hfe
        by_cases hfp : D.page f = p
        · have hf : excursionPulse L (D.opening f) (D.closing f) (t + 1) =
              excursionPulse L (D.opening f) (D.closing f) t := by
            by_contra hfm
            exact hfe (D.changes_unique hL (hfp.trans hp.symm) hfm he)
          simp [move, hfp, hf]
        · simp [move, hfp]
      · simp
    rw [hs]
    simpa only [move, ite_eq_left hp] using
      excursionPulse_unitSteps L (D.opening e) (D.closing e) t
  · have hs : (∑ e : E, move e) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      by_cases hp : D.page e = p
      · have he : excursionPulse L (D.opening e) (D.closing e) (t + 1) =
            excursionPulse L (D.opening e) (D.closing e) t := by
          by_contra he
          exact hm ⟨e, hp, he⟩
        simp [move, hp, he]
      · simp [move, hp]
    rw [hs]
    norm_num

end NestedPulseSchedule
end TransposeFollowup

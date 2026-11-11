import LeanMachine.BlockProgramCoarsen
import LeanMachine.WeightedGrid

/-! The exact set of original writer/reader contexts of each dated value.
Unread dates have span zero. One common shifted partition pays both resident
switches and all distinct foreign versions. -/

namespace LeanMachine.BlockProgram
open Finset Classical
open scoped BigOperators

variable {O S A : Type*} {R : O → Type*}

noncomputable def participants (p : BlockProgram O R S A) (context : O → ℕ) (T t : ℕ) :
    Finset ℕ := insert (context (p.owner t))
      (((range T).filter (fun u => t ∈ p.reads u)).image (fun u => context (p.owner u)))

theorem participants_nonempty (p : BlockProgram O R S A) (context : O → ℕ) (T t : ℕ) :
    (p.participants context T t).Nonempty := ⟨_, mem_insert_self _ _⟩

noncomputable def span (p : BlockProgram O R S A) (context : O → ℕ) (T t : ℕ) : ℕ :=
  (p.participants context T t).max' (p.participants_nonempty context T t) -
    (p.participants context T t).min' (p.participants_nonempty context T t)

noncomputable def variation (p : BlockProgram O R S A) (context : O → ℕ) (T : ℕ) : ℕ :=
  ∑ t ∈ range (T-1), (max (context (p.owner t)) (context (p.owner (t+1))) -
    min (context (p.owner t)) (context (p.owner (t+1))))

/-- Comparing every reader to its actual writer is equivalent to comparing
the extreme participating contexts. No consecutivity or one-reader premise. -/
theorem foreign_iff_extrema (p : BlockProgram O R S A) (context : O → ℕ)
    (T t g θ : ℕ) :
    (∃ u < T, t ∈ p.reads u ∧
      ShiftedGrid.label g θ (context (p.owner t)) ≠ ShiftedGrid.label g θ (context (p.owner u))) ↔
    ShiftedGrid.label g θ ((p.participants context T t).min' (p.participants_nonempty context T t)) ≠
      ShiftedGrid.label g θ ((p.participants context T t).max' (p.participants_nonempty context T t)) := by
  rw [← ShiftedGrid.nonconstant_iff_extrema_ne (p.participants_nonempty context T t)]
  constructor
  · rintro ⟨u, hu, hr, he⟩
    exact ⟨_, mem_insert_self _ _, _, mem_insert_of_mem
      (mem_image.mpr ⟨u, mem_filter.mpr ⟨mem_range.mpr hu, hr⟩, rfl⟩), he⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    by_contra hn
    have hall : ∀ z ∈ p.participants context T t,
        ShiftedGrid.label g θ z = ShiftedGrid.label g θ (context (p.owner t)) := by
      intro z hz
      rcases mem_insert.mp hz with he | hz
      · rw [he]
      · obtain ⟨u, hu, rfl⟩ := mem_image.mp hz
        obtain ⟨hu, hr⟩ := mem_filter.mp hu
        exact (not_ne_iff.mp (fun h => hn ⟨u, mem_range.mp hu, hr, h⟩)).symm
    exact hxy ((hall x hx).trans (hall y hy).symm)

/-- The original state variation and all literal version spans share one
partition. The extraction functions may depend on the chosen partition. -/
theorem exists_coarsened_cost_le
    (p : BlockProgram O R S A) (context : O → ℕ) (T g : ℕ) (hg : 0 < g)
    {I : Type*} {Raw : Fin g → I → Type*}
    (group : Fin g → O → I)
    (restrict : (θ : Fin g) → (o : O) → Raw θ (group θ o) → R o)
    (hgroup : ∀ θ o v, group θ o = group θ v ↔
      ShiftedGrid.label g θ.val (context o) = ShiftedGrid.label g θ.val (context v))
    (Sbits : ℝ) (hS : 0 ≤ Sbits) (bits : ℕ → ℝ) (hbits : ∀ t, 0 ≤ bits t) :
    ∃ θ : Fin g,
      Sbits * ((p.coarsen (group θ) (restrict θ)).stateExports T).card +
        ∑ t ∈ (p.coarsen (group θ) (restrict θ)).versionExports T, bits t ≤
      (Sbits * p.variation context T +
        ∑ t ∈ range T, (p.span context T t : ℝ) * bits t) / g := by
  let items : Finset (ℕ ⊕ ℕ) := (range (T-1)).disjSum (range T)
  let lo : ℕ ⊕ ℕ → ℕ := Sum.elim
    (fun t => min (context (p.owner t)) (context (p.owner (t+1))))
    (fun t => (p.participants context T t).min' (p.participants_nonempty context T t))
  let hi : ℕ ⊕ ℕ → ℕ := Sum.elim
    (fun t => max (context (p.owner t)) (context (p.owner (t+1))))
    (fun t => (p.participants context T t).max' (p.participants_nonempty context T t))
  let cost : ℕ ⊕ ℕ → ℝ := Sum.elim (fun _ => Sbits) bits
  have horder (i) (_hi : i ∈ items) : lo i ≤ hi i := by
    cases i with
    | inl t => exact min_le_max
    | inr t =>
      exact (p.participants context T t).min'_le _
        ((p.participants context T t).max'_mem (p.participants_nonempty context T t))
  have hcost (i) (_hi : i ∈ items) : 0 ≤ cost i := by
    cases i with
    | inl t => exact hS
    | inr t => exact hbits t
  obtain ⟨θ, hθ, hcharge⟩ := ShiftedGrid.exists_weightedCharge_le items lo hi cost g hg horder hcost
  refine ⟨⟨θ, hθ⟩, ?_⟩
  let q := p.coarsen (group ⟨θ,hθ⟩) (restrict ⟨θ,hθ⟩)
  have hs (t : ℕ) :
      (t < T ∧ t+1 < T ∧ q.owner t ≠ q.owner (t+1)) ↔
        t < T-1 ∧ ShiftedGrid.label g θ (lo (Sum.inl t)) ≠
          ShiftedGrid.label g θ (hi (Sum.inl t)) := by
    have he := not_iff_not.mpr (hgroup ⟨θ,hθ⟩ (p.owner t) (p.owner (t+1)))
    change (t < T ∧ t+1 < T ∧ group _ _ ≠ group _ _) ↔ _
    simp only [ne_eq, he]
    dsimp [lo, hi]
    by_cases ht : context (p.owner t) ≤ context (p.owner (t+1))
    · rw [min_eq_left ht, max_eq_right ht]
      omega
    · rw [min_eq_right (le_of_not_ge ht), max_eq_left (le_of_not_ge ht)]
      constructor <;> rintro ⟨h1, h2⟩
      · exact ⟨by omega, Ne.symm h2.2⟩
      · exact ⟨by omega, by omega, Ne.symm h2⟩
  have hv (t : ℕ) :
      (∃ u < T, t ∈ q.reads u ∧ q.owner t ≠ q.owner u) ↔
        ShiftedGrid.label g θ (lo (Sum.inr t)) ≠ ShiftedGrid.label g θ (hi (Sum.inr t)) := by
    change (∃ u < T, t ∈ p.reads u ∧ group _ _ ≠ group _ _) ↔ _
    simp_rw [not_iff_not.mpr (hgroup ⟨θ,hθ⟩ _ _)]
    exact p.foreign_iff_extrema context T t g θ
  have hstate : q.stateExports T = (range (T-1)).filter
      (fun t => ShiftedGrid.label g θ (lo (Sum.inl t)) ≠ ShiftedGrid.label g θ (hi (Sum.inl t))) := by
    ext t
    simp only [stateExports, mem_filter, mem_range]
    exact hs t
  have hver : q.versionExports T = (range T).filter
      (fun t => ShiftedGrid.label g θ (lo (Sum.inr t)) ≠ ShiftedGrid.label g θ (hi (Sum.inr t))) := by
    ext t
    simp only [versionExports, mem_filter, hv]
  have hsSum : Sbits * (q.stateExports T).card =
      ∑ t ∈ range (T-1), if ShiftedGrid.label g θ (lo (Sum.inl t)) ≠
        ShiftedGrid.label g θ (hi (Sum.inl t)) then Sbits else 0 := by
    rw [hstate, ← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  have hpaid : Sbits * (q.stateExports T).card + ∑ t ∈ q.versionExports T, bits t =
      ShiftedGrid.weightedCharge items lo hi cost g θ := by
    rw [ShiftedGrid.weightedCharge]
    change _ = ∑ i ∈ (range (T-1)).disjSum (range T), _
    rw [sum_disjSum, hsSum, hver, sum_filter]
    rfl
  have hbill : (∑ i ∈ items, ((hi i - lo i : ℕ) : ℝ) * cost i) =
      Sbits * p.variation context T +
        ∑ t ∈ range T, (p.span context T t : ℝ) * bits t := by
    dsimp [items]
    rw [sum_disjSum]
    simp only [lo, hi, cost, Sum.elim_inl, Sum.elim_inr, ← sum_mul]
    unfold span variation
    rw [Nat.cast_sum]
    ring
  change Sbits * (q.stateExports T).card + ∑ t ∈ q.versionExports T, bits t ≤ _
  rw [hpaid]
  exact hcharge.trans_eq (congrArg (fun r : ℝ => r / g) hbill)

end LeanMachine.BlockProgram

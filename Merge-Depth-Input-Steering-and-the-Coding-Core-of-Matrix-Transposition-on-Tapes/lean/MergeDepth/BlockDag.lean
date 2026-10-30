import MergeDepth.ColdGenie
import MergeDepth.SkeletonWalk

/-!
# The block DAG of a skeleton class (Lemma 4.5(a))

For coarse work walks `s j`, `prevS (s j) t` is the last earlier time at which `s j` has the value
`s j t`. The block DAG has a state edge `t → t - 1` and a block edge `t → prevS (s j) t` for every
work tape (`BlockStep`).

* `blockStep_iff`: the block DAG is the dependency DAG of the coarse walks (state edges and long
  hops of the walks), `DepStep`.
* `card_blockOut_le`, `card_blockIn_le`: every vertex has at most `k + 1` out- and in-neighbours.

Part (d) of Lemma 4.5 is `skeleton_entries_ownerLoad` in `MergeDepth/BlockMachine.lean`.
-/

namespace MergeDepth

open Finset BoundedNesting

variable {k : ℕ}

open Classical in
/-- The last earlier time with the same value. -/
noncomputable def prevS (y : ℕ → ℤ) (t : ℕ) : Option ℕ :=
  if h : ((range t).filter fun t' => y t' = y t).Nonempty then
    some (((range t).filter fun t' => y t' = y t).max' h)
  else none

theorem prevS_spec {y : ℕ → ℤ} {t u : ℕ} :
    prevS y t = some u ↔ u < t ∧ y u = y t ∧ ∀ v, u < v → v < t → y v ≠ y t := by
  classical
  unfold prevS
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl
      have hmem := max'_mem _ h
      obtain ⟨h1, h2⟩ := mem_filter.mp hmem
      refine ⟨mem_range.mp h1, h2, fun v hv1 hv2 hv => ?_⟩
      have := le_max' ((range t).filter fun t' => y t' = y t) v (mem_filter.mpr ⟨mem_range.mpr hv2, hv⟩)
      omega
    · rintro ⟨h1, h2, h3⟩
      refine le_antisymm ?_ (le_max' _ u (mem_filter.mpr ⟨mem_range.mpr h1, h2⟩))
      have hmem := max'_mem _ h
      obtain ⟨h4, h5⟩ := mem_filter.mp hmem
      by_contra hlt
      push Not at hlt
      exact h3 _ hlt (mem_range.mp h4) h5
  · simp only [false_iff, not_and]
    intro h1 h2
    exact absurd ⟨u, mem_filter.mpr ⟨mem_range.mpr h1, h2⟩⟩ h

/-- A step of the block DAG: a state edge, or a block edge to the last earlier visit of a block. -/
def BlockStep (s : Fin k → ℕ → ℤ) (T : ℕ) (t u : ℕ) : Prop :=
  t < T ∧ (u + 1 = t ∨ ∃ j, prevS (s j) t = some u)

/-- **Lemma 4.5(a).** The block DAG is the dependency DAG of the coarse walks. -/
theorem blockStep_iff (s : Fin k → ℕ → ℤ) (T t u : ℕ) : BlockStep s T t u ↔ DepStep s T t u := by
  constructor
  · rintro ⟨ht, h | ⟨j, hj⟩⟩
    · exact Or.inl ⟨h, ht⟩
    · obtain ⟨h1, h2, h3⟩ := prevS_spec.mp hj
      by_cases hut : u + 1 = t
      · exact Or.inl ⟨hut, ht⟩
      · have hhop : IsHop (s j) T u t := ⟨by omega, ht, h2.symm, fun v hv => by
          obtain ⟨hv1, hv2⟩ := mem_Ioo.mp hv
          rw [h2]
          exact h3 v hv1 hv2⟩
        exact Or.inr (mem_image.mpr ⟨(j, u, t), mem_allHops.mpr hhop, rfl⟩)
  · rintro (⟨h, ht⟩ | h)
    · exact ⟨ht, Or.inl h⟩
    · obtain ⟨η, hη, he⟩ := mem_image.mp h
      obtain ⟨hl, ht, heq, hin⟩ := mem_allHops.mp hη
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨ht, Or.inr ⟨η.1, prevS_spec.mpr ⟨by omega, heq.symm, fun v hv1 hv2 hv => ?_⟩⟩⟩
      exact hin v (mem_Ioo.mpr ⟨hv1, hv2⟩) (hv.trans heq)

open Classical in
/-- **Lemma 4.5(a), out-degrees.** -/
theorem card_blockOut_le (s : Fin k → ℕ → ℤ) (T t : ℕ) :
    ((range T).filter (BlockStep s T t ·)).card ≤ k + 1 := by
  have hsub : (range T).filter (BlockStep s T t ·) ⊆
      insert (t - 1) (univ.biUnion fun j : Fin k => (prevS (s j) t).toFinset) := by
    intro u hu
    obtain ⟨-, -, h | ⟨j, hj⟩⟩ := mem_filter.mp hu
    · exact mem_insert.mpr (Or.inl (by omega))
    · exact mem_insert_of_mem (mem_biUnion.mpr ⟨j, mem_univ _, by simp [hj]⟩)
  refine (card_le_card hsub).trans ((card_insert_le _ _).trans ?_)
  have : (univ.biUnion fun j : Fin k => (prevS (s j) t).toFinset).card ≤ k := by
    refine card_biUnion_le.trans ?_
    calc ∑ j : Fin k, (prevS (s j) t).toFinset.card ≤ ∑ _j : Fin k, 1 :=
          sum_le_sum fun j _ => by cases prevS (s j) t <;> simp
      _ = k := by simp
  omega

open Classical in
/-- **Lemma 4.5(a), in-degrees.** -/
theorem card_blockIn_le (s : Fin k → ℕ → ℤ) (T u : ℕ) :
    ((range T).filter (BlockStep s T · u)).card ≤ k + 1 := by
  -- for each tape at most one later time has `u` as its last earlier visit
  have huniq : ∀ j t t', prevS (s j) t = some u → prevS (s j) t' = some u → t = t' := by
    intro j t t' h h'
    obtain ⟨h1, h2, h3⟩ := prevS_spec.mp h
    obtain ⟨h1', h2', h3'⟩ := prevS_spec.mp h'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h3' t h1 hlt (h2.symm.trans h2')
    · exact h3 t' h1' hlt (h2'.symm.trans h2)
  have hsub : (range T).filter (BlockStep s T · u) ⊆
      insert (u + 1) (univ.biUnion fun j : Fin k =>
        ((range T).filter fun t => prevS (s j) t = some u)) := by
    intro t ht
    obtain ⟨htT, -, h | ⟨j, hj⟩⟩ := mem_filter.mp ht
    · exact mem_insert.mpr (Or.inl (by omega))
    · exact mem_insert_of_mem (mem_biUnion.mpr ⟨j, mem_univ _, mem_filter.mpr ⟨htT, hj⟩⟩)
  refine (card_le_card hsub).trans ((card_insert_le _ _).trans ?_)
  have : (univ.biUnion fun j : Fin k =>
      ((range T).filter fun t => prevS (s j) t = some u)).card ≤ k := by
    refine card_biUnion_le.trans ?_
    calc ∑ j : Fin k, ((range T).filter fun t => prevS (s j) t = some u).card ≤ ∑ _j : Fin k, 1 :=
          sum_le_sum fun j _ => card_le_one.mpr fun t ht t' ht' =>
            huniq j t t' (mem_filter.mp ht).2 (mem_filter.mp ht').2
      _ = k := by simp
  omega

end MergeDepth

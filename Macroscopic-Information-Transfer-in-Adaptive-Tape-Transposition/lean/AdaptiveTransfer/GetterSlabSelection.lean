import AdaptiveTransfer.SlabGeometry

/-! Chronological slab selection with an arbitrary positive visit cap.
The finite chunk construction is reused from `long_slab_chunks`; only the
averaging argument is extended from the original half-input cap.
-/

namespace AdaptiveTransfer.Getter
open Finset NativeRelations
open scoped BigOperators

/-- The same actual slab dichotomy for every positive cap B. -/
theorem exists_slab_chunk_cap {L T B : ℕ} (hL : 0 < L) (hB : 0 < B)
    {m : ℕ → ℤ} {K : Finset ℕ}
    (hK : ∀ t < T - 1, m t ≠ m (t + 1) → t ∈ K)
    {ot : Fin L → ℕ} (hot : ∀ r, ot r < T) :
    (∃ s : ℤ, ((Ico 0 T).filter (fun t => m t = s)).card ≤ B ∧
      L ≤ 2 * (K.card + 1) * (outIn ot ((Ico 0 T).filter (fun t => m t = s))).card) ∨
    (∃ (s : ℤ) (a e : ℕ), a ≤ e ∧ e ≤ T ∧
      ((Ico a e).filter (fun t => m t = s)).card ≤ B ∧
      L * B < 4 * T * (outIn ot ((Ico a e).filter (fun t => m t = s))).card) := by
  classical
  let active := (range T).image m
  let short := active.filter fun s => (slabSteps m T s).card ≤ B
  let long := active.filter fun s => ¬ (slabSteps m T s).card ≤ B
  let mass := fun s => (outIn ot (slabSteps m T s)).card
  have hall : L ≤ ∑ s ∈ active, mass s := by
    have hcov : (univ : Finset (Fin L)) ⊆ active.biUnion (fun s => outIn ot (slabSteps m T s)) := by
      intro j _
      refine mem_biUnion.mpr ⟨m (ot j), mem_image_of_mem _ (mem_range.mpr (hot j)), ?_⟩
      exact mem_filter.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_range.mpr (hot j), rfl⟩⟩
    calc
      L = (univ : Finset (Fin L)).card := (card_fin L).symm
      _ ≤ (active.biUnion (fun s => outIn ot (slabSteps m T s))).card := card_le_card hcov
      _ ≤ _ := card_biUnion_le
  have hsplit : (∑ s ∈ short, mass s) + (∑ s ∈ long, mass s) = ∑ s ∈ active, mass s :=
    sum_filter_add_sum_filter_not _ _ _
  have hico (s : ℤ) : (Ico 0 T).filter (fun t => m t = s) = slabSteps m T s := by
    ext t; simp [slabSteps]
  by_cases hs : L ≤ 2 * ∑ s ∈ short, mass s
  · have hne : short.Nonempty := by
      by_contra hh
      rw [not_nonempty_iff_eq_empty.mp hh, sum_empty, mul_zero] at hs
      omega
    obtain ⟨s, hsm, hmax⟩ := exists_max_image short mass hne
    have hsum : (∑ t ∈ short, mass t) ≤ short.card * mass s :=
      (sum_le_sum (fun t ht => hmax t ht)).trans_eq (by simp)
    have hcard : short.card ≤ K.card + 1 :=
      (card_le_card (filter_subset _ _)).trans (card_activeSlabs_le hK)
    exact Or.inl ⟨s, by simpa only [hico] using (mem_filter.mp hsm).2,
      by rw [hico]; exact hs.trans ((Nat.mul_le_mul_left 2 hsum).trans
        (by change 2 * (short.card * mass s) ≤ 2 * (K.card + 1) * mass s
            nlinarith [Nat.mul_le_mul_right (mass s) hcard]))⟩
  · have hlong : L < 2 * ∑ s ∈ long, mass s := by omega
    let count (s : ℤ) := ((slabSteps m T s).card + B - 1) / B
    have chunks (s : ℤ) (hs : s ∈ long) :
        count s * B ≤ 2 * (slabSteps m T s).card ∧
        ∃ lo hi : ℕ → ℕ,
          (∀ i < count s, lo i ≤ hi i ∧ hi i ≤ T ∧
            ((Ico (lo i) (hi i)).filter fun t => m t = s).card ≤ B) ∧
          mass s ≤ ∑ i ∈ range (count s),
            (outIn ot ((Ico (lo i) (hi i)).filter fun t => m t = s)).card :=
      long_slab_chunks hB s (by have := (mem_filter.mp hs).2; omega) ot
    let lo (s : ℤ) := if hs : s ∈ long then (chunks s hs).2.choose else fun _ => 0
    let hi (s : ℤ) := if hs : s ∈ long then (chunks s hs).2.choose_spec.choose else fun _ => 0
    have spec (s : ℤ) (hs : s ∈ long) := (chunks s hs).2.choose_spec.choose_spec
    have spec' (s : ℤ) (hs : s ∈ long) :
        (∀ i < count s, lo s i ≤ hi s i ∧ hi s i ≤ T ∧
          ((Ico (lo s i) (hi s i)).filter fun t => m t = s).card ≤ B) ∧
        mass s ≤ ∑ i ∈ range (count s),
          (outIn ot ((Ico (lo s i) (hi s i)).filter fun t => m t = s)).card := by
      simpa only [lo, hi, dite_eq_left hs] using spec s hs
    let indices := long.sigma fun s => range (count s)
    let weight (i : ℤ × ℕ) := (outIn ot ((Ico (lo i.1 i.2) (hi i.1 i.2)).filter
      fun t => m t = i.1)).card
    let wt (i : Sigma fun _ : ℤ => ℕ) := weight (i.1, i.2)
    have htotal : L < 2 * ∑ i ∈ indices, wt i := by
      rw [sum_sigma]
      exact hlong.trans_le (Nat.mul_le_mul_left 2 (sum_le_sum fun s hs => (spec' s hs).2))
    have hdisj : (long : Set ℤ).PairwiseDisjoint (slabSteps m T) := by
      intro s _ t _ hst
      simp only [Function.onFun]
      exact disjoint_left.mpr fun u hu hv => hst ((mem_filter.mp hu).2.symm.trans (mem_filter.mp hv).2)
    have hsum : (∑ s ∈ long, (slabSteps m T s).card) ≤ T := by
      rw [← card_biUnion hdisj]
      exact (card_le_card (show long.biUnion (slabSteps m T) ⊆ range T from
        fun t ht => by obtain ⟨s, _, hs⟩ := mem_biUnion.mp ht; exact (mem_filter.mp hs).1)).trans_eq (card_range _)
    have hcount : indices.card * B ≤ 2 * T := by
      rw [card_sigma, sum_mul]
      simp only [card_range]
      exact (sum_le_sum (fun s hs => (chunks s hs).1)).trans
        (by simpa only [← mul_sum] using Nat.mul_le_mul_left 2 hsum)
    have hne : indices.Nonempty := by
      by_contra hh
      rw [not_nonempty_iff_eq_empty.mp hh, sum_empty, mul_zero] at htotal
      omega
    obtain ⟨i, hi', hmax⟩ := exists_max_image indices wt hne
    obtain ⟨his, hii⟩ := mem_sigma.mp hi'
    have hsumwt : (∑ j ∈ indices, wt j) ≤ indices.card * wt i :=
      (sum_le_sum (fun j hj => hmax j hj)).trans_eq (by simp)
    obtain ⟨hle, hT, hcard⟩ := (spec' i.1 his).1 i.2 (mem_range.mp hii)
    refine Or.inr ⟨i.1, lo i.1 i.2, hi i.1 i.2, hle, hT, hcard, ?_⟩
    calc
      L * B < (2 * indices.card * wt i) * B := Nat.mul_lt_mul_of_pos_right
        (htotal.trans_le (by nlinarith [hsumwt])) hB
      _ = 2 * (indices.card * B) * wt i := by ring
      _ ≤ 2 * (2 * T) * wt i := by gcongr
      _ = _ := by dsimp [wt, weight]; ring

end AdaptiveTransfer.Getter

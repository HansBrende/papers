import LeanMachine.MonotoneChainEnvelope

/-! # Normalized charts from finite order conflicts

Prefix maxima are indexed by the coordinate sums, so no arbitrary ordering of
points with tied sums is needed. The stronger statement permits a separate
conflict allowance in each coordinate.
-/

namespace LeanMachine.OrderConflictChart

open Finset
open MonotoneChain (total)

variable {I H : Type*} [Fintype I] [Nonempty I] [Fintype H] [Nonempty H]

noncomputable def lowerSet (v : I → H → ℝ) (i : I) : Finset I := by
  classical
  exact univ.filter (fun j => total v j ≤ total v i)

omit [Nonempty I] [Nonempty H] in
private theorem mem_prefix_self (v : I → H → ℝ) (i : I) : i ∈ lowerSet v i := by
  classical
  simp [lowerSet]

omit [Nonempty I] [Nonempty H] in
private theorem prefix_nonempty (v : I → H → ℝ) (i : I) : (lowerSet v i).Nonempty :=
  ⟨i, mem_prefix_self v i⟩

noncomputable def prefixMaximum (v : I → H → ℝ) (i : I) (h : H) : ℝ :=
  (lowerSet v i).sup' (prefix_nonempty v i) (fun j => v j h)

omit [Nonempty I] [Nonempty H] in
theorem le_prefixMaximum (v : I → H → ℝ) (i : I) (h : H) :
    v i h ≤ prefixMaximum v i h :=
  by simpa only [prefixMaximum] using
    Finset.le_sup' (fun j => v j h) (mem_prefix_self v i)

omit [Nonempty I] [Nonempty H] in
theorem prefixMaximum_le (v : I → H → ℝ) (D : H → ℝ)
    (hD : ∀ i j, total v i ≤ total v j → ∀ h, v i h - v j h ≤ D h)
    (i : I) (h : H) : prefixMaximum v i h ≤ v i h + D h := by
  classical
  apply Finset.sup'_le
  intro j hj
  have hh := hD j i (by simpa [lowerSet] using hj) h
  linarith

omit [Nonempty I] [Nonempty H] in
theorem prefixMaximum_mono (v : I → H → ℝ) {i j : I}
    (hij : total v i ≤ total v j) (h : H) :
    prefixMaximum v i h ≤ prefixMaximum v j h := by
  classical
  apply Finset.sup'_le
  intro l hl
  unfold prefixMaximum
  apply Finset.le_sup' (fun l => v l h)
  have hli : total v l ≤ total v i := by simpa [lowerSet] using hl
  simpa [lowerSet] using hli.trans hij

omit [Nonempty I] [Nonempty H] in
theorem prefixMaximum_chain (v : I → H → ℝ) (i j : I) :
    (∀ h, prefixMaximum v i h ≤ prefixMaximum v j h) ∨
      (∀ h, prefixMaximum v j h ≤ prefixMaximum v i h) := by
  rcases le_total (total v i) (total v j) with hij | hji
  · exact Or.inl (prefixMaximum_mono v hij)
  · exact Or.inr (prefixMaximum_mono v hji)

/-- Coordinate-specific conflicts give coordinate-specific upper errors. The
lower error is the negative sum of the other coordinates' allowances. -/
theorem exists_coordinate_chart [DecidableEq H] (v : I → H → ℝ) (D : H → ℝ)
    (hD : ∀ i j, total v i ≤ total v j → ∀ h, v i h - v j h ≤ D h) :
    ∃ f : H → ℝ → ℝ,
      (∀ h, Monotone (f h)) ∧
      (∀ h, LipschitzWith 1 (f h)) ∧
      (∀ z, (∑ h, f h z) = z) ∧
      (∀ i h, -(∑ l ∈ univ.erase h, D l) ≤ f h (total v i) - v i h ∧
        f h (total v i) - v i h ≤ D h) := by
  classical
  obtain ⟨f, hm, hl, hs, hk⟩ :=
    MonotoneChain.exists_normalized_chain (prefixMaximum v) (prefixMaximum_chain v)
  have ht : ∀ i, total v i ≤ total (prefixMaximum v) i := by
    intro i
    exact Finset.sum_le_sum (fun h _ => le_prefixMaximum v i h)
  have hu : ∀ i h, f h (total v i) - v i h ≤ D h := by
    intro i h
    have h₁ := hm h (ht i)
    rw [hk] at h₁
    have h₂ := prefixMaximum_le v D hD i h
    linarith
  refine ⟨f, hm, hl, hs, ?_⟩
  intro i h
  refine ⟨?_, hu i h⟩
  have hzero : (∑ l, (f l (total v i) - v i l)) = 0 := by
    rw [Finset.sum_sub_distrib, hs]
    simp only [total, sub_self]
  have heq := Finset.sum_erase_add univ
    (fun l => f l (total v i) - v i l) (mem_univ h)
  rw [hzero] at heq
  have hle : (∑ l ∈ univ.erase h, (f l (total v i) - v i l)) ≤
      ∑ l ∈ univ.erase h, D l :=
    Finset.sum_le_sum (fun l _ => hu i l)
  linarith

/-- The uniform order-conflict chart used for coherent clusters of tape heads. -/
theorem exists_chart (v : I → H → ℝ) (D : ℝ)
    (hD : ∀ i j, total v i ≤ total v j → ∀ h, v i h - v j h ≤ D) :
    ∃ f : H → ℝ → ℝ,
      (∀ h, Monotone (f h)) ∧
      (∀ h, LipschitzWith 1 (f h)) ∧
      (∀ z, (∑ h, f h z) = z) ∧
      (∀ i h, -((Fintype.card H : ℝ) - 1) * D ≤ f h (total v i) - v i h ∧
        f h (total v i) - v i h ≤ D) := by
  classical
  obtain ⟨f, hm, hl, hs, hb⟩ := exists_coordinate_chart v (fun _ => D) hD
  refine ⟨f, hm, hl, hs, ?_⟩
  intro i h
  have heq : (∑ l ∈ univ.erase h, D) = ((Fintype.card H : ℝ) - 1) * D := by
    have hh := Finset.sum_erase_add univ (fun _ : H => D) (mem_univ h)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh ⊢
    linarith
  simpa only [heq, neg_mul] using hb i h

omit [Fintype I] [Nonempty I] [Nonempty H] in
/-- Monotonicity and two approximation errors bound every ordered conflict.
Neither normalization nor the Lipschitz property is needed for this direction. -/
theorem conflict_le_two_error (v : I → H → ℝ) (f : H → ℝ → ℝ) (J : ℝ)
    (hm : ∀ h, Monotone (f h))
    (herr : ∀ i h, |f h (total v i) - v i h| ≤ J)
    {i j : I} (hij : total v i ≤ total v j) (h : H) :
    v i h - v j h ≤ 2 * J := by
  have hi := (abs_le.mp (herr i h)).1
  have hj := (abs_le.mp (herr j h)).2
  have hmono := hm h hij
  linarith


/-- The literal maximum of the positive ordered coordinate conflicts. Entries
with the wrong sum order contribute zero. -/
noncomputable def orderConflict (v : I → H → ℝ) : ℝ := by
  classical
  exact univ.sup' univ_nonempty (fun x : I × I × H =>
    if total v x.1 ≤ total v x.2.1 then max (v x.1 x.2.2 - v x.2.1 x.2.2) 0 else 0)

theorem conflict_le_orderConflict (v : I → H → ℝ) {i j : I}
    (hij : total v i ≤ total v j) (h : H) :
    v i h - v j h ≤ orderConflict v := by
  classical
  have hh := Finset.le_sup' (fun x : I × I × H =>
    if total v x.1 ≤ total v x.2.1 then max (v x.1 x.2.2 - v x.2.1 x.2.2) 0 else 0)
      (mem_univ (i, j, h))
  simp only [hij, ite_true] at hh
  exact (le_max_left _ _).trans hh

/-- Exact finite-max formulation of the order-conflict chart theorem. -/
theorem exists_order_conflict_chart (v : I → H → ℝ) :
    ∃ f : H → ℝ → ℝ,
      (∀ h, Monotone (f h)) ∧
      (∀ h, LipschitzWith 1 (f h)) ∧
      (∀ z, (∑ h, f h z) = z) ∧
      (∀ i h, -((Fintype.card H : ℝ) - 1) * orderConflict v ≤
          f h (total v i) - v i h ∧
        f h (total v i) - v i h ≤ orderConflict v) :=
  exists_chart v (orderConflict v) (fun _ _ hij h => conflict_le_orderConflict v hij h)

/-- A normalized chart of error at most `J` has order conflict at most `2J`.
The proof only requires monotonicity, so it also applies to any larger chart class. -/
theorem orderConflict_le_two_error (v : I → H → ℝ) (f : H → ℝ → ℝ) (J : ℝ)
    (hm : ∀ h, Monotone (f h))
    (herr : ∀ i h, |f h (total v i) - v i h| ≤ J) : orderConflict v ≤ 2 * J := by
  classical
  have hJ : 0 ≤ J := (abs_nonneg _).trans
    (herr (Classical.arbitrary I) (Classical.arbitrary H))
  apply Finset.sup'_le
  intro x _
  split_ifs with hij
  · exact max_le (conflict_le_two_error v f J hm herr hij _) (by positivity)
  · positivity

end LeanMachine.OrderConflictChart

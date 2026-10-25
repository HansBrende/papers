import SubcubicMemo.ReversibleRules

/-! Invertible-block recovery and the exact scalar statements as corollaries. -/

namespace SubcubicMemo

open Finset Module MotionDepthCodes
open scoped BigOperators

variable {V K A : Type*} [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup A] [Module K A] [FiniteDimensional K A]

omit [DecidableEq V] [FiniteDimensional K A] in
/-- A row whose participating coefficient maps are injective is reversible
on any set satisfying the homogeneous row equations. -/
theorem injective_block_rules {T : V → V → A →ₗ[K] A} {C : Set (V → A)}
    (hrow : ∀ f ∈ C, ∀ v, ∑ u, T v u (f u) = 0)
    (hinj : ∀ v u, T v u ≠ 0 → Function.Injective (T v u)) :
    ∀ v x, T v x ≠ 0 → ∀ f ∈ C, ∀ g ∈ C,
      (∀ y, T v y ≠ 0 → y ≠ x → f y = g y) → f x = g x := by
  intro v x hTx f hf g hg heq
  have hsum : ∑ u, T v u (f u - g u) = 0 := by
    simp only [map_sub, sum_sub_distrib, hrow f hf, hrow g hg, sub_self]
  have hzero : ∀ u ∈ univ, u ≠ x → T v u (f u - g u) = 0 := by
    intro u _ hux
    by_cases hTu : T v u = 0
    · simp [hTu]
    · simp [heq u hTu hux]
  rw [sum_eq_single x hzero (fun hn => False.elim (hn (mem_univ _)))] at hsum
  have : f x - g x = 0 := hinj v x hTx (hsum.trans (map_zero (T v x)).symm)
  exact sub_eq_zero.mp this

omit [FiniteDimensional K A] in
/-- Nonzero injective edge blocks suffice; in finite dimension these are exactly
the invertible participating blocks. All fields and all finite widths are allowed. -/
theorem injective_block_information_set [Nontrivial A]
    {G : SimpleGraph V} [DecidableRel G.Adj] (T : V → V → A →ₗ[K] A)
    (hdiag : ∀ v, T v v = LinearMap.id)
    (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → T v u = 0)
    (hinj : ∀ v u, T v u ≠ 0 → Function.Injective (T v u))
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    ∃ B : Finset V, B.card ≤ G.matchingNumber ∧
      ∀ C : Set (V → A), (∀ f ∈ C, ∀ v, ∑ u, T v u (f u) = 0) →
        Function.Injective (fun f : C => fun v : B => (f : V → A) v) := by
  classical
  let R : V → Finset V := fun v => univ.filter (fun u => T v u ≠ 0)
  have hself : ∀ v, v ∈ R v := by
    intro v
    simp only [R, mem_filter, mem_univ, true_and, hdiag]
    exact one_ne_zero
  have hlocal : ∀ v u, u ∈ R v → u ≠ v → G.Adj v u := by
    intro v u hu huv
    by_contra hnot
    exact (mem_filter.mp hu).2 (hpat v u huv.symm hnot)
  obtain ⟨B, hcard, hB⟩ := named_rules_information_set R hself hlocal htri hdeg
  refine ⟨B, hcard, ?_⟩
  intro C hrow
  apply hB
  intro v x hx f hf g hg heq
  apply injective_block_rules hrow hinj v x (mem_filter.mp hx).2 f hf g hg
  intro y hy hyx
  exact heq y (mem_filter.mpr ⟨mem_univ _, hy⟩) hyx

theorem injective_block_finrank_le
    {G : SimpleGraph V} [DecidableRel G.Adj] (T : V → V → A →ₗ[K] A)
    (C : Submodule K (V → A)) (hdiag : ∀ v, T v v = LinearMap.id)
    (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → T v u = 0)
    (hinj : ∀ v u, T v u ≠ 0 → Function.Injective (T v u))
    (hrow : ∀ f ∈ C, ∀ v, ∑ u, T v u (f u) = 0)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    finrank K C ≤ G.matchingNumber * finrank K A := by
  classical
  cases subsingleton_or_nontrivial A with
  | inl hA =>
    let := hA
    simp [Module.finrank_zero_of_subsingleton]
  | inr hA =>
    let := hA
    obtain ⟨B, hcard, hB⟩ := injective_block_information_set T hdiag hpat hinj htri hdeg
    let f : C →ₗ[K] (B → A) :=
      { toFun := fun x v => x.val v
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hdim := LinearMap.finrank_le_finrank_of_injective (f := f) (hB C hrow)
    have hcod : finrank K (B → A) = B.card * finrank K A := by
      simp [Module.finrank_pi_fintype]
    rw [hcod] at hdim
    exact hdim.trans (Nat.mul_le_mul_right _ hcard)

/-- The original graph-specialized scalar nullity bound follows directly from
the new reversible-rule theorem. -/
theorem original_graph_matching {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Matrix V V K} (hdiag : ∀ v, M v v = 1)
    (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    finrank K (LinearMap.ker M.mulVecLin) ≤ G.matchingNumber := by
  classical
  apply original_matching_bound (thmSHyp_of_cliqueFree hdiag hpat htri) _
    (star_of_degree_le_three hpat hdeg)
  intro v u hu
  obtain ⟨hne, hMu⟩ := mem_recSet.mp hu
  by_contra hnot
  exact hMu (hpat v u hne.symm hnot)

/-- Both clauses of the original minrank equality. Only its matching-code
construction is reused; the upper-nullity argument is the stronger theorem. -/
theorem original_minrank {G : SimpleGraph V} [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    (∀ M : Matrix V V K, (∀ v, M v v = 1) →
      (∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0) →
      Fintype.card V - G.matchingNumber ≤ M.rank) ∧
      ∃ M : Matrix V V K, (∀ v, M v v = 1) ∧
        (∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0) ∧
        M.rank = Fintype.card V - G.matchingNumber := by
  have hrank : ∀ M : Matrix V V K,
      M.rank + finrank K (LinearMap.ker M.mulVecLin) = Fintype.card V := by
    intro M
    have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at h
    exact h
  refine ⟨?_, ?_⟩
  · intro M hdiag hpat
    have h := original_graph_matching hdiag hpat htri hdeg
    have := hrank M
    omega
  · obtain ⟨M, hdiag, hpat, hlo⟩ :=
      exists_pattern_matchingNumber_le_finrank_ker (F := K) (G := G)
    have hhi := original_graph_matching hdiag hpat htri hdeg
    have := hrank M
    exact ⟨M, hdiag, hpat, by omega⟩

end SubcubicMemo

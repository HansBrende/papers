import AdaptiveTransfer.LocalSnapshots

/-! Actual pre-step snapshots for protected-core clusters. Only complementary
heads contribute long-return targets; every clustered fringe is paid at each
original selected-run entry, and every core is paid once at a positive start. -/

namespace AdaptiveTransfer
open Transpose Finset NativeRelations BoundedNesting

noncomputable def offClusterReturns {k : ℕ} (xs : Fin k → ℕ → ℤ)
    (cluster : Finset (Fin k)) (T H : ℕ) : Finset (Fin k × ℕ × ℕ) := by
  classical
  exact (allHops xs T).filter fun e => e.1 ∉ cluster ∧
    ∃ u ∈ Ioo e.2.1 e.2.2, H < (xs e.1 u - xs e.1 e.2.1).natAbs

noncomputable def offClusterLowerEndpoints {k : ℕ} (xs : Fin k → ℕ → ℤ)
    (cluster : Finset (Fin k)) (T H : ℕ) : Finset ℕ :=
  (offClusterReturns xs cluster T H).image fun e => e.2.1

namespace ExecutionPrefix
variable {M : TM} {w : List Bool} {T : ℕ}

noncomputable def clusterSnapshot (E : ExecutionPrefix M w T) (C : Finset ℕ)
    (cluster : Finset (Fin M.k)) (core fringe : Fin M.k → Finset ℤ)
    (a H : ℕ) (h : Fin M.k) (t : ℕ) (z : ℤ) : Option (Fin (M.g + 1)) :=
  if h ∈ cluster then
    if (a ≠ 0 ∧ t = a ∧ z ∈ core h) ∨ (t ∈ runStarts C ∧ z ∈ fringe h)
    then some ((E.config t).work h z) else none
  else if t ∈ runStarts C ∧ (z - (E.config t).workPos h).natAbs ≤ H
    then some ((E.config t).work h z) else none

theorem clusterSnapshot_sound (E : ExecutionPrefix M w T) (C : Finset ℕ)
    (cluster : Finset (Fin M.k)) (core fringe : Fin M.k → Finset ℤ)
    (a H : ℕ) (h : Fin M.k) (t : ℕ) (z : ℤ) (s : Fin (M.g + 1))
    (hs : E.clusterSnapshot C cluster core fringe a H h t z = some s) : s = (E.config t).work h z := by
  unfold clusterSnapshot at hs
  split_ifs at hs <;> simp_all

/-- The exhaustive actual latest-parent argument works for every protected
core and paid fringe, with a full original-graph separator on the complement. -/
theorem clusterSnapshot_parent_coverage (E : ExecutionPrefix M w T)
    (C roots B : Finset ℕ) (cluster : Finset (Fin M.k)) (core fringe : Fin M.k → Finset ℤ)
    (a b H : ℕ) (hCT : ∀ t ∈ C, a ≤ t ∧ t < b) (hbT : b ≤ T)
    (hcover : ∀ t ∈ C, ∀ h ∈ cluster, (E.config t).workPos h ∈ core h ∪ fringe h)
    (houtside : ∀ u, a ≤ u → u < b → u ∉ C → ∀ h ∈ cluster,
      (E.config u).workPos h ∉ core h)
    (hsep : IsMengerVertexCut (fun h t => (E.config t).workPos h) T roots
      (offClusterLowerEndpoints (fun h t => (E.config t).workPos h) cluster T H) B)
    {t : ℕ} (ht : t ∈ localAncestors (fun h t => (E.config t).workPos h) T roots C B)
    (h : Fin M.k) {p : ℕ} (hpt : p < t)
    (hpos : (E.config t).workPos h = (E.config p).workPos h)
    (hlast : ∀ u, p < u → u < t → (E.config t).workPos h ≠ (E.config u).workPos h) :
    p ∈ localAncestors (fun h t => (E.config t).workPos h) T roots C B ∪ B ∨
      ∃ s, p < s ∧ s ≤ t ∧
        (E.clusterSnapshot C cluster core fringe a H h s ((E.config t).workPos h)).isSome := by
  classical
  have htC := localAncestors_subset ht
  have htbound := hCT t htC
  have htT : t < T := htbound.2.trans_le hbT
  have hdep := depStep_of_last_visit (xs := fun h u => (E.config u).workPos h) h htT hpt hpos hlast
  by_cases hh : h ∈ cluster
  · rcases mem_union.mp (hcover t htC h hh) with hc | hf
    · by_cases hap : a ≤ p
      · left
        apply localAncestors_parent_inside ht hdep
        by_contra hpC
        exact houtside p hap (hpt.trans htbound.2) hpC h hh (hpos ▸ hc)
      · right
        refine ⟨a, by omega, htbound.1, ?_⟩
        simp only [clusterSnapshot, hh, ite_true]
        have ha : a ≠ 0 := by omega
        simp only [ha, ne_eq, not_false_eq_true, hc, and_self, true_or, ite_true, Option.isSome_some]
    · obtain ⟨r, hr, hrt, hte⟩ := exists_run_cover (fun u hu => (hCT u hu).2.trans_le hbT) htC
      by_cases hrp : r ≤ p
      · exact Or.inl (localAncestors_parent_inside ht hdep
          ((runEnd_spec (fun u hu => (hCT u hu).2.trans_le hbT) hr).2.2.2 p
            (mem_Ico.mpr ⟨hrp, hpt.trans hte⟩)))
      · refine Or.inr ⟨r, by omega, hrt, ?_⟩
        simp only [clusterSnapshot, hh, ite_true, hr, hf, and_self, or_true, Option.isSome_some]
  · obtain ⟨r, hr, hrt, hte⟩ := exists_run_cover (fun u hu => (hCT u hu).2.trans_le hbT) htC
    by_cases hrp : r ≤ p
    · exact Or.inl (localAncestors_parent_inside ht hdep
        ((runEnd_spec (fun u hu => (hCT u hu).2.trans_le hbT) hr).2.2.2 p
          (mem_Ico.mpr ⟨hrp, hpt.trans hte⟩)))
    · by_cases hz : ((E.config t).workPos h - (E.config r).workPos h).natAbs ≤ H
      · refine Or.inr ⟨r, by omega, hrt, ?_⟩
        simp only [clusterSnapshot, hh, ite_false, hr, hz, and_self, ite_true, Option.isSome_some]
      · have hfar : H < ((E.config t).workPos h - (E.config r).workPos h).natAbs := by omega
        have hrt' : r < t := by
          by_contra hn
          have he : r = t := by omega
          simp only [he, sub_self, Int.natAbs_zero] at hfar
          omega
        have hreturn : (h, p, t) ∈ offClusterReturns
            (fun h t => (E.config t).workPos h) cluster T H := by
          apply mem_filter.mpr
          change (h, p, t) ∈ allHops (fun h u => (E.config u).workPos h) T ∧ h ∉ cluster ∧
            ∃ u ∈ Ioo p t, H < ((E.config u).workPos h - (E.config p).workPos h).natAbs
          refine ⟨mem_allHops.mpr (show IsHop (fun u => (E.config u).workPos h) T p t from
            ⟨by omega, htT, hpos, ?_⟩), hh, r, mem_Ioo.mpr ⟨by omega, hrt'⟩, ?_⟩
          · intro u hu he
            exact hlast u (mem_Ioo.mp hu).1 (mem_Ioo.mp hu).2 (hpos.trans he.symm)
          · rw [← hpos, ← Int.natAbs_neg, neg_sub]
            exact hfar
        have hpY : p ∈ offClusterLowerEndpoints
            (fun h t => (E.config t).workPos h) cluster T H :=
          mem_image.mpr ⟨(h, p, t), hreturn, rfl⟩
        exact Or.inl (mem_union_right _ (localAncestors_target_parent_cut hsep ht hdep hpY))


end ExecutionPrefix
end AdaptiveTransfer

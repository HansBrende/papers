import AdaptiveTransfer.LocalAncestors
import AdaptiveTransfer.LocalFragmentReplay
import AdaptiveTransfer.ReturnImports
import AdaptiveTransfer.ReplayGeometry

/-! Actual localized snapshots and their original-graph coverage. The free
slab snapshot is paid only at a positive outer start. Every other snapshot is
an ordinary entry window; exterior long-return parents are paid cut steps. -/

namespace AdaptiveTransfer
open Transpose Finset NativeRelations BoundedNesting

namespace ExecutionPrefix
variable {M : TM} {w v : List Bool} {T : ℕ}

noncomputable def localSnapshot (E : ExecutionPrefix M w T) (C : Finset ℕ) (S : Finset ℤ)
    (a H : ℕ) (f : Fin M.k) (h : Fin M.k) (t : ℕ) (z : ℤ) : Option (Fin (M.g + 1)) :=
  if h = f then
    if a ≠ 0 ∧ t = a ∧ z ∈ S then some ((E.config t).work h z) else none
  else if t ∈ runStarts C ∧ (z - (E.config t).workPos h).natAbs ≤ H then
    some ((E.config t).work h z) else none

theorem localSnapshot_sound (E : ExecutionPrefix M w T) (C : Finset ℕ) (S : Finset ℤ)
    (a H : ℕ) (f h : Fin M.k) (t : ℕ) (z : ℤ) (s : Fin (M.g + 1))
    (hs : E.localSnapshot C S a H f h t z = some s) : s = (E.config t).work h z := by
  unfold localSnapshot at hs
  split_ifs at hs <;> simp_all

theorem localSnapshot_free (E : ExecutionPrefix M w T) (C : Finset ℕ) (S : Finset ℤ)
    {a H : ℕ} (f : Fin M.k) (ha : a ≠ 0) {z : ℤ} (hz : z ∈ S) :
    (E.localSnapshot C S a H f f a z).isSome := by
  simp [localSnapshot, ha, hz]

theorem localSnapshot_window (E : ExecutionPrefix M w T) {C : Finset ℕ} (S : Finset ℤ)
    (a H : ℕ) {f h : Fin M.k} (hh : h ≠ f) {r : ℕ} (hr : r ∈ runStarts C)
    {z : ℤ} (hz : (z - (E.config r).workPos h).natAbs ≤ H) :
    (E.localSnapshot C S a H f h r z).isSome := by
  simp only [localSnapshot, ite_eq_right hh, hr, hz, and_self, ite_true, Option.isSome_some]

/-- Paid ordinary records determine every overlay, including overlaps and
snapshot/cut ties. Cells outside each window are left unchanged. -/
theorem localSnapshot_eq_of_paid (E : ExecutionPrefix M w T) {T' : ℕ} (F : ExecutionPrefix M v T')
    (C : Finset ℕ) (S : Finset ℤ) (a H : ℕ) (f : Fin M.k)
    (hpos : ∀ r ∈ runStarts C, (E.config r).workPos = (F.config r).workPos)
    (hfree : a ≠ 0 → ∀ z ∈ S, (E.config a).work f z = (F.config a).work f z)
    (hwindow : ∀ r ∈ runStarts C, ∀ h, h ≠ f → ∀ z,
      (z - (E.config r).workPos h).natAbs ≤ H → (E.config r).work h z = (F.config r).work h z)
    (h : Fin M.k) (t : ℕ) : E.localSnapshot C S a H f h t = F.localSnapshot C S a H f h t := by
  funext z
  by_cases hh : h = f
  · subst h
    simp only [localSnapshot, ite_true]
    by_cases hcond : a ≠ 0 ∧ t = a ∧ z ∈ S
    · simp only [hcond.2.1, hfree hcond.1 z hcond.2.2]
    · simp only [ite_eq_right hcond]
  · simp only [localSnapshot, ite_eq_right hh]
    by_cases ht : t ∈ runStarts C
    · have hp := congrFun (hpos t ht) h
      simp only [ht, true_and, ← hp]
      by_cases hz : (z - (E.config t).workPos h).natAbs ≤ H
      · simp only [ite_eq_left hz, hwindow t ht h hh z hz]
      · simp only [ite_eq_right hz]
    · simp only [ht, false_and, ite_false]

end ExecutionPrefix

noncomputable def offCarrierLowerEndpoints {k : ℕ} (xs : Fin k → ℕ → ℤ)
    (f : Fin k) (T H : ℕ) : Finset ℕ :=
  (offCarrierReturns xs f T H).image fun e => e.2.1

namespace ExecutionPrefix
variable {M : TM} {w : List Bool} {T : ℕ}

/-- Every actual last parent of a localized retained read is kept, cut, or
covered by a later paid snapshot. The separator targets all original long
return lowers, including those outside the selected chunk. -/
theorem localSnapshot_parent_coverage (E : ExecutionPrefix M w T)
    (C Sroots B : Finset ℕ) (S : Finset ℤ) (a b H : ℕ) (f : Fin M.k)
    (hCT : ∀ t ∈ C, a ≤ t ∧ t < b) (hbT : b ≤ T)
    (hcarrier : ∀ t, a ≤ t → t < b → (t ∈ C ↔ (E.config t).workPos f ∈ S))
    (hsep : IsMengerVertexCut (fun h t => (E.config t).workPos h) T Sroots
      (offCarrierLowerEndpoints (fun h t => (E.config t).workPos h) f T H) B)
    {t : ℕ} (ht : t ∈ localAncestors (fun h t => (E.config t).workPos h) T Sroots C B)
    (h : Fin M.k) {p : ℕ} (hpt : p < t)
    (hpos : (E.config t).workPos h = (E.config p).workPos h)
    (hlast : ∀ u, p < u → u < t → (E.config t).workPos h ≠ (E.config u).workPos h) :
    p ∈ localAncestors (fun h t => (E.config t).workPos h) T Sroots C B ∪ B ∨
      ∃ s, p < s ∧ s ≤ t ∧ (E.localSnapshot C S a H f h s ((E.config t).workPos h)).isSome := by
  classical
  have htC := localAncestors_subset ht
  have htbound := hCT t htC
  have htT : t < T := htbound.2.trans_le hbT
  have hdep := depStep_of_last_visit (xs := fun h u => (E.config u).workPos h) h htT hpt hpos hlast
  by_cases hh : h = f
  · subst h
    have hzS := (hcarrier t htbound.1 htbound.2).mp htC
    by_cases hap : a ≤ p
    · left
      apply localAncestors_parent_inside ht hdep
      exact (hcarrier p hap (hpt.trans htbound.2)).mpr (hpos ▸ hzS)
    · right
      exact ⟨a, by omega, htbound.1, E.localSnapshot_free C S f (by omega) hzS⟩
  · obtain ⟨r, hr, hrt, hte⟩ := exists_run_cover (fun u hu => (hCT u hu).2.trans_le hbT) htC
    by_cases hrp : r ≤ p
    · exact Or.inl (localAncestors_parent_inside ht hdep
        ((runEnd_spec (fun u hu => (hCT u hu).2.trans_le hbT) hr).2.2.2 p
          (mem_Ico.mpr ⟨hrp, hpt.trans hte⟩)))
    · by_cases hz : ((E.config t).workPos h - (E.config r).workPos h).natAbs ≤ H
      · exact Or.inr ⟨r, by omega, hrt, E.localSnapshot_window S a H hh hr hz⟩
      · have hfar : H < ((E.config t).workPos h - (E.config r).workPos h).natAbs := by omega
        have hrt' : r < t := by
          by_contra hn
          have he : r = t := by omega
          simp only [he, sub_self, Int.natAbs_zero] at hfar
          omega
        have hreturn : (h, p, t) ∈ offCarrierReturns (fun h t => (E.config t).workPos h) f T H := by
          apply mem_filter.mpr
          change (h, p, t) ∈ allHops (fun h u => (E.config u).workPos h) T ∧ h ≠ f ∧
            ∃ u ∈ Ioo p t, H < ((E.config u).workPos h - (E.config p).workPos h).natAbs
          refine ⟨mem_allHops.mpr (show IsHop (fun u => (E.config u).workPos h) T p t from
            ⟨by omega, htT, hpos, ?_⟩), hh, r, mem_Ioo.mpr ⟨by omega, hrt'⟩, ?_⟩
          · intro u hu he
            exact hlast u (mem_Ioo.mp hu).1 (mem_Ioo.mp hu).2 (hpos.trans he.symm)
          · rw [← hpos, ← Int.natAbs_neg, neg_sub]
            exact hfar
        have hpY : p ∈ offCarrierLowerEndpoints (fun h t => (E.config t).workPos h) f T H :=
          mem_image.mpr ⟨(h, p, t), hreturn, rfl⟩
        exact Or.inl (mem_union_right _ (localAncestors_target_parent_cut hsep ht hdep hpY))

end ExecutionPrefix
end AdaptiveTransfer

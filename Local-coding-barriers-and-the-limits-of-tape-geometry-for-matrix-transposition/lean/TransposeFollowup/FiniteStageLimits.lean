import TransposeFollowup.StageRealGeometry
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Topology.Order.OrderClosed

/-! Finite stage coverage passes to endpoint limits by finite additivity and
ordinary limits of sums. Collapsed stages are permitted. No convergence theorem
for measures, or extra limiting coverage hypothesis, is needed. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology MeasureTheory
open scoped BigOperators
set_option autoImplicit false

theorem finite_stageRegion_omission {κ : Type*} (Q : Finset κ)
    {l r : κ → ℝ} {H : ℝ} (hH : 0 ≤ H)
    (hb : ∀ k ∈ Q, 0 ≤ l k ∧ l k ≤ r k ∧ r k ≤ H)
    (hd : (Q : Set κ).PairwiseDisjoint (fun k => Ico (l k) (r k))) :
    volume.real (Ico 0 H \ stageRegion l r (Q : Set κ))=
      H-∑ k ∈ Q, (r k-l k) := by
  have hs : stageRegion l r (Q : Set κ) ⊆ Ico 0 H := by
    intro x hx
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hk,hxk⟩ := Set.mem_iUnion.mp hk
    exact ⟨(hb k hk).1.trans hxk.1,hxk.2.trans_le (hb k hk).2.2⟩
  have hm : MeasurableSet (stageRegion l r (Q : Set κ)) :=
    MeasurableSet.biUnion Q.countable_toSet (fun _ _ => measurableSet_Ico)
  have hf : ∀ k ∈ Q, volume (Ico (l k) (r k)) ≠ ⊤ := by
    intro k hk
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  have hclock : volume (Ico (0 : ℝ) H) ≠ ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  rw [measureReal_sdiff hs hm hclock,Real.volume_real_Ico_of_le hH,sub_zero]
  change H-volume.real (⋃ k ∈ Q, Ico (l k) (r k))=H-∑ k ∈ Q, (r k-l k)
  rw [measureReal_biUnion_finset hd (fun _ _ => measurableSet_Ico) hf]
  congr 1
  exact Finset.sum_congr rfl (fun k hk => Real.volume_real_Ico_of_le (hb k hk).2.1)

theorem stage_intervals_disjoint_of_tendsto {κ : Type*} {Q : Set κ}
    {ls rs : ℕ → κ → ℝ} {l r : κ → ℝ}
    (hl : ∀ k ∈ Q, Tendsto (fun n => ls n k) atTop (𝓝 (l k)))
    (hr : ∀ k ∈ Q, Tendsto (fun n => rs n k) atTop (𝓝 (r k)))
    (hd : ∀ᶠ n in atTop, Q.PairwiseDisjoint (fun k => Ico (ls n k) (rs n k))) :
    Q.PairwiseDisjoint (fun k => Ico (l k) (r k)) := by
  intro k hk j hj hkj
  apply Set.Ico_disjoint_Ico.mpr
  apply le_of_tendsto_of_tendsto ((hr k hk).min (hr j hj)) ((hl k hk).max (hl j hj))
  filter_upwards [hd] with n hn
  exact Set.Ico_disjoint_Ico.mp (hn hk hj hkj)

theorem finite_stage_omission_tendsto {κ : Type*} (Q : Finset κ)
    {ls rs : ℕ → κ → ℝ} {Hs : ℕ → ℝ} {l r : κ → ℝ} {H : ℝ}
    (hl : ∀ k ∈ Q, Tendsto (fun n => ls n k) atTop (𝓝 (l k)))
    (hr : ∀ k ∈ Q, Tendsto (fun n => rs n k) atTop (𝓝 (r k)))
    (hH : Tendsto Hs atTop (𝓝 H))
    (hb : ∀ᶠ n in atTop, 0 ≤ Hs n ∧ ∀ k ∈ Q,
      0 ≤ ls n k ∧ ls n k ≤ rs n k ∧ rs n k ≤ Hs n)
    (hd : ∀ᶠ n in atTop,
      (Q : Set κ).PairwiseDisjoint (fun k => Ico (ls n k) (rs n k))) :
    Tendsto (fun n => volume.real (Ico 0 (Hs n) \ stageRegion (ls n) (rs n) (Q : Set κ)))
      atTop (𝓝 (volume.real (Ico 0 H \ stageRegion l r (Q : Set κ)))) := by
  have hH0 : 0 ≤ H := ge_of_tendsto hH (hb.mono (fun _ hn => hn.1))
  have hbl : ∀ k ∈ Q, 0 ≤ l k ∧ l k ≤ r k ∧ r k ≤ H := by
    intro k hk
    exact ⟨ge_of_tendsto (hl k hk) (hb.mono (fun _ hn => (hn.2 k hk).1)),
      le_of_tendsto_of_tendsto (hl k hk) (hr k hk) (hb.mono (fun _ hn => (hn.2 k hk).2.1)),
      le_of_tendsto_of_tendsto (hr k hk) hH (hb.mono (fun _ hn => (hn.2 k hk).2.2))⟩
  rw [finite_stageRegion_omission Q hH0 hbl (stage_intervals_disjoint_of_tendsto hl hr hd)]
  apply (hH.sub (tendsto_finsetSum Q (fun k hk => (hr k hk).sub (hl k hk)))).congr'
  filter_upwards [hb,hd] with n hn hdn
  exact (finite_stageRegion_omission Q hn.1 hn.2 hdn).symm

end TransposeFollowup.RegularMotion

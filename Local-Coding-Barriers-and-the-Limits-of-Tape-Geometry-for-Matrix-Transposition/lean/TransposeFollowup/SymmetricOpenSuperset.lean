import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Algebra.Group.Basic

/-! Outer regularity gives a symmetric open superset within a prescribed
bounded open neighborhood. The compact closure and factor-two volume
bound are proved together. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [MeasurableSpace H]

theorem exists_symmetric_open_superset_add (σ : Measure H) [Measure.OuterRegular σ]
    {A W K : Set H} (hAs : ∀ x, x⁻¹ ∈ A ↔ x ∈ A) (hAW : A ⊆ W)
    (hW : IsOpen W) (hWK : W ⊆ K) (hK : IsCompact K)
    (hA0 : 0 < σ A) (hAt : σ A < ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ O : Set H, A ⊆ O ∧ O ⊆ W ∧ O.Nonempty ∧ IsOpen O ∧
      (∀ x, x⁻¹ ∈ O ↔ x ∈ O) ∧ IsCompact (closure O) ∧ closure O ⊆ K ∧
      σ A ≤ σ O ∧ σ O ≤ σ A + ε := by
  obtain ⟨V, hAV, hV, hVm⟩ := A.exists_isOpen_lt_add hAt.ne hε.ne'
  let O := (V ∩ W) ∩ Inv.inv ⁻¹' (V ∩ W)
  have hAO : A ⊆ O := by
    intro x hx
    exact ⟨⟨hAV hx, hAW hx⟩, hAV ((hAs x).mpr hx), hAW ((hAs x).mpr hx)⟩
  have hOW : O ⊆ W := fun _ hx => hx.1.2
  have hOo : IsOpen O := (hV.inter hW).inter ((hV.inter hW).preimage continuous_inv)
  have hOc : closure O ⊆ K := closure_minimal (hOW.trans hWK) hK.isClosed
  have hOm : σ A ≤ σ O := measure_mono hAO
  have hOn : O.Nonempty := by
    by_contra hn
    have hz : O = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hp := hA0.trans_le hOm
    simp only [hz, measure_empty, lt_self_iff_false] at hp
  refine ⟨O, hAO, hOW, hOn, hOo, ?_, hK.of_isClosed_subset isClosed_closure hOc, hOc, hOm, ?_⟩
  · intro x
    change ((x⁻¹ ∈ V ∩ W) ∧ (x⁻¹)⁻¹ ∈ V ∩ W) ↔ (x ∈ V ∩ W ∧ x⁻¹ ∈ V ∩ W)
    simp only [inv_inv, and_comm]
  · calc
      σ O ≤ σ V := measure_mono (fun _ hx => hx.1.1)
      _ ≤ σ A + ε := hVm.le

theorem exists_symmetric_open_superset (σ : Measure H) [Measure.OuterRegular σ]
    {A W K : Set H} (hAs : ∀ x, x⁻¹ ∈ A ↔ x ∈ A) (hAW : A ⊆ W)
    (hW : IsOpen W) (hWK : W ⊆ K) (hK : IsCompact K)
    (hA0 : 0 < σ A) (hAt : σ A < ⊤) :
    ∃ O : Set H, A ⊆ O ∧ O ⊆ W ∧ O.Nonempty ∧ IsOpen O ∧
      (∀ x, x⁻¹ ∈ O ↔ x ∈ O) ∧ IsCompact (closure O) ∧ closure O ⊆ K ∧
      σ A ≤ σ O ∧ σ O ≤ 2 * σ A := by
  simpa only [two_mul] using
    exists_symmetric_open_superset_add σ hAs hAW hW hWK hK hA0 hAt hA0

end TransposeFollowup

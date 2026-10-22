import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Basic.Real.ENatENNReal

/-! Finite attainment of Mathlib's external covering number, using
its existing definition and the well-ordering of ENat. -/
namespace Metric
open Classical Set
open scoped ENNReal NNReal
set_option autoImplicit false

theorem exists_finset_card_eq_externalCoveringNumber {X : Type*} [PseudoEMetricSpace X]
    {η : ℝ≥0} {A : Set X} (h : externalCoveringNumber η A ≠ ⊤) :
    ∃ F : Finset X, IsCover η A (F : Set X) ∧ (F.card : ℕ∞) = externalCoveringNumber η A := by
  let : Nonempty {C : Set X // IsCover η A C} := ⟨⟨A, IsCover.refl η A⟩⟩
  obtain ⟨C, hC⟩ := ENat.exists_eq_iInf (fun C : {C : Set X // IsCover η A C} => C.val.encard)
  have he : C.val.encard = externalCoveringNumber η A := by
    simpa only [iInf_subtype, externalCoveringNumber] using hC
  have hf : C.val.Finite := Set.encard_ne_top_iff.mp (he ▸ h)
  refine ⟨hf.toFinset, ?_, ?_⟩
  · simpa only [hf.coe_toFinset] using C.property
  · rw [← hf.encard_eq_coe_toFinset_card]
    exact he

end Metric

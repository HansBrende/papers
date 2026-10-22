import TransposeFollowup.HaarSandwichBounds
import Mathlib.Order.Preorder.Finite
import Mathlib.MeasureTheory.Group.Pointwise
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-! Continuous Ruzsa covering by a maximal finite packing. Finiteness
comes from a volume/cardinality bound, not from compactness alone. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

theorem haar_translate_packing_card (σ : Measure G) [Measure.IsMulLeftInvariant σ]
    {B T : Set G} (hT : MeasurableSet T) (F : Finset G) (hFB : (F : Set G) ⊆ B)
    (hd : (F : Set G).PairwiseDisjoint (fun x => x • T)) :
    (F.card : ℝ≥0∞) * σ T ≤ σ (B * T) := by
  calc
    _ = ∑ x ∈ F, σ (x • T) := by simp only [measure_smul, Finset.sum_const, nsmul_eq_mul]
    _ = σ (⋃ x ∈ F, x • T) := (measure_biUnion_finset hd (fun x _ => hT.const_smul x)).symm
    _ ≤ σ (B * T) := by
      apply measure_mono
      intro y hy
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hy
      obtain ⟨hxF, hy⟩ := Set.mem_iUnion.mp hx
      obtain ⟨t, ht, rfl⟩ := Set.mem_smul_set.mp hy
      exact Set.mul_mem_mul (hFB hxF) ht

theorem exists_finite_haar_translate_cover (σ : Measure G) [Measure.IsMulLeftInvariant σ]
    {B T : Set G} (hT : MeasurableSet T) (hT0 : 0 < σ T) (hTt : σ T < ⊤)
    {R : ℝ≥0∞} (hRt : R ≠ ⊤) (hBT : σ (B * T) ≤ R * σ T) :
    ∃ F : Finset G, (F : Set G) ⊆ B ∧ (F.card : ℝ≥0∞) ≤ R ∧
      B ⊆ (F : Set G) * T * T⁻¹ := by
  let P : Set (Finset G) := {F | (F : Set G) ⊆ B ∧
    (F : Set G).PairwiseDisjoint (fun x => x • T)}
  have hbound : ∀ F ∈ P, (F.card : ℝ≥0∞) ≤ R := by
    intro F hF
    apply (ENNReal.mul_le_mul_iff_left hT0.ne' hTt.ne).mp
    exact (haar_translate_packing_card σ hT F hF.1 hF.2).trans hBT
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hRt
  have hfinite : (Finset.card '' P).Finite := (Set.finite_Iio N).subset (by
    rintro n ⟨F, hF, rfl⟩
    have hh : (F.card : ℝ≥0∞) < N := (hbound F hF).trans_lt hN
    exact_mod_cast hh)
  have hPn : P.Nonempty := ⟨∅, by simp [P]⟩
  obtain ⟨F, hF, hmax⟩ := Set.Finite.exists_maximalFor' Finset.card P hfinite hPn
  refine ⟨F, hF.1, hbound F hF, ?_⟩
  intro b hb
  by_contra hn
  have hdis : ∀ x ∈ F, Disjoint (b • T) (x • T) := by
    intro x hx
    apply Set.disjoint_left.mpr
    intro y hyb hyx
    obtain ⟨t, ht, rfl⟩ := Set.mem_smul_set.mp hyb
    obtain ⟨u, hu, heq⟩ := Set.mem_smul_set.mp hyx
    change x * u = b * t at heq
    have hm : x * u * t⁻¹ ∈ (F : Set G) * T * T⁻¹ :=
      Set.mul_mem_mul (Set.mul_mem_mul hx hu) (by simpa only [Set.mem_inv, inv_inv] using ht)
    rw [heq, mul_inv_cancel_right] at hm
    exact hn hm
  have hbF : b ∉ F := by
    intro hbF
    have hTn : T.Nonempty := nonempty_of_measure_ne_zero hT0.ne'
    obtain ⟨t, ht⟩ := hTn
    exact Set.disjoint_left.mp (hdis b hbF) (Set.smul_mem_smul_set ht) (Set.smul_mem_smul_set ht)
  have hins : insert b F ∈ P := by
    constructor
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hb
      · exact hF.1 hx
    · rw [Finset.coe_insert]
      exact Set.pairwiseDisjoint_insert_of_notMem hbF |>.mpr ⟨hF.2, hdis⟩
  have hh : (insert b F).card ≤ F.card := hmax hins (Finset.card_le_card (Finset.subset_insert _ _))
  rw [Finset.card_insert_of_notMem hbF] at hh
  omega

end TransposeFollowup

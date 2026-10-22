import TransposeFollowup.ExternalCoverAttainment

/-! A finite cover by pieces has a piece carrying at least the average
external covering complexity. All covering numbers use the same radius. -/
namespace TransposeFollowup
open Classical Set
open scoped ENNReal NNReal
set_option autoImplicit false

theorem exists_large_cover_piece {X I : Type*} [PseudoEMetricSpace X]
    (F : Finset I) (hF : F.Nonempty) (A : Set X) (S : I → Set X) {η : ℝ≥0}
    (hcover : ∀ x ∈ A, ∃ i ∈ F, x ∈ S i)
    (hfin : ∀ i ∈ F, Metric.externalCoveringNumber η (S i) ≠ ⊤) :
    ∃ i ∈ F, Metric.externalCoveringNumber η A ≠ ⊤ ∧
      (Metric.externalCoveringNumber η A : ℝ≥0∞).toReal ≤
        (F.card : ℝ) * (Metric.externalCoveringNumber η (S i) : ℝ≥0∞).toReal := by
  have hI : Nonempty F := by
    obtain ⟨i, hi⟩ := hF
    exact ⟨⟨i, hi⟩⟩
  let : Nonempty F := hI
  have hex (i : F) := Metric.exists_finset_card_eq_externalCoveringNumber (hfin i i.2)
  choose E hE hcard using hex
  obtain ⟨i, _hi, hmax⟩ := Finset.univ.exists_max_image (fun i : F => (E i).card) Finset.univ_nonempty
  let C := Finset.univ.biUnion E
  have hc : Metric.IsCover η A (C : Set X) := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := hcover x hx
    obtain ⟨c, hce, hdist⟩ := hE ⟨j, hj⟩ hxj
    exact ⟨c, Finset.mem_biUnion.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, hce⟩, hdist⟩
  have hCcard : C.card ≤ F.card * (E i).card := by
    calc
      _ ≤ ∑ j : F, (E j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j : F, (E i).card := Finset.sum_le_sum (fun j _ => hmax j (Finset.mem_univ _))
      _ = _ := by simp
  have hN : Metric.externalCoveringNumber η A ≤ (C.card : ℕ∞) := by
    simpa only [Set.encard_coe_eq_coe_finsetCard] using hc.externalCoveringNumber_le_encard
  have hNt : Metric.externalCoveringNumber η A ≠ ⊤ := ne_top_of_le_ne_top (by simp) hN
  have hNr : (Metric.externalCoveringNumber η A : ℝ≥0∞).toReal ≤ (C.card : ℝ) := by
    simpa only [ENNReal.toReal_natCast] using ENNReal.toReal_mono
      (by finiteness : (C.card : ℝ≥0∞) ≠ ⊤) (ENat.toENNReal_mono hN)
  have hEq : ((E i).card : ℝ) = (Metric.externalCoveringNumber η (S i) : ℝ≥0∞).toReal := by
    have hh : ((E i).card : ℝ≥0∞) = (Metric.externalCoveringNumber η (S i) : ℝ≥0∞) := by
      exact_mod_cast hcard i
    simpa only [ENNReal.toReal_natCast] using congrArg ENNReal.toReal hh
  refine ⟨i, i.2, hNt, hNr.trans ?_⟩
  rw [← hEq]
  exact_mod_cast hCcard

end TransposeFollowup

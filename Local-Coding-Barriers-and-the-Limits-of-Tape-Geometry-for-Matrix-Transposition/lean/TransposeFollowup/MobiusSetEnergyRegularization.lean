import TransposeFollowup.DensityEnergyCongruence
import TransposeFollowup.SymmetricOpenSuperset
import TransposeFollowup.MobiusOpenEntryBox
import TransposeFollowup.MobiusUnimodular

/-! Replace an essentially bounded symmetric set by an open precompact
set, preserving its energy from below and controlling volume and location. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_symmetric_open_energy_superset_add {A : Set Group} {R : ℝ}
    (hAs : ∀ x, x⁻¹ ∈ A ↔ x ∈ A)
    (hae : (A ∩ matrixEntryBox R) =ᵐ[(Measure.haar : Measure Group)] A)
    (hA0 : 0 < (Measure.haar : Measure Group) A)
    (hAt : (Measure.haar : Measure Group) A < ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ O : Set Group, A ∩ matrixEntryBox R ⊆ O ∧ O.Nonempty ∧ IsOpen O ∧
      (∀ x, x⁻¹ ∈ O ↔ x ∈ O) ∧ IsCompact (closure O) ∧
      closure O ⊆ matrixEntryBox (R + 1) ∧
      (Measure.haar : Measure Group) A ≤ (Measure.haar : Measure Group) O ∧
      (Measure.haar : Measure Group) O ≤ (Measure.haar : Measure Group) A + ε ∧
      haarMultiplicativeEnergy Measure.haar A A ≤ haarMultiplicativeEnergy Measure.haar O O := by
  have hm := measure_congr hae
  have hs : ∀ x, x⁻¹ ∈ A ∩ matrixEntryBox R ↔ x ∈ A ∩ matrixEntryBox R := by
    intro x
    simp only [Set.mem_inter_iff, hAs x, matrixEntryBox_inv_iff R x]
  obtain ⟨O, hAO, _, hOn, hOo, hOs, hOc, hOb, hOl, hOu⟩ :=
    exists_symmetric_open_superset_add (Measure.haar : Measure Group) hs
      (fun _ hx => matrixEntryBox_subset_open_add_one R hx.2)
      (matrixOpenEntryBox_isOpen (R + 1)) (matrixOpenEntryBox_subset (R + 1))
      (matrixEntryBox_isCompact (R + 1)) (by rwa [hm]) (by rwa [hm]) hε
  refine ⟨O, hAO, hOn, hOo, hOs, hOc, hOb, ?_, ?_, ?_⟩
  · rwa [hm] at hOl
  · rwa [hm] at hOu
  · rw [← haarMultiplicativeEnergy_congr_ae Measure.haar hae hae]
    exact haarMultiplicativeEnergy_mono Measure.haar hAO hAO

theorem exists_symmetric_open_energy_superset {A : Set Group} {R : ℝ}
    (hAs : ∀ x, x⁻¹ ∈ A ↔ x ∈ A)
    (hae : (A ∩ matrixEntryBox R) =ᵐ[(Measure.haar : Measure Group)] A)
    (hA0 : 0 < (Measure.haar : Measure Group) A)
    (hAt : (Measure.haar : Measure Group) A < ⊤) :
    ∃ O : Set Group, A ∩ matrixEntryBox R ⊆ O ∧ O.Nonempty ∧ IsOpen O ∧
      (∀ x, x⁻¹ ∈ O ↔ x ∈ O) ∧ IsCompact (closure O) ∧
      closure O ⊆ matrixEntryBox (R + 1) ∧
      (Measure.haar : Measure Group) A ≤ (Measure.haar : Measure Group) O ∧
      (Measure.haar : Measure Group) O ≤ 2 * (Measure.haar : Measure Group) A ∧
      haarMultiplicativeEnergy Measure.haar A A ≤ haarMultiplicativeEnergy Measure.haar O O := by
  simpa only [two_mul] using exists_symmetric_open_energy_superset_add hAs hae hA0 hAt hA0

end TransposeFollowup.RealMobius

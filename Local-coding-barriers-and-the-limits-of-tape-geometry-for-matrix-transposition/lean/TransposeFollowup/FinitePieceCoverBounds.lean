import TransposeFollowup.ExternalCoverAttainment

/-! Finite subadditivity of native external covering numbers and the
opposite inequality for pieces separated by more than twice the radius.
The proofs assign actual centers of finite external covers. -/
namespace TransposeFollowup
open Classical Set
open scoped ENNReal NNReal
set_option autoImplicit false

theorem coveringNumber_le_sum_of_cover {X I : Type*} [PseudoEMetricSpace X]
    (F : Finset I) (A : Set X) (S : I → Set X) {η : ℝ≥0}
    (hcover : ∀ x ∈ A, ∃ i ∈ F, x ∈ S i)
    (hfin : ∀ i ∈ F, Metric.externalCoveringNumber η (S i) ≠ ⊤) :
    Metric.externalCoveringNumber η A ≠ ⊤ ∧
      (Metric.externalCoveringNumber η A : ℝ≥0∞).toReal ≤
        ∑ i ∈ F, (Metric.externalCoveringNumber η (S i) : ℝ≥0∞).toReal := by
  have hex (i : F) := Metric.exists_finset_card_eq_externalCoveringNumber (hfin i i.2)
  choose E hE hcard using hex
  let C := Finset.univ.biUnion E
  have hc : Metric.IsCover η A (C : Set X) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hcover x hx
    obtain ⟨c, hce, hd⟩ := hE ⟨i, hi⟩ hxi
    exact ⟨c, Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, hce⟩, hd⟩
  have hN : Metric.externalCoveringNumber η A ≤ (C.card : ℕ∞) := by
    simpa only [Set.encard_coe_eq_coe_finsetCard] using hc.externalCoveringNumber_le_encard
  have hNr : (Metric.externalCoveringNumber η A : ℝ≥0∞).toReal ≤ (C.card : ℝ) := by
    simpa only [ENNReal.toReal_natCast] using ENNReal.toReal_mono
      (by finiteness : (C.card : ℝ≥0∞) ≠ ⊤) (ENat.toENNReal_mono hN)
  have hEq (i : F) : ((E i).card : ℝ) =
      (Metric.externalCoveringNumber η (S i) : ℝ≥0∞).toReal := by
    have hh : ((E i).card : ℝ≥0∞) = (Metric.externalCoveringNumber η (S i) : ℝ≥0∞) := by
      exact_mod_cast hcard i
    simpa only [ENNReal.toReal_natCast] using congrArg ENNReal.toReal hh
  refine ⟨ne_top_of_le_ne_top (by simp) hN, hNr.trans ?_⟩
  calc
    _ ≤ ∑ i : F, ((E i).card : ℝ) := by exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := E))
    _ = ∑ i : F, (Metric.externalCoveringNumber η (S i) : ℝ≥0∞).toReal :=
      Finset.sum_congr rfl (fun i _ => hEq i)
    _ = _ := Finset.sum_coe_sort F (fun i => (Metric.externalCoveringNumber η (S i) : ℝ≥0∞).toReal)

theorem sum_coveringNumber_le_of_separated {X I : Type*} [PseudoMetricSpace X]
    (F : Finset I) (S : I → Set X) {C : Set X} {η : ℝ≥0}
    (hfin : Metric.externalCoveringNumber η C ≠ ⊤)
    (hsub : ∀ i ∈ F, S i ⊆ C)
    (hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j,
      2 * (η : ℝ) < dist x y) :
    (∀ i ∈ F, Metric.externalCoveringNumber η (S i) ≠ ⊤) ∧
      (∑ i ∈ F, (Metric.externalCoveringNumber η (S i) : ℝ≥0∞).toReal) ≤
        (Metric.externalCoveringNumber η C : ℝ≥0∞).toReal := by
  obtain ⟨E, hE, hcard⟩ := Metric.exists_finset_card_eq_externalCoveringNumber hfin
  let bucket (i : I) := E.filter (fun c => ∃ x ∈ S i, dist x c ≤ (η : ℝ))
  have hdis : (F : Set I).PairwiseDisjoint bucket := by
    intro i hi j hj hne
    apply Finset.disjoint_left.mpr
    intro c hci hcj
    obtain ⟨_, x, hx, hxc⟩ := Finset.mem_filter.mp hci
    obtain ⟨_, y, hy, hyc⟩ := Finset.mem_filter.mp hcj
    have hh := dist_triangle x c y
    rw [dist_comm c y] at hh
    have hxy := hsep i hi j hj hne x hx y hy
    linarith
  have hsum : ∑ i ∈ F, (bucket i).card ≤ E.card := by
    rw [← Finset.card_biUnion hdis]
    apply Finset.card_le_card
    intro c hc
    obtain ⟨i, _hi, hci⟩ := Finset.mem_biUnion.mp hc
    exact (Finset.mem_filter.mp hci).1
  have hN (i : I) (hi : i ∈ F) : Metric.externalCoveringNumber η (S i) ≤ ((bucket i).card : ℕ∞) := by
    have hc : Metric.IsCover η (S i) (bucket i : Set X) := by
      intro x hx
      obtain ⟨c, hce, hd⟩ := hE (hsub i hi hx)
      have hdist : dist x c ≤ (η : ℝ) := by exact_mod_cast edist_le_coe.mp hd
      exact ⟨c, Finset.mem_filter.mpr ⟨hce, x, hx, hdist⟩, hd⟩
    simpa only [Set.encard_coe_eq_coe_finsetCard] using hc.externalCoveringNumber_le_encard
  have hNr (i : I) (hi : i ∈ F) :
      (Metric.externalCoveringNumber η (S i) : ℝ≥0∞).toReal ≤ ((bucket i).card : ℝ) := by
    simpa only [ENNReal.toReal_natCast] using ENNReal.toReal_mono
      (by finiteness : ((bucket i).card : ℝ≥0∞) ≠ ⊤) (ENat.toENNReal_mono (hN i hi))
  have hEq : (E.card : ℝ) = (Metric.externalCoveringNumber η C : ℝ≥0∞).toReal := by
    have hh : (E.card : ℝ≥0∞) = (Metric.externalCoveringNumber η C : ℝ≥0∞) := by exact_mod_cast hcard
    simpa only [ENNReal.toReal_natCast] using congrArg ENNReal.toReal hh
  refine ⟨fun i hi => ne_top_of_le_ne_top (by simp) (hN i hi), ?_⟩
  calc
    _ ≤ ∑ i ∈ F, ((bucket i).card : ℝ) := Finset.sum_le_sum hNr
    _ ≤ (E.card : ℝ) := by exact_mod_cast hsum
    _ = _ := hEq

theorem coveringNumber_le_remainder_add_sum {X I : Type*} [PseudoEMetricSpace X]
    (F : Finset I) (A : Set X) (S : I → Set X) {η : ℝ≥0}
    (hAfin : Metric.externalCoveringNumber η A ≠ ⊤)
    (hfin : ∀ i ∈ F, Metric.externalCoveringNumber η (S i) ≠ ⊤) :
    let R := {x | x ∈ A ∧ ∀ i ∈ F, x ∉ S i}
    Metric.externalCoveringNumber η R ≠ ⊤ ∧
      (Metric.externalCoveringNumber η A : ℝ≥0∞).toReal ≤
        (Metric.externalCoveringNumber η R : ℝ≥0∞).toReal +
          ∑ i ∈ F, (Metric.externalCoveringNumber η (S i) : ℝ≥0∞).toReal := by
  let R := {x | x ∈ A ∧ ∀ i ∈ F, x ∉ S i}
  have hRfin : Metric.externalCoveringNumber η R ≠ ⊤ :=
    ne_top_of_le_ne_top hAfin (Metric.externalCoveringNumber_mono_set (fun _ hx => hx.1))
  let P : Option F → Set X := fun i => match i with
    | none => R
    | some j => S j
  have hcover : ∀ x ∈ A, ∃ i ∈ (Finset.univ : Finset (Option F)), x ∈ P i := by
    intro x hx
    by_cases hn : ∀ i ∈ F, x ∉ S i
    · exact ⟨none, Finset.mem_univ _, hx, hn⟩
    · push Not at hn
      obtain ⟨i, hi, hxi⟩ := hn
      exact ⟨some ⟨i, hi⟩, Finset.mem_univ _, hxi⟩
  have hPfin : ∀ i ∈ (Finset.univ : Finset (Option F)), Metric.externalCoveringNumber η (P i) ≠ ⊤ := by
    intro i _
    cases i with
    | none => exact hRfin
    | some i => exact hfin i i.2
  have hb := (coveringNumber_le_sum_of_cover Finset.univ A P hcover hPfin).2
  refine ⟨hRfin, ?_⟩
  rw [Fintype.sum_option] at hb
  change (Metric.externalCoveringNumber η A : ℝ≥0∞).toReal ≤
    (Metric.externalCoveringNumber η R : ℝ≥0∞).toReal +
      ∑ i : F, (Metric.externalCoveringNumber η (S i) : ℝ≥0∞).toReal at hb
  rw [Finset.sum_coe_sort F (fun i => (Metric.externalCoveringNumber η (S i) : ℝ≥0∞).toReal)] at hb
  exact hb

end TransposeFollowup

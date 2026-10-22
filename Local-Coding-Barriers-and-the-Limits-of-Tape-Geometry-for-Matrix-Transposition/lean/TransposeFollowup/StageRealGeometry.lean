import TransposeFollowup.UnitTickRegions

/-! Exact passage from native integer stage clocks to real interval geometry.
No measure-theoretic coverage or disjointness is postulated. -/
namespace TransposeFollowup.RegularMotion
open Classical Set MeasureTheory
set_option autoImplicit false

def stageRegion {κ : Type*} (l r : κ → ℝ) (Q : Set κ) : Set ℝ :=
  ⋃ k ∈ Q, Ico (l k) (r k)

theorem real_stage_iff_label {κ : Type*} {T : ℕ}
    (label : Fin T → κ) (A E : κ → ℕ)
    (hstage : ∀ k (t : Fin T), (A k ≤ t.val ∧ t.val < E k) ↔ label t=k)
    (k : κ) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) T) :
    x ∈ Ico (A k : ℝ) (E k) ↔ label ⟨⌊x⌋₊,(Nat.floor_lt hx.1).mpr hx.2⟩=k := by
  rw [← hstage]
  exact and_congr (Nat.le_floor_iff hx.1).symm (Nat.floor_lt hx.1).symm

theorem real_stage_subset_clock {κ : Type*} {T : ℕ} (A E : κ → ℕ)
    (hE : ∀ k, E k ≤ T) (k : κ) : Ico (A k : ℝ) (E k) ⊆ Ico (0 : ℝ) T := by
  intro x hx
  exact ⟨(Nat.cast_nonneg _).trans hx.1,hx.2.trans_le (by exact_mod_cast hE k)⟩

theorem real_stages_pairwise_disjoint {κ : Type*} {T : ℕ}
    (label : Fin T → κ) (A E : κ → ℕ) (hE : ∀ k, E k ≤ T)
    (hstage : ∀ k (t : Fin T), (A k ≤ t.val ∧ t.val < E k) ↔ label t=k) :
    Pairwise (fun k m => Disjoint (Ico (A k : ℝ) (E k)) (Ico (A m : ℝ) (E m))) := by
  intro k m hkm
  apply Set.disjoint_left.mpr
  intro x hxk hxm
  have hx := real_stage_subset_clock A E hE k hxk
  exact hkm (((real_stage_iff_label label A E hstage k hx).mp hxk).symm.trans
    ((real_stage_iff_label label A E hstage m hx).mp hxm))

theorem real_stages_scaled_pairwise_disjoint {κ : Type*} {T : ℕ} {P : ℝ} (hP : 0 < P)
    (label : Fin T → κ) (A E : κ → ℕ) (hE : ∀ k, E k ≤ T)
    (hstage : ∀ k (t : Fin T), (A k ≤ t.val ∧ t.val < E k) ↔ label t=k) :
    Pairwise (fun k m => Disjoint (Ico ((A k : ℝ)/P) ((E k : ℝ)/P))
      (Ico ((A m : ℝ)/P) ((E m : ℝ)/P))) := by
  intro k m hkm
  have hd := (real_stages_pairwise_disjoint label A E hE hstage hkm).preimage (fun x : ℝ => P*x)
  convert hd using 1 <;> ext x <;>
    simp only [Set.mem_preimage,Set.mem_Ico,div_le_iff₀ hP,lt_div_iff₀ hP,mul_comm x P]

theorem stageRegion_eq_tickCells {κ : Type*} {T : ℕ}
    (label : Fin T → κ) (A E : κ → ℕ) (hE : ∀ k, E k ≤ T)
    (hstage : ∀ k (t : Fin T), (A k ≤ t.val ∧ t.val < E k) ↔ label t=k) (Q : Set κ) :
    stageRegion (fun k => (A k : ℝ)) (fun k => (E k : ℝ)) Q=
      tickCells (Finset.univ.filter (fun t => label t ∈ Q)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hk,hxk⟩ := Set.mem_iUnion.mp hk
    have hxT := real_stage_subset_clock A E hE k hxk
    apply (mem_tickCells_iff _ hxT).mpr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [(real_stage_iff_label label A E hstage k hxT).mp hxk]
    exact hk
  · intro hx
    have hxT := tickCells_subset_clock _ hx
    have ht := (Finset.mem_filter.mp ((mem_tickCells_iff _ hxT).mp hx)).2
    refine Set.mem_iUnion.mpr ⟨label ⟨⌊x⌋₊,(Nat.floor_lt hxT.1).mpr hxT.2⟩,
      Set.mem_iUnion.mpr ⟨ht,?_⟩⟩
    exact (real_stage_iff_label label A E hstage _ hxT).mpr rfl

theorem stageRegion_measurable {κ : Type*} {T : ℕ}
    (label : Fin T → κ) (A E : κ → ℕ) (hE : ∀ k, E k ≤ T)
    (hstage : ∀ k (t : Fin T), (A k ≤ t.val ∧ t.val < E k) ↔ label t=k) (Q : Set κ) :
    MeasurableSet (stageRegion (fun k => (A k : ℝ)) (fun k => (E k : ℝ)) Q) := by
  rw [stageRegion_eq_tickCells label A E hE hstage Q]
  exact tickCells_measurable _

theorem stageRegion_volume_real {κ : Type*} {T : ℕ}
    (label : Fin T → κ) (A E : κ → ℕ) (hE : ∀ k, E k ≤ T)
    (hstage : ∀ k (t : Fin T), (A k ≤ t.val ∧ t.val < E k) ↔ label t=k) (Q : Set κ) :
    volume.real (stageRegion (fun k => (A k : ℝ)) (fun k => (E k : ℝ)) Q)=
      ((Finset.univ.filter (fun t : Fin T => label t ∈ Q)).card : ℝ) := by
  rw [stageRegion_eq_tickCells label A E hE hstage Q,tickCells_volume_real]

theorem stageRegion_omission_volume {κ : Type*} {T : ℕ}
    (label : Fin T → κ) (A E : κ → ℕ) (hE : ∀ k, E k ≤ T)
    (hstage : ∀ k (t : Fin T), (A k ≤ t.val ∧ t.val < E k) ↔ label t=k) (Q : Set κ) :
    volume.real (Ico (0 : ℝ) T \ stageRegion (fun k => (A k : ℝ)) (fun k => (E k : ℝ)) Q)=
      ((Finset.univ.filter (fun t : Fin T => label t ∉ Q)).card : ℝ) := by
  rw [stageRegion_eq_tickCells label A E hE hstage Q,tickCells_compl,tickCells_volume_real]
  have heq : (Finset.univ.filter (fun t : Fin T => label t ∈ Q))ᶜ=
      Finset.univ.filter (fun t : Fin T => label t ∉ Q) := by ext t; simp
  rw [heq]

theorem stageRegion_scale {κ : Type*} (l r : κ → ℝ) (Q : Set κ) {P : ℝ} (hP : 0 < P) :
    (fun x : ℝ => P*x) ⁻¹' stageRegion l r Q=
      stageRegion (fun k => l k/P) (fun k => r k/P) Q := by
  ext x
  simp only [stageRegion,Set.mem_preimage,Set.mem_iUnion,Set.mem_Ico,div_le_iff₀ hP,
    lt_div_iff₀ hP,mul_comm x P]

theorem volume_real_preimage_pos_mul {P : ℝ} (hP : 0 < P) (S : Set ℝ) :
    volume.real ((fun x : ℝ => P*x) ⁻¹' S)=volume.real S/P := by
  simp only [measureReal_def,Real.volume_preimage_mul_left hP.ne',ENNReal.toReal_mul,
    abs_of_pos (inv_pos.mpr hP),ENNReal.toReal_ofReal (inv_nonneg.mpr hP.le)]
  ring

theorem stageRegion_scaled_omission_volume {κ : Type*} {T : ℕ}
    (label : Fin T → κ) (A E : κ → ℕ) (hE : ∀ k, E k ≤ T)
    (hstage : ∀ k (t : Fin T), (A k ≤ t.val ∧ t.val < E k) ↔ label t=k)
    (Q : Set κ) {P : ℝ} (hP : 0 < P) :
    volume.real (Ico (0 : ℝ) ((T : ℝ)/P) \
      stageRegion (fun k => (A k : ℝ)/P) (fun k => (E k : ℝ)/P) Q)=
      ((Finset.univ.filter (fun t : Fin T => label t ∉ Q)).card : ℝ)/P := by
  rw [← stageRegion_scale _ _ Q hP]
  have heq : Ico (0 : ℝ) ((T : ℝ)/P) \
      (fun x : ℝ => P*x) ⁻¹' stageRegion (fun k => (A k : ℝ)) (fun k => (E k : ℝ)) Q=
      (fun x : ℝ => P*x) ⁻¹' (Ico (0 : ℝ) T \
        stageRegion (fun k => (A k : ℝ)) (fun k => (E k : ℝ)) Q) := by
    ext x
    simp only [Set.mem_sdiff,Set.mem_preimage,Set.mem_Ico,lt_div_iff₀ hP,
      mul_nonneg_iff_of_pos_left hP,mul_comm x P]
  rw [heq,volume_real_preimage_pos_mul hP,stageRegion_omission_volume label A E hE hstage Q]

end TransposeFollowup.RegularMotion

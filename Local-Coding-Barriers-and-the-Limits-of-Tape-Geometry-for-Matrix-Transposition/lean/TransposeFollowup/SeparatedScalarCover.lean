import TransposeFollowup.ExternalCoverAttainment
import TransposeFollowup.BoundedCoordinatePacking

/-! One-dimensional cover refinement and finite separated scalar sets
whose cardinality controls the native covering number. -/
namespace TransposeFollowup
open Classical Set BoundedCoordinatePacking
open scoped ENNReal NNReal
set_option autoImplicit false

theorem scalar_coveringNumber_le_patches {S : Set ℝ} (F : Finset ℝ) {N : ℝ} {η : ℝ≥0}
    (hN : 0 ≤ N) (hη : 0 < η) (hcover : ∀ x ∈ S, ∃ c ∈ F, |x - c| ≤ N) :
    Metric.externalCoveringNumber η S ≠ ⊤ ∧
      (Metric.externalCoveringNumber η S : ℝ≥0∞).toReal ≤
        (2 * N / (η : ℝ) + 1) * (F.card : ℝ) := by
  have hηR : (0 : ℝ) < η := hη
  let K := binCount N η
  let E := F.biUnion (fun c => (Finset.range K).image (fun k : ℕ => c - N + (k : ℝ) * (η : ℝ)))
  have hcard : E.card ≤ F.card * K := by
    calc
      _ ≤ ∑ c ∈ F, ((Finset.range K).image (fun k : ℕ => c - N + (k : ℝ) * (η : ℝ))).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _c ∈ F, K := Finset.sum_le_sum (fun _ _ =>
        (Finset.card_image_le).trans_eq (Finset.card_range K))
      _ = _ := by simp
  have hc : Metric.IsCover η S (E : Set ℝ) := by
    intro x hx
    obtain ⟨c, hcf, hxc⟩ := hcover x hx
    let k := bin N η (x - c)
    have hk : k < K := bin_lt hηR hxc
    have hq : 0 ≤ (x - c + N) / (η : ℝ) := div_nonneg (by linarith [(abs_le.mp hxc).1]) hηR.le
    have hl := Nat.floor_le hq
    have hu := Nat.lt_floor_add_one ((x - c + N) / (η : ℝ))
    change (k : ℝ) ≤ (x - c + N) / (η : ℝ) at hl
    change (x - c + N) / (η : ℝ) < (k : ℝ) + 1 at hu
    have hl' := (le_div_iff₀ hηR).mp hl
    have hu' := (div_lt_iff₀ hηR).mp hu
    have hd : dist x (c - N + (k : ℝ) * (η : ℝ)) ≤ (η : ℝ) := by
      rw [Real.dist_eq]
      apply (abs_lt.mpr ⟨by nlinarith, by nlinarith⟩).le
    refine ⟨c - N + (k : ℝ) * (η : ℝ), ?_, edist_le_coe.mpr ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨c, hcf, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩⟩
    · exact_mod_cast hd
  have hNc : Metric.externalCoveringNumber η S ≤ (E.card : ℕ∞) := by
    simpa only [Set.encard_coe_eq_coe_finsetCard] using hc.externalCoveringNumber_le_encard
  have hfinite : Metric.externalCoveringNumber η S ≠ ⊤ := ne_top_of_le_ne_top (by simp) hNc
  have hNr : (Metric.externalCoveringNumber η S : ℝ≥0∞).toReal ≤ (E.card : ℝ) := by
    simpa only [ENNReal.toReal_natCast] using ENNReal.toReal_mono
      (by finiteness : (E.card : ℝ≥0∞) ≠ ⊤) (ENat.toENNReal_mono hNc)
  refine ⟨hfinite, hNr.trans ?_⟩
  calc
    _ ≤ (F.card : ℝ) * (K : ℝ) := by exact_mod_cast hcard
    _ ≤ (F.card : ℝ) * (2 * N / (η : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (binCount_le hN hηR) (Nat.cast_nonneg _)
    _ = _ := mul_comm _ _

theorem exists_separated_scalar_cover {S : Set ℝ} {B : ℝ} {η : ℝ≥0}
    (hB : 0 ≤ B) (hη : 0 < η) (hS : S.Nonempty) (hbound : ∀ x ∈ S, |x| ≤ B) :
    ∃ T : Finset ℝ, T.Nonempty ∧ (T : Set ℝ) ⊆ S ∧
      (∀ s ∈ T, ∀ t ∈ T, s ≠ t → 4 * (η : ℝ) < |s - t|) ∧
      Metric.externalCoveringNumber η S ≠ ⊤ ∧
      (Metric.externalCoveringNumber η S : ℝ≥0∞).toReal ≤ 9 * (T.card : ℝ) := by
  have hfin2 : Metric.externalCoveringNumber (2 * η) S ≠ ⊤ :=
    (scalar_coveringNumber_le_patches ({0} : Finset ℝ) hB (by positivity : 0 < 2 * η)
      (fun x hx => ⟨0, by simp, by simpa only [sub_zero] using hbound x hx⟩)).1
  have hpack : Metric.packingNumber (4 * η) S ≠ ⊤ := by
    apply ne_top_of_le_ne_top hfin2
    simpa only [show (2 : ℝ≥0) * (2 * η) = 4 * η by ring] using
      Metric.packingNumber_two_mul_le_externalCoveringNumber (2 * η) S
  let Z := Metric.maximalSeparatedSet (4 * η) S
  have hZfinite : Z.Finite := by
    apply Set.encard_ne_top_iff.mp
    rw [Metric.encard_maximalSeparatedSet hpack]
    exact hpack
  have hcover : Metric.IsCover (4 * η) S Z := Metric.isCover_maximalSeparatedSet hpack
  have hZnonempty : Z.Nonempty := hcover.nonempty hS
  let T := hZfinite.toFinset
  have hpatch : ∀ x ∈ S, ∃ t ∈ T, |x - t| ≤ 4 * (η : ℝ) := by
    intro x hx
    obtain ⟨t, ht, hd⟩ := hcover hx
    have hh : dist x t ≤ ((4 * η : ℝ≥0) : ℝ) := by exact_mod_cast edist_le_coe.mp hd
    exact ⟨t, hZfinite.mem_toFinset.mpr ht, by simpa only [Real.dist_eq, NNReal.coe_mul, NNReal.coe_ofNat] using hh⟩
  obtain ⟨hfinite, hcard⟩ := scalar_coveringNumber_le_patches T (by positivity : 0 ≤ 4 * (η : ℝ)) hη hpatch
  have hcoef : 2 * (4 * (η : ℝ)) / (η : ℝ) + 1 = 9 := by
    have hηR : (0 : ℝ) < η := hη
    field_simp
    norm_num
  rw [hcoef] at hcard
  refine ⟨T, hZfinite.toFinset_nonempty.mpr hZnonempty, ?_, ?_, hfinite, hcard⟩
  · intro x hx
    exact Metric.maximalSeparatedSet_subset (hZfinite.mem_toFinset.mp hx)
  · intro s hs t ht hne
    have hh := Metric.isSeparated_maximalSeparatedSet (ε := 4 * η) (A := S)
      (hZfinite.mem_toFinset.mp hs) (hZfinite.mem_toFinset.mp ht) hne
    have hn : (4 * η : ℝ≥0) < nndist s t := ENNReal.coe_lt_coe.mp hh
    have hr : ((4 * η : ℝ≥0) : ℝ) < dist s t := by exact_mod_cast hn
    simpa only [Real.dist_eq, NNReal.coe_mul, NNReal.coe_ofNat] using hr

end TransposeFollowup

import TransposeFollowup.GeneratorConvolutionWalk
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce

/-! Finitely many actual endpoints carry each finite generator walk.
No freeness or bound on their entries is required. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped Pointwise
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem mconv_ae_finite_support (μ ν : Measure Group) [SFinite ν]
    (F E : Finset Group) (hF : ∀ᵐ a ∂μ, a ∈ F) (hE : ∀ᵐ b ∂ν, b ∈ E) :
    ∀ᵐ z ∂μ ∗ₘ ν, z ∈ F * E := by
  have hs : MeasurableSet (↑(F * E) : Set Group) := (F * E).finite_toSet.measurableSet
  rw [Measure.mconv]
  apply (ae_map_iff (p := fun z => z ∈ F * E) measurable_mul.aemeasurable hs).mpr
  apply (Measure.ae_prod_iff_ae_ae (hs.preimage measurable_mul)).mpr
  filter_upwards [hF] with a ha
  exact hE.mono (fun b hb => Finset.mul_mem_mul ha hb)

theorem generatorWalkMeasure_word_support {m : ℕ} (G : Fin m → Group)
    (hm : 0 < m) (n : ℕ) :
    ∃ F : Finset (FreeGroup (Fin m)), (∀ v ∈ F, FreeGroup.norm v ≤ n) ∧
      ∀ᵐ a ∂generatorWalkMeasure G n, a ∈ F.image (FreeGroup.lift G) := by
  let E : Finset (FreeGroup (Fin m)) :=
    Finset.univ.image FreeGroup.of ∪ Finset.univ.image (fun i => (FreeGroup.of i)⁻¹)
  have hEn : ∀ v ∈ E, FreeGroup.norm v ≤ 1 := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      simp only [FreeGroup.norm_of, le_refl]
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      simp only [FreeGroup.norm_inv_eq, FreeGroup.norm_of, le_refl]
  have hE : ∀ᵐ a ∂symmetricGeneratorMeasure G, a ∈ E.image (FreeGroup.lift G) := by
    unfold symmetricGeneratorMeasure
    apply Measure.ae_smul_measure
    rw [ae_finsetSum_measure_iff]
    intro i _
    rw [ae_add_measure_iff]
    constructor
    · apply (ae_dirac_iff (p := fun a : Group => a ∈ E.image (FreeGroup.lift G))
        (E.image (FreeGroup.lift G)).finite_toSet.measurableSet).mpr
      exact Finset.mem_image.mpr ⟨FreeGroup.of i,
        Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)), by simp⟩
    · apply (ae_dirac_iff (p := fun a : Group => a ∈ E.image (FreeGroup.lift G))
        (E.image (FreeGroup.lift G)).finite_toSet.measurableSet).mpr
      exact Finset.mem_image.mpr ⟨(FreeGroup.of i)⁻¹,
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)), by simp⟩
  induction n with
  | zero =>
    refine ⟨{1}, ?_, ?_⟩
    · intro v hv
      obtain rfl := Finset.mem_singleton.mp hv
      simp
    · change ∀ᵐ a ∂Measure.dirac (1 : Group), a ∈ ({1} : Finset (FreeGroup (Fin m))).image (FreeGroup.lift G)
      simp only [Finset.image_singleton, map_one, Finset.mem_singleton]
      exact (ae_dirac_iff (p := fun a : Group => a = 1) (measurableSet_singleton 1)).mpr rfl
  | succ n ih =>
    obtain ⟨F, hFn, hF⟩ := ih
    have : IsProbabilityMeasure (generatorWalkMeasure G n) := generatorWalkMeasure_probability G hm n
    refine ⟨E * F, ?_, ?_⟩
    · intro v hv
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_mul.mp hv
      exact (FreeGroup.norm_mul_le x y).trans (by have := hEn x hx; have := hFn y hy; omega)
    · have h := mconv_ae_finite_support _ _ _ _ hE hF
      filter_upwards [h] with a ha
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_mul.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨v * z, Finset.mul_mem_mul hv hz, map_mul _ _ _⟩

theorem generatorWalkMeasure_finite_support {m : ℕ} (G : Fin m → Group)
    (hm : 0 < m) (n : ℕ) :
    ∃ F : Finset Group, ∀ᵐ a ∂generatorWalkMeasure G n, a ∈ F := by
  obtain ⟨F, _, hF⟩ := generatorWalkMeasure_word_support G hm n
  exact ⟨F.image (FreeGroup.lift G), hF⟩

end TransposeFollowup.RealMobius

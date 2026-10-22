import TransposeFollowup.RationalCommonSmoothingSeparation
import TransposeFollowup.SmoothedWalkShortWords

/-! An actual mass lower bound for a translated smoothed rational free walk
produces a finite separated subset of the target set. One common smoothing
element is selected; there is no smoothing error or translation-size loss. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory Set RealMobius
open scoped ENNReal NNReal Pointwise Matrix.Norms.Frobenius
set_option autoImplicit false

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem exists_separated_subset_of_smoothed_walk_mass {m D : ℕ} (g : Fin m → Group)
    (hm : 0 < m) (hD : 0 < D) (hg : ∀ i, HasDenominator D (g i))
    (hfree : Function.Injective (FreeGroup.lift (realEmbedding ∘ g)))
    {k : ℝ} (hk : 1 ≤ k) (hcard : k ^ 2 ≤ 2 * m) (t : ℕ)
    {η : ℝ} (hη : 0 < η) (hηone : η ≤ 1)
    {A : Set RealMobius.Group} (hA : MeasurableSet A) (hAb : A ⊆ matrixEntryBox 2)
    (w : RealMobius.Group) {p : ℝ≥0∞} (hp : 0 < p) (hpt : p ≠ ⊤)
    (hmass : p ≤ (generatorWalkMeasure (realEmbedding ∘ g) t ∗ₘ mobiusHaarKernel η) (w • A)) :
    ∃ F : Finset RealMobius.Group, (F : Set RealMobius.Group) ⊆ A ∧
      Metric.IsSeparated (ENNReal.ofReal (1 / (128 * (D : ℝ) ^ (2 * t))))
        ((fun a : RealMobius.Group => (a : Matrix (Fin 2) (Fin 2) ℝ)) '' (F : Set RealMobius.Group)) ∧
      p ≤ 2 * (F.card : ℝ≥0∞) * ENNReal.ofReal ((2 / k) ^ t) := by
  obtain ⟨u, hu, F, _, hF, hmassF⟩ :=
    exists_short_words_of_smoothed_walk_mass g hm hg hfree hk hcard t hη hA w hp hpt hmass
  let f := fun v : FreeGroup (Fin m) => w⁻¹ * FreeGroup.lift (realEmbedding ∘ g) v * u
  have hfA : ∀ v ∈ F, f v ∈ A := fun v hv => (hF v hv).2.2
  have hinj : Function.Injective f := by
    intro a b he
    exact hfree (mul_left_cancel (mul_right_cancel he))
  refine ⟨F.image f, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact hfA a ha
  · rintro y ⟨y', hy', rfl⟩ z ⟨z', hz', rfl⟩ hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz'
    have hab : FreeGroup.lift (realEmbedding ∘ g) a ≠
        FreeGroup.lift (realEmbedding ∘ g) b := fun he => hne (by rw [hfree he])
    have hsep := common_smoothing_separated (pow_pos hD t) (hF a ha).2.1 (hF b hb).2.1 hab
      (mobiusIdentityBall_subset_entryBox_two hη hηone hu) (hAb (hfA a ha))
    have hdist : 1 / (128 * (D : ℝ) ^ (2 * t)) <
        dist ((f a : RealMobius.Group) : Matrix (Fin 2) (Fin 2) ℝ)
          ((f b : RealMobius.Group) : Matrix (Fin 2) (Fin 2) ℝ) := by
      have hd : 0 < (D : ℝ) ^ (2 * t) := by positivity
      have hs : 1 / (64 * (D : ℝ) ^ (2 * t)) ≤
          dist ((f a : RealMobius.Group) : Matrix (Fin 2) (Fin 2) ℝ)
            ((f b : RealMobius.Group) : Matrix (Fin 2) (Fin 2) ℝ) := by
        simpa only [f, Nat.cast_pow, ← pow_mul, mul_comm t 2] using hsep
      apply lt_of_lt_of_le _ hs
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith
    rw [edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans (by positivity) hdist)).mpr hdist
  · simpa only [Finset.card_image_of_injective F hinj] using hmassF

end TransposeFollowup.RationalFreePair

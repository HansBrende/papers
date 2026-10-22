import TransposeFollowup.DyadicBandOverlapEnergy
import TransposeFollowup.DyadicBandRegularityCost
import TransposeFollowup.DyadicMaskedCorrelation

/-! A fixed relative-cost threshold makes every finite discarded sum
small in L2. Mask differences identify exactly the discarded bands. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
set_option autoImplicit false

noncomputable def dyadicRegularityThreshold : ℝ :=
  3 * 1024 ^ 2 * (dyadicBandRegularityConstant + 1)

theorem dyadicRegularityThreshold_pos : 0 < dyadicRegularityThreshold := by
  unfold dyadicRegularityThreshold
  have h := dyadicBandRegularityConstant_nonneg
  positivity

theorem dyadicBadBand_sum_norm_le (s : Finset ℕ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (hnorm : ‖hf.toLp f‖ = 1) :
    let u := fun j => (smoothBand hf hs (dyadicAnnularCutoff j)
      (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume
    let bad := s.filter (fun j => ¬dyadicBandRegularityCost hf hs j ≤ dyadicRegularityThreshold * ‖u j‖ ^ 2)
    ‖∑ j ∈ bad, u j‖ ≤ 1 / 1024 := by
  classical
  let u := fun j => (smoothBand hf hs (dyadicAnnularCutoff j)
    (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume
  let bad := s.filter (fun j => ¬dyadicBandRegularityCost hf hs j ≤ dyadicRegularityThreshold * ‖u j‖ ^ 2)
  have hcost := dyadicBandRegularityCost_sum_le bad hf hs
  simp only [hnorm, one_pow, mul_one] at hcost
  have he : dyadicRegularityThreshold * (∑ j ∈ bad, ‖u j‖ ^ 2) ≤ dyadicBandRegularityConstant := by
    calc
      _ = ∑ j ∈ bad, dyadicRegularityThreshold * ‖u j‖ ^ 2 := Finset.mul_sum _ _ _
      _ ≤ ∑ j ∈ bad, dyadicBandRegularityCost hf hs j := by
        apply Finset.sum_le_sum
        intro j hj
        exact (lt_of_not_ge (Finset.mem_filter.mp hj).2).le
      _ ≤ _ := hcost
  have ho := dyadicBand_sum_norm_sq_le_three_energy bad hf hs
  change ‖∑ j ∈ bad, u j‖ ^ 2 ≤ 3 * ∑ j ∈ bad, ‖u j‖ ^ 2 at ho
  have hscaled := mul_le_mul_of_nonneg_left ho dyadicRegularityThreshold_pos.le
  have hsquare : ‖∑ j ∈ bad, u j‖ ^ 2 ≤ (1 / 1024 : ℝ) ^ 2 := by
    apply (mul_le_mul_iff_right₀ dyadicRegularityThreshold_pos).mp
    calc
      _ ≤ 3 * dyadicBandRegularityConstant := by nlinarith [he, hscaled]
      _ ≤ dyadicRegularityThreshold * (1 / 1024 : ℝ) ^ 2 := by
        unfold dyadicRegularityThreshold
        linarith
  change ‖∑ j ∈ bad, u j‖ ≤ _
  nlinarith [norm_nonneg (∑ j ∈ bad, u j)]

theorem dyadicMaskedBand_sum_sub_inter (s : Finset ℕ) (p q : ℕ → Prop)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    (∑ j ∈ s, dyadicMaskedBand p hf hs j) -
      (∑ j ∈ s, dyadicMaskedBand (fun j => p j ∧ q j) hf hs j) =
      ∑ j ∈ (s.filter p).filter (fun j => ¬q j),
        (smoothBand hf hs (dyadicAnnularCutoff j)
          (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume := by
  classical
  rw [← Finset.sum_sub_distrib, Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hp : p j <;> by_cases hq : q j <;> simp [dyadicMaskedBand, hp, hq]

theorem dyadicMaskedBand_regular_discard_norm_le (s : Finset ℕ) (p : ℕ → Prop)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (hnorm : ‖hf.toLp f‖ = 1) :
    ‖(∑ j ∈ s, dyadicMaskedBand p hf hs j) -
      (∑ j ∈ s, dyadicMaskedBand (fun j => p j ∧ dyadicBandRegularityCost hf hs j ≤
        dyadicRegularityThreshold * ‖(smoothBand hf hs (dyadicAnnularCutoff j)
          (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume‖ ^ 2) hf hs j)‖ ≤ 1 / 1024 := by
  rw [dyadicMaskedBand_sum_sub_inter]
  exact dyadicBadBand_sum_norm_le (s.filter p) hf hs hnorm

end TransposeFollowup

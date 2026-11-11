import AdaptiveTransfer.InformationAccounting
import TransposeFollowup.ConditionalEntropyFibers
import TransposeFollowup.UniformEntropy
import Mathlib.Tactic

/-! Metadata-dependent support charges under one finite law. Empty metadata
fibres and zero-mass fibres require no arbitrary nonempty certificate. -/

namespace AdaptiveTransfer

open TransposeFollowup Finset Classical
open scoped BigOperators

theorem conditional_entropy_le_mean_log_support {Ω H A : Type*}
    [Fintype Ω] [Fintype H] [Fintype A]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (metadata : Ω → H) (record : Ω → A)
    (menu : H → Finset A) (hmenu : ∀ x, record x ∈ menu (metadata x)) :
    conditionalObservationEntropy p record metadata ≤
      ∑ x, p x * Real.log ((menu (metadata x)).card : ℝ) := by
  rw [← sum_helperMass_mul_observationEntropy p hp metadata record]
  calc
    _ ≤ ∑ a, helperMass p metadata a * Real.log ((menu a).card : ℝ) := by
      apply sum_le_sum
      intro a _
      by_cases ha : helperMass p metadata a = 0
      · simp only [ha, zero_mul, le_refl]
      · have ham := helperMass_nonneg p hp metadata a
        let := helperFiber_nonempty_of_mass_pos p metadata a (lt_of_le_of_ne ham (Ne.symm ha))
        apply mul_le_mul_of_nonneg_left _ ham
        apply observationEntropy_le_log_support _
          (helperConditionalWeight_nonneg p hp metadata a)
          (sum_helperConditionalWeight p metadata a ha) (fun x : HelperFiber metadata a => record x)
          (menu a)
        intro x
        simpa only [← x.property] using hmenu x.val
    _ = _ := sum_pushforward_mul p metadata (fun a => Real.log ((menu a).card : ℝ))

theorem conditional_entropy_le_mean_bits {Ω H A : Type*}
    [Fintype Ω] [Fintype H] [Fintype A]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (metadata : Ω → H) (record : Ω → A)
    (menu : H → Finset A) (hmenu : ∀ x, record x ∈ menu (metadata x))
    (bits : H → ℕ) (hcard : ∀ a, (menu a).card ≤ 2 ^ bits a) :
    conditionalObservationEntropy p record metadata ≤
      (∑ x, p x * (bits (metadata x) : ℝ)) * Real.log 2 := by
  calc
    _ ≤ ∑ x, p x * Real.log ((menu (metadata x)).card : ℝ) :=
      conditional_entropy_le_mean_log_support p hp metadata record menu hmenu
    _ ≤ ∑ x, p x * ((bits (metadata x) : ℝ) * Real.log 2) := by
      apply sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hp x)
      have hc : (0 : ℝ) < (menu (metadata x)).card := by
        exact_mod_cast card_pos.mpr ⟨record x, hmenu x⟩
      have hh : ((menu (metadata x)).card : ℝ) ≤ (2 : ℝ) ^ bits (metadata x) := by
        exact_mod_cast hcard (metadata x)
      exact (Real.log_le_log hc hh).trans_eq (Real.log_pow _ _)
    _ = _ := by simp only [← mul_assoc, sum_mul]

/-- Joint imports pay the information left after actual attained support
menus, even when their bit lengths vary with metadata and exterior. -/
theorem joint_import_information_from_support {Ω Metadata Exterior Ordinary Import : Type*}
    [Fintype Ω] [Fintype Metadata] [Fintype Exterior] [Fintype Ordinary] [Fintype Import]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (metadata : Ω → Metadata) (exterior : Ω → Exterior)
    (ordinary : Ω → Ordinary) (imports : Ω → Import)
    (hinj : Function.Injective (fun x => (((metadata x, exterior x), ordinary x), imports x)))
    (exteriorMenu : Metadata → Finset Exterior)
    (ordinaryMenu : Metadata × Exterior → Finset Ordinary)
    (he : ∀ x, exterior x ∈ exteriorMenu (metadata x))
    (hr : ∀ x, ordinary x ∈ ordinaryMenu (metadata x, exterior x))
    (exteriorBits : Metadata → ℕ) (ordinaryBits : Metadata × Exterior → ℕ)
    (hecard : ∀ m, (exteriorMenu m).card ≤ 2 ^ exteriorBits m)
    (hrcard : ∀ m, (ordinaryMenu m).card ≤ 2 ^ ordinaryBits m) :
    entropy p - observationEntropy p metadata -
      (∑ x, p x * ((exteriorBits (metadata x) : ℝ) + ordinaryBits (metadata x, exterior x))) *
        Real.log 2 ≤
      conditionalObservationEntropy p imports (fun x => ((metadata x, exterior x), ordinary x)) := by
  have heh := conditional_entropy_le_mean_bits p hp metadata exterior exteriorMenu he exteriorBits hecard
  have hrh := conditional_entropy_le_mean_bits p hp (fun x => (metadata x, exterior x))
    ordinary ordinaryMenu hr ordinaryBits hrcard
  have hj := joint_record_information_lower p hp metadata exterior ordinary imports hinj _ _ heh hrh
  simp only [mul_add, sum_add_distrib, add_mul]
  linarith

end AdaptiveTransfer

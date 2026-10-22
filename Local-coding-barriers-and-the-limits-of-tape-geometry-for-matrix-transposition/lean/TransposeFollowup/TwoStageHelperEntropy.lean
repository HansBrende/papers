import TransposeFollowup.TwoStageHelper
import TransposeFollowup.EntropyFibers

/-! The two-stage toll charges actual input and helper entropy for arbitrary
probability distributions on a correct family. Uniform cardinality deficit is
an immediate specialization; the ambient helper type may be infinite. -/
set_option autoImplicit false

namespace TransposeFollowup.TwoStageHelper
open Classical
open scoped BigOperators
variable {n b : Nat} {H : Type*} (T : TwoStageHelper n b H)

noncomputable def attainedHelper (F : Finset (FiniteMatrix n b))
    (x : F) : F.image T.helper :=
  ⟨T.helper x.val, Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩

theorem helper_entropy_deficit_bound_of_distribution
    (F : Finset (FiniteMatrix n b)) (hc : T.CorrectOn F)
    (p : F → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (r : ℕ) (hr : r ≤ n) :
    (n * n * b : ℕ) - entropy p / Real.log 2 +
      observationEntropy p (T.attainedHelper F) / Real.log 2 ≥
        (b * r * (n-r) : ℕ) := by
  classical
  let c := (n-r)*n*b + r*r*b
  let f := T.attainedHelper F
  have hfiber (z : F.image T.helper) : fiberCard f z ≤ 2^c := by
    calc
      _ ≤ (F.filter (fun x => T.helper x = z.val)).card := by
        unfold fiberCard
        apply Finset.card_le_card_of_injOn Subtype.val
        · intro x hx
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          have he := congrArg Subtype.val hx
          exact Finset.mem_filter.mpr ⟨x.property, he⟩
        · intro x hx y hy hxy
          exact Subtype.ext hxy
      _ ≤ 2^c := by
        apply (T.branch z.val).correct_family_card _ _ r hr
        intro x hx
        obtain ⟨hx, he⟩ := Finset.mem_filter.mp hx
        simpa only [apply, he] using hc x hx
  have hent := entropy_le_observation_add_log_fiber_bound p hp f
    ((2 : ℝ)^c) (by positivity) (fun z => by exact_mod_cast hfiber z)
  rw [hp1, one_mul, Real.log_pow] at hent
  have hexpR : (c : ℝ) + (b*r*(n-r) : ℕ) = (n*n*b : ℕ) := by
    exact_mod_cast exponent_decomposition n b r hr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (mul_le_mul_iff_of_pos_right hlog2).mp
  field_simp
  dsimp only [f] at hent
  nlinarith

theorem helper_entropy_deficit_bound (F : Finset (FiniteMatrix n b)) [Nonempty F]
    (hc : T.CorrectOn F) (r : ℕ) (hr : r ≤ n) :
    (n * n * b : ℕ) - Real.log (F.card : ℝ) / Real.log 2 +
      observationEntropy (uniformWeight F) (T.attainedHelper F) / Real.log 2 ≥
        (b * r * (n-r) : ℕ) := by
  have h := T.helper_entropy_deficit_bound_of_distribution F hc
    (uniformWeight F) (uniformWeight_nonneg F) (sum_uniformWeight F) r hr
  simpa only [entropy_uniformWeight, Fintype.card_coe] using h

/-- The quarter toll for every input law supported on the correct family. -/
theorem quarter_helper_entropy_deficit_bound_of_distribution
    (F : Finset (FiniteMatrix n b)) (hc : T.CorrectOn F)
    (p : F → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    (n * n * b : ℕ) - entropy p / Real.log 2 +
      observationEntropy p (T.attainedHelper F) / Real.log 2 ≥
        (b * (n * n / 4) : ℕ) := by
  have h := T.helper_entropy_deficit_bound_of_distribution F hc p hp hp1
    (n / 2) (Nat.div_le_self n 2)
  rwa [mul_assoc b, half_product_eq_floor_quarter] at h

/-- Entropy form of the exact quarter toll; the ambient helper type may be infinite. -/
theorem quarter_helper_entropy_deficit_bound (F : Finset (FiniteMatrix n b)) [Nonempty F]
    (hc : T.CorrectOn F) :
    (n * n * b : Nat) - Real.log (F.card : Real) / Real.log 2 +
      observationEntropy (uniformWeight F) (T.attainedHelper F) / Real.log 2 ≥
        (b * (n * n / 4) : Nat) := by
  have h := T.helper_entropy_deficit_bound F hc (n / 2) (Nat.div_le_self n 2)
  rwa [mul_assoc b, half_product_eq_floor_quarter] at h

end TransposeFollowup.TwoStageHelper

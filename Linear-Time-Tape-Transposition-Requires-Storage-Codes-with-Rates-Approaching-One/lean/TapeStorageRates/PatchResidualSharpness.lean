import TapeStorageRates.PatchesGeometry
import TapeStorageRates.PatchPredictionError
import TransposeFollowup.UniformEntropy

/-! # A noisy pair attains the prediction bounds at every error level -/

namespace TapeStorageRates

open Finset DirectedRecovery TransposeFollowup
open scoped BigOperators

set_option autoImplicit false

/-- Each of two fair bits predicts its partner with error `e`. The partners
have infinite paired distance and give equality in both the helper entropy
and the binary prediction-error bounds, in a single patch of overlap one. -/
theorem noisy_pair_prediction_sharp (e : ℝ) (he₀ : 0 ≤ e) (he₁ : e ≤ 1) :
    ∃ (p : Bool × Bool → ℝ) (X : Bool × Bool → Bool → Bool),
      (∀ u, 0 ≤ p u) ∧ (∑ u, p u = 1) ∧
      (∀ t, shortPairedCoordinates (fun q : Bool => {!q}) t = ∅) ∧
      (∀ q, trueMass p (fun u => X u q) = 2⁻¹) ∧
      (∀ q, trueMass p (fun u => decide (X u (!q) ≠ X u q)) = e) ∧
      (∀ q, coordinateEntropy p X (insert q {!q}) - coordinateEntropy p X {!q} =
        Real.binEntropy e) ∧
      2 * (Real.log 2 - Real.binEntropy e) = 2 * (2 * Real.log 2 - observationEntropy p X) := by
  classical
  let p (u : Bool × Bool) := (if u.1 = u.2 then 1-e else e) / 2
  let X (u : Bool × Bool) (q : Bool) := if q then u.2 else u.1
  have hp (u : Bool × Bool) : 0 ≤ p u := by
    dsimp [p]; split <;> positivity
  have hp1 : ∑ u, p u = 1 := by
    simp [p, Fintype.sum_prod_type]; ring
  have hinj : Function.Injective X := fun _ _ h => Prod.ext (congrFun h false) (congrFun h true)
  have hhalf : 2 * Real.negMulLog ((2:ℝ)⁻¹) = Real.log 2 := by
    have h := Real.binEntropy_two_inv
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, show 1-(2:ℝ)⁻¹ = 2⁻¹ by norm_num,
      ← two_mul] at h
    exact h
  have ht : observationEntropy p X = Real.log 2 + Real.binEntropy e := by
    rw [observationEntropy_injective p hp X hinj, ← hhalf, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp [entropy, p, Fintype.sum_prod_type, div_eq_mul_inv, Real.negMulLog_mul]
    ring
  have hm (q : Bool) : trueMass p (fun u => X u q) = 2⁻¹ := by
    cases q <;> simp [trueMass, pushforward, X, p, Fintype.sum_prod_type] <;> ring
  refine ⟨p,X,hp,hp1,shortPairedCoordinates_eq_empty_of_colors _ id (!·)
    (by decide) (fun _ _ h => mem_singleton.mp h), hm, ?_, ?_, by rw [ht]; ring⟩
  · intro q
    cases q <;> simp [trueMass, pushforward, X, p, Fintype.sum_prod_type]
  · intro q
    have hun : insert q ({!q} : Finset Bool) = univ := by cases q <;> decide
    have hsing : coordinateEntropy p X {!q} = observationEntropy p (fun u => X u (!q)) := by
      apply observationEntropy_eq_of_same_fibers p hp
      intro x y
      simp [bitView_eq_iff]
    rw [hun, coordinateEntropy_univ, ht, hsing, observationEntropy_bool_eq_binEntropy p hp1, hm,
      Real.binEntropy_two_inv]
    ring

end TapeStorageRates

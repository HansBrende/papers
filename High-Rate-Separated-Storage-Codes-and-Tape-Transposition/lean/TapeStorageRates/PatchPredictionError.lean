import TransposeFollowup.PacketInformation
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! # Binary prediction from a permitted helper set

A target bit is determined by the prediction and its error indicator. This
gives the binary error bound in nats for arbitrary finite probability laws.
-/

namespace TapeStorageRates

open Finset TransposeFollowup
open scoped BigOperators

set_option autoImplicit false

variable {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]

/-- The probability of a Boolean event under a finite law. -/
noncomputable abbrev trueMass (p : Ω → ℝ) (f : Ω → Bool) : ℝ := pushforward p f true

theorem trueMass_mem_Icc (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (f : Ω → Bool) : trueMass p f ∈ Set.Icc 0 1 := by
  have ht := sum_pushforward p f
  rw [hp1, Fintype.sum_bool] at ht
  exact ⟨pushforward_nonneg p hp f true, by
    have := pushforward_nonneg p hp f false
    change pushforward p f true ≤ 1
    linarith⟩

theorem observationEntropy_bool_eq_binEntropy (p : Ω → ℝ) (hp1 : ∑ x, p x = 1)
    (f : Ω → Bool) : observationEntropy p f = Real.binEntropy (trueMass p f) := by
  have h := sum_pushforward p f
  rw [hp1, Fintype.sum_bool] at h
  have hf : pushforward p f false = 1 - trueMass p f := by unfold trueMass; linarith
  simp only [observationEntropy, entropy, Fintype.sum_bool, hf,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, trueMass]

/-- Conditional uncertainty about a bit after seeing its helper coordinates
is bounded by the binary entropy of the actual error of any predictor. -/
theorem coordinateEntropy_insert_le_of_predictor (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (X : Ω → V → Bool) (q : V) (B : Finset V)
    (predict : (V → Bool) → Bool) :
    coordinateEntropy p X (insert q B) - coordinateEntropy p X B ≤
      Real.binEntropy (trueMass p fun x => decide (predict (bitView B (X x)) ≠ X x q)) := by
  let view (x : Ω) := bitView B (X x)
  let err (x : Ω) := decide (predict (view x) ≠ X x q)
  have hf : (fun x => bitView (insert q B) (X x)).FactorsThrough
      (fun x => (view x, err x)) := by
    intro x y h
    have hv : view x = view y := congrArg Prod.fst h
    have he : decide (predict (view x) ≠ X x q) = decide (predict (view y) ≠ X y q) :=
      congrArg Prod.snd h
    rw [hv] at he
    apply (bitView_eq_iff _ _ _).mpr
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · exact (by decide : ∀ a b c : Bool, decide (a ≠ b) = decide (a ≠ c) → b = c) _ _ _ he
    · exact (bitView_eq_iff B _ _).mp hv i hi
  have hb := (observationEntropy_le_of_factorsThrough p hp _ _ hf).trans
    (observationEntropy_pair_le_sum p hp hp1 view err)
  rw [observationEntropy_bool_eq_binEntropy p hp1 err] at hb
  exact sub_le_iff_le_add'.mpr hb

/-- Uniform Jensen inequality, including an empty family of scored targets. -/
theorem sum_binEntropy_le_card_mul {I : Type*} [Fintype I] (e : I → ℝ)
    (he : ∀ i, e i ∈ Set.Icc 0 1) :
    ∑ i, Real.binEntropy (e i) ≤
      Fintype.card I * Real.binEntropy ((∑ i, e i) / Fintype.card I) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hempty => simp
  | inr hnon =>
    have hn : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
    have hj := Real.strictConcave_binEntropy.concaveOn.le_map_centerMass
      (t := (univ : Finset I)) (w := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
      (by simpa using hn) (fun i _ => he i)
    simp only [centerMass, sum_const, card_univ, nsmul_eq_mul, mul_one,
      Function.comp_apply, smul_eq_mul, one_mul, ← div_eq_inv_mul] at hj
    exact (div_le_iff₀' hn).mp hj

/-- The sum of the actual error probabilities is the expected total number
of errors. Either index family can be empty. -/
theorem sum_trueMass_eq_expected_count {I : Type*} [Fintype I]
    (p : Ω → ℝ) (f : I → Ω → Bool) :
    ∑ i, trueMass p (f i) =
      ∑ x, p x * ((univ.filter fun i => f i x = true).card : ℝ) := by
  classical
  unfold trueMass pushforward
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [← sum_boole (R := ℝ), mul_sum]
  apply sum_congr rfl
  intro i _
  by_cases h : f i x = true <;> simp [h]

end TapeStorageRates

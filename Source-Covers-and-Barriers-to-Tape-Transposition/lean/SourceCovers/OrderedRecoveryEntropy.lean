import LeanMachine.OrderedRecovery
import TransposeFollowup.UniformEntropy
import TransposeFollowup.CoordinateEntropy
import TransposeFollowup.PacketInformation

/-!
# Entropy cost of ordered recovery

One helper and the unselected raw coordinates determine the entire input by
reverse recovery. Existing finite-entropy inequalities then charge the helper
by its entropy, not by the cardinality of its range. The law may be correlated;
uniform correctness sets are only a specialization.
-/

namespace SourceCovers

open Classical Finset TransposeFollowup
open scoped BigOperators

noncomputable section

variable {Ω V H : Type*} [Fintype Ω] [Fintype V] [Fintype H]

/-- The entropy of a recoverable input is bounded by the helper and the actual
entropy of its coordinate complement, for any probability law. -/
theorem orderedRecovery_entropy_le (p : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → V → Bool) (Z : Ω → H) (A : Finset V) (N : V → Set V)
    (rank : V → ℕ)
    (hforward : ∀ v ∈ A, ∀ u ∈ N v, u ∈ A → rank v < rank u)
    (hlocal : ∀ v ∈ A, ∀ x y, Z x = Z y →
      Set.EqOn (X x) (X y) (N v) → X x v = X y v) :
    observationEntropy p X ≤ observationEntropy p Z + coordinateEntropy p X Aᶜ := by
  have hdet : X.FactorsThrough (fun x => (Z x, bitView Aᶜ (X x))) := by
    intro x y h
    apply LeanMachine.OrderedRecovery.eq_of_rank X Z (A : Set V) N rank
      hforward hlocal (congrArg Prod.fst h)
    intro v hv
    exact (bitView_eq_iff _ _ _).mp (congrArg Prod.snd h) v (by simpa using hv)
  exact (observationEntropy_le_of_factorsThrough p hp _ X hdet).trans
    (observationEntropy_pair_le_sum p hp hp1 Z (fun x => bitView Aᶜ (X x)))

/-- The complement has at most one bit per coordinate. -/
theorem orderedRecovery_entropy_le_card (p : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → V → Bool) (Z : Ω → H) (A : Finset V) (N : V → Set V)
    (rank : V → ℕ)
    (hforward : ∀ v ∈ A, ∀ u ∈ N v, u ∈ A → rank v < rank u)
    (hlocal : ∀ v ∈ A, ∀ x y, Z x = Z y →
      Set.EqOn (X x) (X y) (N v) → X x v = X y v) :
    observationEntropy p X ≤ observationEntropy p Z +
      ((Fintype.card V : ℝ) - A.card) * Real.log 2 := by
  have h := (orderedRecovery_entropy_le p hp hp1 X Z A N rank hforward hlocal).trans
    (add_le_add le_rfl (coordinateEntropy_le_card p hp hp1 X Aᶜ))
  simpa only [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ A)] using h

/-- Correctness deficit and helper entropy, both measured in bits. Only the
selected dependencies need increase in rank; rank injectivity is not needed. -/
theorem orderedRecovery_card_le_deficit_add_helper
    (C : Finset (V → Bool)) (hC : C.Nonempty) (Z : C → H)
    (A : Finset V) (N : V → Set V) (rank : V → ℕ)
    (hforward : ∀ v ∈ A, ∀ u ∈ N v, u ∈ A → rank v < rank u)
    (hlocal : ∀ v ∈ A, ∀ x y : C, Z x = Z y →
      Set.EqOn x.val y.val (N v) → x.val v = y.val v) :
    (A.card : ℝ) ≤ (Fintype.card V : ℝ) - Real.log (C.card : ℝ) / Real.log 2 +
      observationEntropy (uniformWeight C) Z / Real.log 2 := by
  let : Nonempty C := hC.to_subtype
  have he : observationEntropy (uniformWeight C) (fun x : C => x.val) =
      Real.log (C.card : ℝ) := by
    rw [observationEntropy_injective _ (uniformWeight_nonneg C) _ Subtype.val_injective,
      entropy_uniformWeight, Fintype.card_coe]
  have h := orderedRecovery_entropy_le_card (uniformWeight C) (uniformWeight_nonneg C)
    (sum_uniformWeight C) (fun x : C => x.val) Z A N rank hforward hlocal
  rw [he] at h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (A.card : ℝ) ≤ ((Fintype.card V : ℝ) * Real.log 2 - Real.log (C.card : ℝ) +
        observationEntropy (uniformWeight C) Z) / Real.log 2 := by
      apply (le_div_iff₀ hlog).mpr
      nlinarith
    _ = _ := by field_simp

/-- Any distribution over valid selections may be averaged, with one common
helper. No independence between demanded and source coordinates is used. -/
theorem orderedRecovery_weighted_card_le_deficit_add_helper
    {I : Type*} [Fintype I] (C : Finset (V → Bool)) (hC : C.Nonempty)
    (Z : C → H) (A : I → Finset V) (N : I → V → Set V) (rank : I → V → ℕ)
    (hforward : ∀ i, ∀ v ∈ A i, ∀ u ∈ N i v, u ∈ A i → rank i v < rank i u)
    (hlocal : ∀ i, ∀ v ∈ A i, ∀ x y : C, Z x = Z y →
      Set.EqOn x.val y.val (N i v) → x.val v = y.val v)
    (weight : I → ℝ) (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1) :
    (∑ i, weight i * (A i).card) ≤
      (Fintype.card V : ℝ) - Real.log (C.card : ℝ) / Real.log 2 +
        observationEntropy (uniformWeight C) Z / Real.log 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left
      (orderedRecovery_card_le_deficit_add_helper C hC Z (A i) (N i) (rank i)
        (hforward i) (hlocal i)) (hw i))
  simpa only [← Finset.sum_mul, hw1, one_mul] using h

/-- Uniform averaging over a nonempty finite family of common orders. -/
theorem orderedRecovery_average_card_le_deficit_add_helper
    {I : Type*} [Fintype I] [Nonempty I]
    (C : Finset (V → Bool)) (hC : C.Nonempty) (Z : C → H)
    (A : I → Finset V) (N : I → V → Set V) (rank : I → V → ℕ)
    (hforward : ∀ i, ∀ v ∈ A i, ∀ u ∈ N i v, u ∈ A i → rank i v < rank i u)
    (hlocal : ∀ i, ∀ v ∈ A i, ∀ x y : C, Z x = Z y →
      Set.EqOn x.val y.val (N i v) → x.val v = y.val v) :
    (∑ i, ((A i).card : ℝ)) / Fintype.card I ≤
      (Fintype.card V : ℝ) - Real.log (C.card : ℝ) / Real.log 2 +
        observationEntropy (uniformWeight C) Z / Real.log 2 := by
  have h := orderedRecovery_weighted_card_le_deficit_add_helper C hC Z A N rank
    hforward hlocal (uniformWeight I) (uniformWeight_nonneg I) (sum_uniformWeight I)
  simpa only [uniformWeight, ← Finset.mul_sum, div_eq_inv_mul] using h

/-- Revealing `U` raw bits jointly with any helper costs at most `|U|`
additional bits, even when the correctness law is correlated. -/
theorem helperEntropy_pair_raw_bits_le [DecidableEq V]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (Z : Ω → H) (X : Ω → V → Bool) (U : Finset V) (g : ℝ)
    (hZ : observationEntropy p Z / Real.log 2 ≤ g) :
    observationEntropy p (fun x => (Z x, bitView U (X x))) / Real.log 2 ≤
      g + U.card := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := (observationEntropy_pair_le_sum p hp hp1 Z
      (fun x => bitView U (X x))).trans
    (add_le_add le_rfl (coordinateEntropy_le_card p hp hp1 X U))
  apply (div_le_iff₀ hlog).mpr
  have hZ' := (div_le_iff₀ hlog).mp hZ
  nlinarith

end

end SourceCovers

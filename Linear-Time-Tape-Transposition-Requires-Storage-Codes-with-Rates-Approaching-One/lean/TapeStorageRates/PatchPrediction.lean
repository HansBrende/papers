import TapeStorageRates.PatchPredictionError
import TapeStorageRates.PatchResidual

/-! # Prediction accuracy on separated targets

Each scored occurrence belongs to one declared patch. The helper bits are
read from that patch and may be processed by any Boolean prediction rule.
-/

namespace TapeStorageRates

open Finset TransposeFollowup DirectedRecovery
open scoped BigOperators

set_option autoImplicit false

/-- A fixed system of patch predictors. A target scored in several patches
is counted separately for each occurrence, just as the patch load is. -/
structure PatchPredictor (V J : Type*) [Fintype V] [DecidableEq V] [Fintype J]
    (w r : ℕ) where
  relation : V → Finset V
  patch : J → Finset V
  targets : J → Finset V
  helpers : J → V → Finset V
  predict : J → V → (V → Bool) → Bool
  size_le : ∀ j, (targets j).card ≤ w
  load_le : ∀ v, (univ.filter fun j => v ∈ patch j).card ≤ r
  within : ∀ j, targets j ⊆ patch j
  permitted : ∀ j, ∀ q ∈ targets j, helpers j q ⊆ relation q ∩ patch j
  far : ∀ j, ∀ q ∈ targets j, q ∉ shortPairedCoordinates relation (2*w-1)

namespace PatchPredictor

variable {V J Ω : Type*} [Fintype V] [DecidableEq V] [Fintype J] [Fintype Ω] {w r : ℕ}
variable (D : PatchPredictor V J w r)

/-- Each predictor is scored only on the targets specified by its patch. -/
abbrev Scored := (j : J) × ↥(D.targets j)

noncomputable abbrev targetCount := Fintype.card D.Scored

/-- An actual prediction error. Outside its helper coordinates the predictor
receives the fixed value false. -/
def missed (i : D.Scored) (x : V → Bool) : Bool :=
  decide (D.predict i.1 i.2 (bitView (D.helpers i.1 i.2) x) ≠ x i.2)

def mistakeCount (x : V → Bool) : ℕ :=
  (univ.filter fun i => D.missed i x = true).card

/-- Error probability for this target in its specified patch. -/
noncomputable abbrev errorRate (p : Ω → ℝ) (X : Ω → V → Bool) (i : D.Scored) : ℝ :=
  trueMass p fun x => D.missed i (X x)

/-- Average error probability over the scored occurrences. The empty
system has mean error zero. -/
noncomputable def meanError (p : Ω → ℝ) (X : Ω → V → Bool) : ℝ :=
  (∑ i : D.Scored, D.errorRate p X i) / D.targetCount

theorem meanError_nonneg (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (X : Ω → V → Bool) :
    0 ≤ D.meanError p X := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact sum_nonneg fun i _ => pushforward_nonneg p hp _ true

/-- A pointwise cap on the fraction of mistaken predictions also bounds
the mean error under every probability law on those inputs. -/
theorem meanError_le_of_mistakeCount (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (X : Ω → V → Bool) {e : ℝ} (he : 0 ≤ e)
    (hmist : ∀ x, (D.mistakeCount (X x) : ℝ) ≤ e * D.targetCount) :
    D.meanError p X ≤ e := by
  unfold meanError
  by_cases hc : D.targetCount = 0
  · simpa [hc] using he
  have hn : 0 < (D.targetCount : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hc
  apply (div_le_iff₀ hn).mpr
  rw [sum_trueMass_eq_expected_count]
  calc
    _ ≤ ∑ x, p x * (e * D.targetCount) :=
      sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hmist x) (hp x)
    _ = _ := by rw [← sum_mul, hp1, one_mul]

/-- Each actual target error contributes its own binary entropy. Singleton
capacities may be chosen as the marginal entropies to bound improvements over
a biased source by its total correlation. Entropies are in nats. -/
theorem prediction_capacity (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (X : Ω → V → Bool) (cap : V → ℝ)
    (hcap : ∀ q, coordinateEntropy p X {q} ≤ cap q) :
    (∑ i : D.Scored, (cap i.2 - Real.binEntropy (D.errorRate p X i))) ≤
      r * (((∑ q, cap q) - observationEntropy p X) +
        ((∑ q, coordinateEntropy p X {q}) - observationEntropy p X)) := by
  have h := patch_capacity_of_long_targets (bit_coordinate_polymatroid p hp hp1 X) cap hcap
    D.relation D.patch D.targets D.helpers w r D.size_le D.load_le D.within D.permitted D.far
  rw [coordinateEntropy_univ] at h
  apply le_trans _ h
  rw [Fintype.sum_sigma]
  apply sum_le_sum
  intro j _
  rw [← sum_coe_sort (D.targets j)]
  exact sum_le_sum fun q _ => sub_le_sub_left
    (coordinateEntropy_insert_le_of_predictor p hp hp1 X q.val (D.helpers j q) (D.predict j q)) _

/-- The original aggregate prediction bound follows by uniform Jensen and the
one-bit upper bound on each marginal entropy. -/
theorem prediction_deficit (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (X : Ω → V → Bool) :
    D.targetCount * (1 - Real.binEntropy (D.meanError p X) / Real.log 2) ≤
      2 * (r:ℝ) * (Fintype.card V - observationEntropy p X / Real.log 2) := by
  have hcap (q : V) : coordinateEntropy p X {q} ≤ Real.log 2 := by
    simpa using coordinateEntropy_le_card p hp hp1 X {q}
  have h := D.prediction_capacity p hp hp1 X (fun _ => Real.log 2) hcap
  have hm := mul_le_mul_of_nonneg_left (sum_le_sum (s := univ) fun q _ => hcap q) (Nat.cast_nonneg r (α := ℝ))
  have hj : (∑ i : D.Scored, Real.binEntropy (D.errorRate p X i)) ≤
      D.targetCount * Real.binEntropy (D.meanError p X) :=
    sum_binEntropy_le_card_mul _ fun _ => trueMass_mem_Icc p hp hp1 _
  simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul] at h hm
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (mul_le_mul_iff_of_pos_right hl).mp
  field_simp
  linarith only [h, hm, hj]

end PatchPredictor

end TapeStorageRates

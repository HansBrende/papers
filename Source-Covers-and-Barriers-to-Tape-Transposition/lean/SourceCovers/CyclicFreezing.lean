import SourceCovers.FrozenSourceBank
import SourceCovers.CyclicAccounting
import SourceCovers.CyclicRecoveryEntropy
import LeanMachine.CyclicStripeAverage
import LeanMachine.PeriodicStripeSum

/-!
# Cyclic freezing for an actual transpose source bank

One common circular ordering serves every column. The finite bound retains
the maximum slot oscillations and the sharp stripe error; total bank variation
then gives the manuscript's bound, with a smaller additive error.
-/

namespace SourceCovers

open Classical Finset LeanMachine CyclicSelection TransposeFollowup
open scoped BigOperators

noncomputable section

variable {ι H : Type*} [Fintype ι] [Nonempty ι] [Fintype H]
    {d b w θ : ℕ} {t : ℕ → ℕ} {Y : ι → ℕ → ℕ}
    {C : Finset (Fin (d * d * b) → Bool)} {Z : C → H} {g : ℝ}

/-- Sharp finite cyclic freezing. Only the frozen anchors must lie in the
input range; arbitrary nonlinear recovery is allowed on a correlated set. -/
theorem cyclic_freezing_oscillation
    (hd : 0 < d) (hb : 0 < b) (hw : 0 < w)
    (ht : StrictMonoOn t (Set.Iio (d * d * b)))
    (hanchors : ∀ j < d, frozenAnchors Y t (d * b) j ⊆ range (d * d * b))
    (hC : C.Nonempty) (hlocal : TransposeBankRecovers C Z Y t w θ)
    (hZ : observationEntropy (uniformWeight C) Z / Real.log 2 ≤ g) :
    (d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2 ≥
      (d : ℝ) * b * (∑ j ∈ range d, frozenArea Y t d b j) -
        2 * (∑ j ∈ range d, (columnRadius Y t (d * b) j : ℝ)) / d -
        2 * ((w : ℝ) - 1) - ((d : ℝ) * b - b + 1) / 2 - g := by
  let L := d * d * b
  let r := fun j => w - 1 + columnRadius Y t (d * b) j
  let T := frozenOvercover Y t d b w
  let Q := fun j => (∑ z ∈ PeriodicStripe.stripe d b j,
    ((selectingOrders L (T j) z).card : ℝ)) / (2 * L)
  have hL : 0 < L := Nat.mul_pos (Nat.mul_pos hd hd) hb
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hcolumn (j : ℕ) (hj : j < d) :
      (d : ℝ) * b * frozenArea Y t d b j - (2 * r j + 1 / 2) / d -
        b * (1 - 1 / (d : ℝ)) / 2 ≤ Q j := by
    have hSL : frozenAnchors Y t (d * b) j ⊆ range (d * (d * b)) := by
      simpa only [Nat.mul_assoc] using hanchors j hj
    have h := CyclicStripeAverage.pointArea_lower (r := r j) hd hb hj
      (frozenAnchors Y t (d * b) j) (frozenAnchors_nonempty Y t (d * b) j) hSL
    simpa only [frozenArea, Q, T, frozenOvercover, L, r, Nat.mul_assoc,
      Nat.cast_mul] using h
  have hlower := cyclic_column_accounting hd (frozenArea Y t d b) Q r hcolumn
  have hupper := cyclicRecovery_selection_sum_le hL C hC Z
    (fun z => T (z / b % d)) (frozenOvercover_recovers hd hb hw ht hlocal)
  have hsum : (∑ j ∈ range d, Q j) =
      (∑ z ∈ range L, ((selectingOrders L (T (z / b % d)) z).card : ℝ)) /
        (2 * L) := by
    simp only [Q, ← sum_div]
    rw [PeriodicStripe.sum_stripe_eq_sum_coordinates]
    simp only [L, Nat.mul_assoc]
  rw [hsum] at hlower
  have hupper' := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * L)).mpr
    (hupper.trans_eq (mul_comm _ _))
  have hsumr : (∑ j ∈ range d, (r j : ℝ)) =
      (d : ℝ) * ((w : ℝ) - 1) +
        ∑ j ∈ range d, (columnRadius Y t (d * b) j : ℝ) := by
    simp only [r, Nat.cast_add, Nat.cast_sub (Nat.one_le_of_lt hw), Nat.cast_one,
      sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  rw [hsumr] at hlower
  have hcancel : 2 * ((d : ℝ) * ((w : ℝ) - 1) +
        ∑ j ∈ range d, (columnRadius Y t (d * b) j : ℝ)) / d =
      2 * ((w : ℝ) - 1) +
        2 * (∑ j ∈ range d, (columnRadius Y t (d * b) j : ℝ)) / d := by
    field_simp
  rw [hcancel] at hlower
  simp only [L, Nat.cast_mul] at hlower hupper'
  linarith

/-- Theorem F, with the improved additive error `(W - b + 1) / 2`.
The motion bill is the total variation of the actual finite bank. -/
theorem cyclic_freezing {n : ℕ}
    (hd : 0 < d) (hb : 0 < b) (hw : 0 < w)
    (ht : StrictMonoOn t (Set.Iio (d * d * b)))
    (hn : ∀ r < d * d * b, t r ≤ n)
    (hY : ∀ i s, s ≤ n → Y i s < d * d * b)
    (hC : C.Nonempty) (hlocal : TransposeBankRecovers C Z Y t w θ)
    (hZ : observationEntropy (uniformWeight C) Z / Real.log 2 ≤ g) :
    (d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2 ≥
      (d : ℝ) * b * (∑ j ∈ range d, frozenArea Y t d b j) -
        2 * (∑ i, MonotonePatches.variation (fun s => (Y i s : ℝ)) n) / d -
        2 * ((w : ℝ) - 1) - ((d : ℝ) * b - b + 1) / 2 - g := by
  have h := cyclic_freezing_oscillation hd hb hw ht
    (fun _ hj => frozenAnchors_subset hd hb hj hn hY) hC hlocal hZ
  have hρ := sum_column_radius_le Y hd hb ht hn
  change (∑ j : Fin d, (columnRadius Y t (d * b) j : ℝ)) ≤ _ at hρ
  rw [Fin.sum_univ_eq_sum_range (fun j => (columnRadius Y t (d * b) j : ℝ))] at hρ
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hρ (show (0 : ℝ) ≤ 2 by norm_num))
    (show (0 : ℝ) ≤ d by positivity)
  linarith

section Genie

variable {K R : Type*} [Fintype K] [Fintype R] {n : ℕ}
    (G : C → K → R) (β : ℝ)
    (hd : 0 < d) (hb : 0 < b) (hw : 0 < w)
    (ht : StrictMonoOn t (Set.Iio (d * d * b)))
    (hn : ∀ r < d * d * b, t r ≤ n)
    (hY : ∀ i s, s ≤ n → Y i s < d * d * b)
    (hC : C.Nonempty)
    (hR : Real.log (Fintype.card R : ℝ) / Real.log 2 ≤ β)

include hd hb hw ht hn hY hC hR

/-- Whole-step genie specialization, with a real-valued capacity per record. -/
theorem cyclic_freezing_genie (hlocal : TransposeBankRecovers C G Y t w θ) :
    (d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2 ≥
      (d : ℝ) * b * (∑ j ∈ range d, frozenArea Y t d b j) -
        2 * (∑ i, MonotonePatches.variation (fun s => (Y i s : ℝ)) n) / d -
        2 * ((w : ℝ) - 1) - ((d : ℝ) * b - b + 1) / 2 - β * Fintype.card K := by
  let : Nonempty C := hC.to_subtype
  exact cyclic_freezing hd hb hw ht hn hY hC hlocal
    (helperEntropy_recordTuple_bits_le_real (uniformWeight C) (uniformWeight_nonneg C)
      (sum_uniformWeight C) G β hR)

/-- A whole-step genie and fixed additional raw coordinates are charged jointly. -/
theorem cyclic_freezing_genie_raw (U : Finset (Fin (d * d * b)))
    (hlocal : TransposeBankRecovers C (fun x => (G x, bitView U x.val)) Y t w θ) :
    (d * d * b : ℝ) - Real.log (C.card : ℝ) / Real.log 2 ≥
      (d : ℝ) * b * (∑ j ∈ range d, frozenArea Y t d b j) -
        2 * (∑ i, MonotonePatches.variation (fun s => (Y i s : ℝ)) n) / d -
        2 * ((w : ℝ) - 1) - ((d : ℝ) * b - b + 1) / 2 -
        (β * Fintype.card K + U.card) := by
  let : Nonempty C := hC.to_subtype
  have hG := helperEntropy_recordTuple_bits_le_real (uniformWeight C) (uniformWeight_nonneg C)
    (sum_uniformWeight C) G β hR
  have hGU : observationEntropy (uniformWeight C)
      (fun x : C => (G x, bitView U x.val)) / Real.log 2 ≤ β * Fintype.card K + U.card :=
    helperEntropy_pair_raw_bits_le (uniformWeight C) (uniformWeight_nonneg C)
      (sum_uniformWeight C) G (fun x : C => x.val) U (β * Fintype.card K) hG
  exact cyclic_freezing (Z := fun x : C => (G x, bitView U x.val))
    (g := β * Fintype.card K + U.card) hd hb hw ht hn hY hC hlocal hGU

end Genie

end
end SourceCovers

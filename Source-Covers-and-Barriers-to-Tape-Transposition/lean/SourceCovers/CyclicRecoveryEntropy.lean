import LeanMachine.CyclicArcSelection
import SourceCovers.OrderedRecoveryEntropy

/-!
# Entropy upper bound for actual circular selections

The two finite orientations and all `L` cuts use a common helper. A finite
double count converts the average selected-coordinate bound into a sum of
per-coordinate safe-order counts. Source sets need not be disjoint or bounded.
-/

namespace SourceCovers

open Classical Finset LeanMachine.CyclicSelection TransposeFollowup
open scoped BigOperators

noncomputable section

/-- Coordinate selections for one common cut and orientation. -/
def cyclicSelected (L : ℕ) (T : ℕ → Finset ℕ) (p : Fin L × Bool) : Finset (Fin L) :=
  univ.filter fun z => (p.1.val, p.2) ∈ selectingOrders L (T z.val) z.val

private theorem card_fin_selectingOrders (L : ℕ) (T : Finset ℕ) (z : ℕ) :
    ((univ : Finset (Fin L × Bool)).filter
      (fun p => (p.1.val, p.2) ∈ selectingOrders L T z)).card =
      (selectingOrders L T z).card := by
  apply card_bij (fun p _ => (p.1.val, p.2))
  · intro p hp
    exact (mem_filter.mp hp).2
  · intro p hp q hq he
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst he)
    · exact congrArg (fun p : ℕ × Bool => p.2) he
  · intro p hp
    have hcut : p.1 < L := mem_range.mp (mem_product.mp (mem_filter.mp hp).1).1
    exact ⟨(⟨p.1, hcut⟩, p.2), mem_filter.mpr ⟨mem_univ _, hp⟩, rfl⟩

/-- Double counting point/order incidences, with the finite coordinate bridge
handled once here. -/
theorem sum_cyclicSelected_card (L : ℕ) (T : ℕ → Finset ℕ) :
    (∑ p : Fin L × Bool, (cyclicSelected L T p).card) =
      ∑ z ∈ range L, (selectingOrders L (T z) z).card := by
  calc
    _ = ∑ z : Fin L, ((univ : Finset (Fin L × Bool)).filter
        (fun p => (p.1.val, p.2) ∈ selectingOrders L (T z.val) z.val)).card := by
      simp only [cyclicSelected, card_filter]
      exact Finset.sum_comm
    _ = ∑ z : Fin L, (selectingOrders L (T z.val) z.val).card := by
      apply sum_congr rfl
      intro z _
      exact card_fin_selectingOrders L (T z.val) z.val
    _ = _ := Fin.sum_univ_eq_sum_range (fun z => (selectingOrders L (T z) z).card) L

/-- The total number of safe point/order incidences is controlled by the
correctness deficit and the entropy of the same helper for every order. -/
theorem cyclicRecovery_selection_sum_le {L : ℕ} (hL : 0 < L)
    {H : Type*} [Fintype H] (C : Finset (Fin L → Bool)) (hC : C.Nonempty)
    (Z : C → H) (T : ℕ → Finset ℕ)
    (hlocal : ∀ z : Fin L, ∀ x y : C, Z x = Z y →
      Set.EqOn x.val y.val {q : Fin L | q.val ∈ T z.val} → x.val z = y.val z) :
    (∑ z ∈ range L, ((selectingOrders L (T z) z).card : ℝ)) ≤
      (2 * L) * ((L : ℝ) - Real.log (C.card : ℝ) / Real.log 2 +
        observationEntropy (uniformWeight C) Z / Real.log 2) := by
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  let N := fun (_ : Fin L × Bool) (z : Fin L) => {q : Fin L | q.val ∈ T z.val}
  let r := fun (p : Fin L × Bool) (z : Fin L) => orientedRankNat L p.1.val p.2 z.val
  have hf : ∀ p, ∀ v ∈ cyclicSelected L T p, ∀ u ∈ N p v,
      u ∈ cyclicSelected L T p → r p v < r p u := by
    intro p v hv u hu _
    exact (mem_selectingOrders_iff_nat hL).mp (mem_filter.mp hv).2 |>.2 u.val hu
  have hd : ∀ p, ∀ v ∈ cyclicSelected L T p, ∀ x y : C, Z x = Z y →
      Set.EqOn x.val y.val (N p v) → x.val v = y.val v := by
    intro p v _ x y
    exact hlocal v x y
  have h := orderedRecovery_average_card_le_deficit_add_helper C hC Z
    (cyclicSelected L T) N r hf hd
  have hcount : (∑ p : Fin L × Bool, ((cyclicSelected L T p).card : ℝ)) =
      ∑ z ∈ range L, ((selectingOrders L (T z) z).card : ℝ) := by
    exact_mod_cast sum_cyclicSelected_card L T
  rw [hcount] at h
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul,
    Nat.cast_ofNat] at h
  have hpos : (0 : ℝ) < (L : ℝ) * 2 := by positivity
  have hb := (div_le_iff₀ hpos).mp h
  nlinarith

/-- Real-valued record capacities suffice. No rounding to an integral number
of bits and no independence of records is required. -/
theorem helperEntropy_recordTuple_bits_le_real
    {Ω K R : Type*} [Fintype Ω] [Nonempty Ω] [Fintype K] [Fintype R]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (Z : Ω → K → R) (β : ℝ) (hR : Real.log (Fintype.card R : ℝ) / Real.log 2 ≤ β) :
    observationEntropy p Z / Real.log 2 ≤ β * Fintype.card K := by
  let : Nonempty (K → R) := Nonempty.map Z inferInstance
  have h := entropy_le_log_card (pushforward p Z) (pushforward_nonneg p hp Z)
    (by rw [sum_pushforward, hp1])
  have hZ : observationEntropy p Z ≤
      (Fintype.card K : ℝ) * Real.log (Fintype.card R : ℝ) := by
    simpa only [observationEntropy, Fintype.card_fun, Nat.cast_pow, Real.log_pow] using h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hR' := (div_le_iff₀ hlog).mp hR
  have hm := mul_le_mul_of_nonneg_left hR' (Nat.cast_nonneg (α := ℝ) (Fintype.card K))
  apply (div_le_iff₀ hlog).mpr
  nlinarith

end
end SourceCovers

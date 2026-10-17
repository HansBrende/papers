import Transpose.Tape.Blocks
import Transpose.Tape.Locality

/-!
# Blocks and residency at the machine level

* `entryCells_slotSteps_card`: `e₂(J) = Σ_t e₂ᵗ(J)` for a union of slots.
* `entryPoints_slotSteps_card`: `e₁(J) = μ(J)`.
* `charging_bound`: `e₂ ≤ r χ + c k r μ` for any admissible residency (`c = 3` for pair residency).
* `srcRows_congr`, `srcRows_slotSteps_eq`: the rows read during a union of slots are the union of
  the rows read in its slots, and depend only on the input-head positions.
* `srcRows_slotSteps_card_le`: at most two rows per slot (P1).
-/

namespace Transpose.Tape.Impl

open Transpose

theorem mem_slotSteps {r T τ : ℕ} {U : Set ℕ} : τ ∈ slotSteps r U T ↔ τ < T ∧ τ / r ∈ U := by
  classical
  simp [slotSteps, Finset.mem_filter]

theorem entryCells_slotSteps_card (M : TM) (w : List Bool) (r : ℕ) (U : Set ℕ) (T : ℕ) :
    (entryCells (workTraj M w) (slotSteps r U T)).card =
      ∑ t : Fin M.k, (entryTimes r (fun τ => workTraj M w τ t) U T).card := by
  classical
  have heq : entryCells (workTraj M w) (slotSteps r U T) =
      Finset.univ.biUnion (fun t =>
        (entryTimes r (fun τ => workTraj M w τ t) U T).image (fun τ => (t, τ))) := by
    ext ⟨t, τ⟩
    simp only [mem_entryCells, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
      mem_entryTimes, mem_slotSteps, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hτT, hτU⟩, σ, hσJ, hσ⟩
      refine ⟨t, τ, ⟨hτT, hτU, σ, ?_, hσ⟩, rfl, rfl⟩
      intro hσU; exact hσJ ⟨lt_trans hσ.1 hτT, hσU⟩
    · rintro ⟨t', τ', ⟨hτT, hτU, σ, hσU, hσ⟩, rfl, rfl⟩
      exact ⟨⟨hτT, hτU⟩, σ, fun h => hσU h.2, hσ⟩
  rw [heq, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro t _
    exact Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)
  · intro t _ t' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_image] at hp hp'
    obtain ⟨τ, -, rfl⟩ := hp
    obtain ⟨τ', -, he⟩ := hp'
    exact hne (Prod.mk.inj he).1.symm

/-- Division facts: a step whose predecessor lies in another slot starts its slot. -/
theorem slot_start_of_div_ne {r τ : ℕ} (hr : 1 ≤ r) (hτ : 1 ≤ τ) (hne : (τ - 1) / r ≠ τ / r) :
    τ / r * r = τ ∧ (τ - 1) / r = τ / r - 1 ∧ 1 ≤ τ / r := by
  have hdm := Nat.div_add_mod' τ r
  have hm := Nat.mod_lt τ (show 0 < r by omega)
  set q := τ / r
  set m := τ % r
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have hτq : τ = q * r := by omega
    have hq : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · rw [h0] at hτq; omega
      · exact h0
    refine ⟨hτq.symm, ?_, hq⟩
    apply Nat.div_eq_of_lt_le
    · rw [Nat.sub_one_mul]; omega
    · rw [Nat.sub_add_cancel hq]; omega
  · exfalso
    apply hne
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.succ_mul]; omega

theorem entryPoints_slotSteps_card {r : ℕ} (hr : 1 ≤ r) (U : Set ℕ) (T : ℕ) :
    (entryPoints (slotSteps r U T)).card = (memBoundaries U (numSlots r T)).card := by
  classical
  apply Finset.card_nbij' (· / r) (· * r)
  · intro τ hτ
    simp only [Finset.mem_coe, mem_entryPoints, mem_slotSteps] at hτ
    obtain ⟨⟨hτT, hτU⟩, hτ0, hprev⟩ := hτ
    have hprevU : (τ - 1) / r ∉ U := fun h => hprev ⟨by omega, h⟩
    have hne : (τ - 1) / r ≠ τ / r := fun e => hprevU (e ▸ hτU)
    obtain ⟨-, hdiv, hq⟩ := slot_start_of_div_ne hr (by omega) hne
    simp only [Finset.mem_coe, memBoundaries, Finset.mem_filter, Finset.mem_range]
    refine ⟨div_lt_numSlots hr hτT, hτU, hq, ?_⟩
    rw [← hdiv]; exact hprevU
  · intro z hz
    simp only [Finset.mem_coe, memBoundaries, Finset.mem_filter, Finset.mem_range] at hz
    obtain ⟨hzN, hzU, hz1, hzprev⟩ := hz
    have hzT : z * r < T := (numSlots_spec hr).1 hzN
    simp only [Finset.mem_coe, mem_entryPoints, mem_slotSteps]
    have hdiv : z * r / r = z := Nat.mul_div_cancel z (by omega)
    have hzr : 1 * 1 ≤ z * r := Nat.mul_le_mul hz1 hr
    refine ⟨⟨hzT, by rw [hdiv]; exact hzU⟩, by omega, ?_⟩
    rintro ⟨-, hU⟩
    apply hzprev
    have : (z * r - 1) / r = z - 1 := by
      apply Nat.div_eq_of_lt_le
      · rw [Nat.sub_one_mul]; omega
      · rw [Nat.sub_add_cancel hz1]; omega
    rwa [this] at hU
  · intro τ hτ
    simp only [Finset.mem_coe, mem_entryPoints, mem_slotSteps] at hτ
    obtain ⟨⟨hτT, hτU⟩, hτ0, hprev⟩ := hτ
    have hprevU : (τ - 1) / r ∉ U := fun h => hprev ⟨by omega, h⟩
    have hne : (τ - 1) / r ≠ τ / r := fun e => hprevU (e ▸ hτU)
    exact (slot_start_of_div_ne hr (by omega) hne).1
  · intro z _
    exact Nat.mul_div_cancel z (by omega)

/-- **The Charging Lemma, any admissible residency:** `e₂(J) ≤ r χ(J) + c k r μ(J)`. With pair
residency (`c = 3`, `pairRes_admissible`) this is `e₂ ≤ r χ + 3 k r μ`. -/
theorem charging_bound (M : TM) (w : List Bool) {r : ℕ} (hr : 1 ≤ r) {T c : ℕ}
    (R : Fin M.k → ℕ → Finset ℤ) (hR : ∀ t, AdmissibleRes r (fun τ => workTraj M w τ t) T (R t) c)
    (U : Set ℕ) :
    (entryCells (workTraj M w) (slotSteps r U T)).card ≤
      r * (∑ t : Fin M.k, (chordsInto (R t) U (numSlots r T)).card) +
      c * M.k * r * (memBoundaries U (numSlots r T)).card := by
  rw [entryCells_slotSteps_card]
  calc ∑ t : Fin M.k, (entryTimes r (fun τ => workTraj M w τ t) U T).card
      ≤ ∑ t : Fin M.k, r * ((chordsInto (R t) U (numSlots r T)).card +
          c * (memBoundaries U (numSlots r T)).card) :=
        Finset.sum_le_sum (fun t _ => entryTimes_card_le hr (hR t) U)
    _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
        ring

/-- **(P1) for one slot**: if `r ≤ n b`, a slot reads at most two rows. -/
theorem rows_in_slot_card_le (M : TM) (w₀ : List Bool) {n b r : ℕ}
    (hrnb : r ≤ n * b) (T y : ℕ) : (srcRows M w₀ n b (slotOf r T y)).card ≤ 2 := by
  classical
  unfold srcRows
  set S := (Finset.range n).filter (fun i => ∃ τ ∈ slotOf r T y,
      ((i * n * b : ℕ) : ℤ) ≤ (run M w₀ τ).inPos ∧
        (run M w₀ τ).inPos < (((i + 1) * n * b : ℕ) : ℤ)) with hS
  by_cases hne : S.Nonempty
  · set m := S.min' hne
    have hsub : S ⊆ {m, m + 1} := by
      intro i hi
      have hmi : m ≤ i := Finset.min'_le _ _ hi
      have hm : m ∈ S := Finset.min'_mem _ _
      rw [hS, Finset.mem_filter] at hi hm
      obtain ⟨-, τ, hτ, hi1, hi2⟩ := hi
      obtain ⟨-, τ', hτ', hm1, hm2⟩ := hm
      rw [mem_slotOf] at hτ hτ'
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hc
      push Not at hc
      have hfar : m + 2 ≤ i := by omega
      have hd := slot_dist (unitSteps_inTraj M w₀) hτ'.1 hτ'.2.1 hτ.1 hτ.2.1
      simp only [inTraj] at hd
      have hprod : (m + 1) * n * b + n * b ≤ i * n * b := by
        have : (m + 2) * n * b ≤ i * n * b :=
          Nat.mul_le_mul_right b (Nat.mul_le_mul_right n hfar)
        have e : (m + 2) * n * b = (m + 1) * n * b + n * b := by ring
        omega
      have hprodZ : (((m + 1) * n * b : ℕ) : ℤ) + ((n * b : ℕ) : ℤ) ≤ ((i * n * b : ℕ) : ℤ) := by
        exact_mod_cast hprod
      have hrZ : (r : ℤ) ≤ ((n * b : ℕ) : ℤ) := by exact_mod_cast hrnb
      have := le_abs_self ((run M w₀ τ).inPos - (run M w₀ τ').inPos)
      linarith
    calc S.card ≤ ({m, m + 1} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := by refine le_trans (Finset.card_insert_le _ _) ?_; simp
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp

/-- The rows read during `J` depend only on the input-head positions during `J`. -/
theorem srcRows_congr {M : TM} {w w' : List Bool} {n b : ℕ} {J : Finset ℕ}
    (h : ∀ τ ∈ J, (run M w τ).inPos = (run M w' τ).inPos) :
    srcRows M w n b J = srcRows M w' n b J := by
  classical
  unfold srcRows
  exact Finset.filter_congr fun i _ => exists_congr fun τ => and_congr_right fun hτ => by
    rw [h τ hτ]

open Classical in
/-- The rows read during a union of slots are the union of the rows read in its slots. -/
theorem srcRows_slotSteps_eq {M : TM} {w : List Bool} {n b r T : ℕ} (hr : 1 ≤ r) (U : Set ℕ) :
    srcRows M w n b (slotSteps r U T) =
      ((Finset.range (numSlots r T)).filter (· ∈ U)).biUnion
        (fun y => srcRows M w n b (slotOf r T y)) := by
  classical
  ext i
  simp only [srcRows, Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, mem_slotSteps]
  constructor
  · rintro ⟨hi, τ, ⟨hτT, hτU⟩, h1, h2⟩
    exact ⟨τ / r, ⟨div_lt_numSlots hr hτT, hτU⟩, hi, τ, mem_slotOf_div hr hτT, h1, h2⟩
  · rintro ⟨y, ⟨-, hyU⟩, hi, τ, hτ, h1, h2⟩
    rw [mem_slotOf] at hτ
    refine ⟨hi, τ, ⟨hτ.2.2, ?_⟩, h1, h2⟩
    rw [slot_div hτ.1 hτ.2.1]; exact hyU

open Classical in
theorem srcRows_slotSteps_card_le (M : TM) (w₀ : List Bool) {n b r : ℕ} (hr : 1 ≤ r)
    (hrnb : r ≤ n * b) (U : Set ℕ) (T : ℕ) :
    (srcRows M w₀ n b (slotSteps r U T)).card ≤
      2 * ((Finset.range (numSlots r T)).filter (· ∈ U)).card := by
  rw [srcRows_slotSteps_eq hr, Nat.mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum fun y _ => rows_in_slot_card_le M w₀ hrnb T y)

end Transpose.Tape.Impl

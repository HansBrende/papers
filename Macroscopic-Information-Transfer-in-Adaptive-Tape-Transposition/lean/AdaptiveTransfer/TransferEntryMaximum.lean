import DirectedRecovery.StorageCode
import AdaptiveTransfer.FrozenCutInvoice

/-! The literal finite maximum over all nonlinear storage codes. -/

namespace AdaptiveTransfer.TransferEntry
open Finset MotionDepthCodes
attribute [local instance] Classical.propDecidable

noncomputable def maxCodeCard {V : Type*} [Fintype V] [DecidableEq V]
    (Q : V → Finset V) (m : ℕ) : ℕ :=
  ((univ : Finset (Finset (V → Fin m → Bool))).filter (IsStorageCode Q)).sup Finset.card

noncomputable def capacity {V : Type*} [Fintype V] [DecidableEq V]
    (Q : V → Finset V) (m : ℕ) : ℝ := Real.logb 2 (maxCodeCard Q m : ℝ)

noncomputable def deficit {V : Type*} [Fintype V] [DecidableEq V]
    (Q : V → Finset V) (m : ℕ) : ℝ := (m : ℝ) * Fintype.card V - capacity Q m

theorem code_card_le_max {V : Type*} [Fintype V] [DecidableEq V]
    {Q : V → Finset V} {m : ℕ} {C : Finset (V → Fin m → Bool)}
    (hC : IsStorageCode Q C) : C.card ≤ maxCodeCard Q m :=
  le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_univ _, hC⟩)

theorem exists_max_code {V : Type*} [Fintype V] [DecidableEq V]
    (Q : V → Finset V) (m : ℕ) :
    ∃ C : Finset (V → Fin m → Bool), IsStorageCode Q C ∧ C.card = maxCodeCard Q m := by
  have he : IsStorageCode Q (∅ : Finset (V → Fin m → Bool)) := by
    intro x hx
    exact (notMem_empty x hx).elim
  obtain ⟨C, hC, hcard⟩ := exists_mem_eq_sup
    ((univ : Finset (Finset (V → Fin m → Bool))).filter (IsStorageCode Q))
    ⟨∅, mem_filter.mpr ⟨mem_univ _, he⟩⟩ Finset.card
  exact ⟨C, (mem_filter.mp hC).2, hcard.symm⟩

theorem maxCodeCard_pos {V : Type*} [Fintype V] [DecidableEq V]
    (Q : V → Finset V) (m : ℕ) : 0 < maxCodeCard Q m := by
  let x : V → Fin m → Bool := fun _ _ => false
  have hc : IsStorageCode Q ({x} : Finset _) := by
    intro a ha b hb v _
    have ha' := mem_singleton.mp ha
    have hb' := mem_singleton.mp hb
    simp only [ha', hb']
  have hh := code_card_le_max hc
  simpa only [card_singleton, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero] using hh

theorem maxCodeCard_le {V : Type*} [Fintype V] [DecidableEq V]
    (Q : V → Finset V) (m : ℕ) : maxCodeCard Q m ≤ 2 ^ (m * Fintype.card V) := by
  apply Finset.sup_le
  intro C _
  have hh := C.card_le_univ
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul] using hh

theorem code_log_le_capacity {V : Type*} [Fintype V] [DecidableEq V]
    {Q : V → Finset V} {m : ℕ} {C : Finset (V → Fin m → Bool)}
    (hC : IsStorageCode Q C) (hne : C.Nonempty) :
    Real.logb 2 (C.card : ℝ) ≤ capacity Q m := by
  apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hne.card_pos)
  exact_mod_cast code_card_le_max hC

@[simp] theorem maxCodeCard_zero {V : Type*} [Fintype V] [DecidableEq V]
    (Q : V → Finset V) : maxCodeCard Q 0 = 1 := by
  have hlo := maxCodeCard_pos Q 0
  have hhi := maxCodeCard_le Q 0
  simp only [Nat.zero_mul, pow_zero] at hhi
  exact Nat.le_antisymm hhi hlo

@[simp] theorem capacity_zero {V : Type*} [Fintype V] [DecidableEq V]
    (Q : V → Finset V) : capacity Q 0 = 0 := by simp [capacity]

@[simp] theorem deficit_zero {V : Type*} [Fintype V] [DecidableEq V]
    (Q : V → Finset V) : deficit Q 0 = 0 := by simp [deficit]

theorem deficit_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (Q : V → Finset V) (m : ℕ) : 0 ≤ deficit Q m := by
  have hh := logb_le_of_card_le_two_pow (maxCodeCard_pos Q m) (maxCodeCard_le Q m)
  unfold deficit capacity
  push_cast at hh
  linarith

end AdaptiveTransfer.TransferEntry

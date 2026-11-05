import TapeStorageRates.PacketCompilerRecord
import TapeStorageRates.ResourceBounds
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators

/-! # A uniform bit width for complete packet step records -/

namespace TapeStorageRates.PacketCompiler

open Transpose TapeStorageRates.ResourceBounds

set_option autoImplicit false
set_option synthInstance.maxSize 4096

private abbrev RecordTuple (M : TM) (s r : ℕ) :=
  Fin (M.q+1) × Fin (s+r) × (Fin M.k → Fin s) × InputWord s r ×
    (Fin 3 → InputWord s r) × (Fin 3 → Fin M.k → WorkWord M s) ×
    (Fin M.k → WorkWord M s) × Option (Fin s → Bool)

private def recordEquiv (M : TM) (s r : ℕ) : StepRecord M s r ≃ RecordTuple M s r where
  toFun z := (z.boundary.state, z.boundary.inputOffset, z.boundary.workOffset, z.boundary.pending,
    z.inputCells, z.workCells, z.written, z.output)
  invFun := fun ⟨q, i, w, p, x, y, z, o⟩ => ⟨⟨q,i,w,p⟩,x,y,z,o⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- One coefficient works for every packet size and every shorter ragged tail. The record
contains all three read windows, all work writes, and the output packet. -/
theorem stepRecord_bits (M : TM) :
    ∃ b : ℕ, 0 < b ∧ ∀ s r : ℕ, 0 < s → r < s → Fintype.card (StepRecord M s r) ≤ 2^(b*s) := by
  let iw := fun s : ℕ => 3^(2*s)
  let ww := fun s : ℕ => ((M.g+1)^s)^M.k
  have hi : expBound iw := exp_array 3 2
  have hw : expBound ww := exp_pow (by simpa using exp_array (M.g+1) 1) M.k
  have ho : expBound (fun s => 2*2^s) := exp_mul (exp_const 2) (by simpa using exp_array 2 1)
  obtain ⟨b, hb⟩ := exp_mul (exp_const (M.q+1)) (exp_mul (exp_mul (exp_const 2) exp_self)
    (exp_mul (exp_pow exp_self M.k) (exp_mul hi (exp_mul (exp_pow hi 3)
      (exp_mul (exp_pow hw 3) (exp_mul hw ho))))))
  refine ⟨b+1, by omega, fun s r hs hr => ?_⟩
  apply le_trans ?_ ((hb s hs).trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right s (Nat.le_succ b))))
  rw [Fintype.card_congr (recordEquiv M s r)]
  simp only [RecordTuple, WorkWord, InputWord, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_option, Fintype.card_bool, iw, ww, id_eq, Nat.reduceAdd]
  have he : s+r ≤ 2*s := by omega
  have hi' : 3^(s+r) ≤ 3^(2*s) := Nat.pow_le_pow_right (by decide) he
  have ho' : 2^s + 1 ≤ 2*2^s := by
    have h : 0 < 2^s := by positivity
    omega
  gcongr

/-- Fixed machine coefficient, positive even for the trivial state and tape alphabets. -/
noncomputable def recordBits (M : TM) : ℕ := (stepRecord_bits M).choose

theorem recordBits_pos (M : TM) : 0 < recordBits M := (stepRecord_bits M).choose_spec.1

/-- This single injection supplies the finite ordinal alphabet of a packet class. Its bit
budget is independent of both matrix dimension and the actual trajectory. -/
noncomputable def encodeRecord (M : TM) {s r : ℕ} (hs : 0 < s) (hr : r < s) :
    StepRecord M s r ↪ Fin (2^(recordBits M*s)) :=
  (Fintype.equivFin _).toEmbedding.trans
    (Fin.castLEEmb ((stepRecord_bits M).choose_spec.2 s r hs hr))

end TapeStorageRates.PacketCompiler

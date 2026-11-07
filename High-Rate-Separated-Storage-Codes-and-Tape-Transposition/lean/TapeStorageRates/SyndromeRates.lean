import TapeStorageRates.SyndromeFibres
import DirectedRecovery.Hyperfinite
import LeanMachine.FinitePartition

/-! # One syndrome partition, all source subsets and confidence levels -/

namespace TapeStorageRates

open Finset DirectedRecovery MotionDepthCodes
set_option autoImplicit false
noncomputable section

variable {V K A : Type*} [Fintype V] [DecidableEq V] [Field K]

open Classical in
/-- Restricting a syndrome fibre to any source set preserves recovery. -/
theorem matrixSyndrome_subset_fibre_storage (H : Matrix V V K) (e : A → K)
    (he : Function.Injective e) (hd : ∀ v, H v v ≠ 0)
    (S : Finset (V → A)) (z : V → K) :
    IsStorageCode (matrixHelpers H) (S.filter fun x => matrixSyndrome H e x = z) := by
  intro x hx y hy v hhelp
  exact matrixSyndrome_isIndexCode H e he hd x y
    ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) v hhelp

open Classical in
omit [DecidableEq V] in
/-- The exact moment uses the number of syndrome labels attained on the
chosen source set. No alphabet embedding or diagonal hypothesis is needed
for this counting identity. -/
theorem matrixSyndrome_deficit_moment (H : Matrix V V K) (e : A → K)
    (S : Finset (V → A)) {b : ℝ} (hb : 1 < b) (L : ℝ) :
    ∑ x ∈ S, b ^ (L - Real.logb b
      (S.filter fun y => matrixSyndrome H e y = matrixSyndrome H e x).card) =
      ((S.image (matrixSyndrome H e)).card : ℝ) * b ^ L := by
  simpa only [sub_zero, sum_const, nsmul_eq_mul] using
    LeanMachine.FinitePartition.deficit_moment S (matrixSyndrome H e)
      (by linarith) hb.ne' L (fun _ => 0)

open Classical in
/-- The rank bound on attained syndrome labels, expressed in any logarithmic base. -/
theorem matrixSyndrome_image_card_le_rpow [Fintype K]
    (H : Matrix V V K) (e : A → K) (S : Finset (V → A)) {b : ℝ} (hb : 1 < b) :
    ((S.image (matrixSyndrome H e)).card : ℝ) ≤
      b ^ ((H.rank : ℝ) * Real.logb b (Fintype.card K)) := by
  have hq : 0 < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ ((Fintype.card K ^ H.rank : ℕ) : ℝ) :=
      Nat.cast_le.mpr (matrixSyndrome_image_card_le H e S)
    _ = b ^ ((H.rank : ℝ) * Real.logb b (Fintype.card K)) := by
      rw [mul_comm, Real.rpow_mul (by linarith : 0 ≤ b),
        Real.rpow_logb (by linarith) hb.ne' hq, Real.rpow_natCast, Nat.cast_pow]

open Classical in
/-- A fixed matrix and embedding give the stated tail for every nonempty
source subset and every confidence parameter, without choosing a new partition. -/
theorem matrixSyndrome_tail [Fintype K] (H : Matrix V V K) (e : A → K)
    (S : Finset (V → A)) (hS : S.Nonempty) {b : ℝ} (hb : 1 < b) (t : ℝ) :
    ((S.filter fun x => Real.logb b
      (S.filter fun y => matrixSyndrome H e y = matrixSyndrome H e x).card <
      Real.logb b S.card - (H.rank : ℝ) * Real.logb b (Fintype.card K) - t).card : ℝ) /
        S.card ≤ b ^ (-t) :=
  LeanMachine.FinitePartition.tail_of_image_card S hS (matrixSyndrome H e) hb
    (matrixSyndrome_image_card_le_rpow H e S hb) t

/-- The canonical embedding of the binary alphabet in any field. -/
def bitInField (K : Type*) [Field K] (x : Bool) : K := if x then 1 else 0

theorem bitInField_injective : Function.Injective (bitInField K) := by
  intro x y h
  cases x <;> cases y <;> simp_all [bitInField]

/-- A matrix check produces a nonempty binary storage code with the exact
rank charge, on the original coordinates and helper relation. -/
theorem matrix_exists_binary_code_rate [Fintype K] [Nonempty V]
    (H : Matrix V V K) (hd : ∀ v, H v v ≠ 0) :
    ∃ C : Finset (V → Bool), C.Nonempty ∧ IsStorageCode (matrixHelpers H) C ∧
      1 - (H.rank : ℝ) * Real.logb 2 (Fintype.card K) / Fintype.card V ≤
        storageCodeRate C := by
  classical
  obtain ⟨y, hC, hstorage, hcard⟩ :=
    matrixSyndrome_exists_large_fibre H (bitInField K) bitInField_injective hd
  refine ⟨indexFiber (matrixSyndrome H (bitInField K)) y, hC, hstorage, ?_⟩
  have hCpos : 0 < ((indexFiber (matrixSyndrome H (bitInField K)) y).card : ℝ) := by
    exact_mod_cast hC.card_pos
  have hq : 0 < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  have hN : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hreal : (2 : ℝ) ^ Fintype.card V ≤
      (Fintype.card K : ℝ) ^ H.rank *
        (indexFiber (matrixSyndrome H (bitInField K)) y).card := by
    exact_mod_cast hcard
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < 2 ^ Fintype.card V) hreal
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
    Real.logb_mul (pow_pos hq _).ne' hCpos.ne', Real.logb_pow] at hlog
  unfold storageCodeRate
  rw [Fintype.card_bool, Nat.cast_ofNat]
  apply (le_div_iff₀ hN).mpr
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hN.ne']
  linarith

open Classical in
/-- Rate-normalized form of the common-partition tail. The same statement
holds for correlated or adaptively selected source subsets. -/
theorem matrixSyndrome_binary_rate_tail [Fintype K] [Nonempty V]
    (H : Matrix V V K) (S : Finset (V → Bool)) (hS : S.Nonempty) (u : ℝ) :
    ((S.filter fun x => storageCodeRate
      (S.filter fun y => matrixSyndrome H (bitInField K) y = matrixSyndrome H (bitInField K) x) <
      storageCodeRate S - (H.rank : ℝ) * Real.logb 2 (Fintype.card K) / Fintype.card V - u).card : ℝ) /
        S.card ≤ (2 : ℝ) ^ (-u * Fintype.card V) := by
  have h := LeanMachine.FinitePartition.normalized_tail S hS (matrixSyndrome H (bitInField K))
      (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast Fintype.card_pos : 0 < (Fintype.card V : ℝ))
      (matrixSyndrome_image_card_le_rpow H (bitInField K) S (by norm_num)) u
  convert h using 1
  congr 2

end
end TapeStorageRates

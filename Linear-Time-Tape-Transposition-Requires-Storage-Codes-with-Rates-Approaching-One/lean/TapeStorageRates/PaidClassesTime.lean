import TapeStorageRates.PaidClasses

/-! # Uniform batch and time coefficients at a public native deadline -/

namespace TapeStorageRates.PaidClasses

set_option autoImplicit false

/-- Uniformly in the packet size, entry width and remainder, the number
of padded batches is at most this many per packet (with one boundary packet). -/
noncomputable def batchCoefficient (c : ℝ) : ℕ := 2 * ⌈c⌉₊ + 1

/-- The full final halt-detection batch is counted. -/
theorem padded_batches_le {d a s r : ℕ} (ha : 0 < a) (hs : 0 < s) (hr : r < s)
    {c : ℝ} (hc : 0 ≤ c) :
    ⌊c * (((d*d*(a*s+r) : ℕ) : ℝ) + 1)⌋₊ / s + 1 ≤
      batchCoefficient c * (d*d*a + 1) := by
  let L := d*d*(a*s+r)
  let n := d*d*a
  let K := ⌈c⌉₊
  have hb : r ≤ a*s := hr.le.trans (Nat.le_mul_of_pos_left s ha)
  have hsize : L+1 ≤ (2*n+1)*s := by
    dsimp only [L,n]
    nlinarith only [Nat.mul_le_mul_left (d*d) hb,hs]
  have hfloor : ⌊c*((L:ℝ)+1)⌋₊ ≤ K*(L+1) := by
    have h := Nat.floor_le (show 0 ≤ c*((L:ℝ)+1) by positivity)
    have hK : c ≤ (K:ℝ) := Nat.le_ceil _
    exact_mod_cast h.trans (mul_le_mul_of_nonneg_right hK (by positivity))
  have hle : ⌊c*((L:ℝ)+1)⌋₊ ≤ (K*(2*n+1))*s := by
    simpa only [Nat.mul_assoc] using hfloor.trans (Nat.mul_le_mul_left K hsize)
  have hd := Nat.div_le_div_right (c := s) hle
  rw [Nat.mul_div_cancel _ hs] at hd
  change ⌊c*((L:ℝ)+1)⌋₊ / s + 1 ≤ (2*K+1)*(n+1)
  nlinarith only [hd]

/-- Eleven packet ticks per padded batch have a fixed linear time
coefficient, independent of the packet size. -/
theorem padded_time_le {d a s r : ℕ} (ha : 0 < a) (hs : 0 < s) (hr : r < s)
    {c : ℝ} (hc : 0 ≤ c) :
    ((11 * (⌊c * (((d*d*(a*s+r) : ℕ) : ℝ) + 1)⌋₊ / s + 1) : ℕ) : ℝ) ≤
      (11 * batchCoefficient c : ℝ) * ((d*d*a : ℕ) + 1) := by
  let R := ⌊c * (((d*d*(a*s+r) : ℕ) : ℝ) + 1)⌋₊ / s + 1
  change ((11*R : ℕ) : ℝ) ≤ _
  have h : 11*R ≤ 11*batchCoefficient c*(d*d*a+1) := by
    simpa only [R,Nat.mul_assoc] using
      Nat.mul_le_mul_left 11 (padded_batches_le (d := d) ha hs hr hc)
  exact_mod_cast h

end TapeStorageRates.PaidClasses

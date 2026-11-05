import TapeStorageRates.DegreeParameters
import TapeStorageRates.DegreeInversion

/-!
# The binary degree cap at the actual genie depth

Paper 14 bounds the full depth. Trimming both packet port degrees at twice the size of a depth
cone, then expanding each packet to `s` bits, gives the cap below. Its double logarithm has the
power and the single logarithmic factor needed by the inversion.
-/

namespace TapeStorageRates

open Filter Finset DirectedRecovery BoundedStackDepth

set_option autoImplicit false

/-- The degree cap after trimming packet incidence and expanding to `s` binary coordinates. -/
def packetIncidenceCap (k s D : ℕ) : ℕ := 2 * s * ∑ j ∈ range (D + 1), (k + 1) ^ j

private theorem sum_pow_le_two_pow (a t : ℕ) :
    ∑ j ∈ range t, a ^ j ≤ 2 ^ ((a + 1) * t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ha : a ≤ 2 ^ (a + 1) := (Nat.le_succ a).trans (Nat.lt_two_pow_self (n := a + 1)).le
    have hp : a ^ t ≤ 2 ^ ((a + 1) * t) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left ha _
    have h2 : 2 ≤ 2 ^ (a + 1) := by
      simpa using Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ a + 1 by omega)
    rw [sum_range_succ, Nat.mul_succ, pow_add]
    calc
      _ ≤ 2 ^ ((a + 1) * t) + 2 ^ ((a + 1) * t) := Nat.add_le_add ih hp
      _ ≤ _ := by rw [← Nat.mul_two]; exact Nat.mul_le_mul_left _ h2

private theorem degreeLogLog_le_of_double_pow {δ L : ℕ} (h : δ ≤ 2 ^ (2 ^ L)) :
    degreeLogLog δ ≤ (L : ℝ) := by
  by_cases hδ : 1 < δ
  · have hpos : (1 : ℝ) < δ := by exact_mod_cast hδ
    have hh : (δ : ℝ) ≤ (2 : ℝ) ^ (2 ^ L : ℕ) := by exact_mod_cast h
    have h₁ := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hh
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h₁
    have h₂ := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (Real.logb_pos (by norm_num) hpos) h₁
    simpa [degreeLogLog, Real.logb_pow] using h₂
  · have hh : δ = 0 ∨ δ = 1 := by omega
    rcases hh with rfl | rfl <;> simp [degreeLogLog]

/-- An exponential upper bound on the full depth suffices for a linear bound on the double
logarithm of the binary degree cap. -/
theorem degreeLogLog_packetIncidenceCap_le (k s D L : ℕ) (hD : D ≤ 2 ^ L) :
    degreeLogLog (packetIncidenceCap k s D) ≤ ((s + k + L + 5 : ℕ) : ℝ) := by
  have hs : s ≤ 2 ^ s := (Nat.lt_two_pow_self (n := s)).le
  have hcap := mul_le_two_pow (mul_le_two_pow (by decide : 2 ≤ 2 ^ 1) hs) (sum_pow_le_two_pow (k + 1) (D + 1))
  have hsp : 1 + s ≤ 2 ^ s := by simpa [Nat.add_comm] using (Nat.lt_two_pow_self (n := s))
  have hDp := add_le_two_pow hD (by decide : 1 ≤ 2 ^ 0)
  have hk : k + 1 + 1 ≤ 2 ^ (k + 2) := (Nat.lt_two_pow_self (n := k + 2)).le
  have hsum := add_le_two_pow hsp (mul_le_two_pow hk hDp)
  apply degreeLogLog_le_of_double_pow
  apply hcap.trans (Nat.pow_le_pow_right (by decide) ?_)
  exact hsum.trans (Nat.pow_le_pow_right (by decide) (by omega))

/-- For the actual Paper 14 genie with a fixed time coefficient, unit revealed-bit budget and
step-value width at most linear in packet size, the cap has the required double-logarithmic
upper bound. All constants precede the packet-size and code-length limits. -/
theorem genie_packet_cap_degree_bound_at (k b : ℕ) {C : ℝ} (hC : 1 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ s β : ℕ, 1 ≤ s → 1 ≤ β → β ≤ b*s →
      degreeLogLog (packetIncidenceCap k s (genieDepth k β C 1)) ≤
        B * (s : ℝ) ^ (4 * k ^ 2 + 1) * Real.logb 2 ((s : ℝ) + 1) := by
  let a : ℕ := ⌈4 * (b : ℝ) * C⌉₊
  obtain ⟨E, P, hparameters⟩ := paper14_radix_bounds k a
  let V := E * P + a + k + 6
  have hV : 0 < V := by dsimp [V]; omega
  refine ⟨2 * (V : ℝ), by positivity, ?_⟩
  intro s β hs hβ1 hβb
  let x := 4 * (β : ℝ) * C
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hβpos : (0 : ℝ) < β := by exact_mod_cast hβ1
  have hx : 0 < x := by dsimp [x]; positivity
  have hxe : x ≤ (a : ℝ) * s := calc
    _ ≤ 4 * ((b * s : ℕ) : ℝ) * C := by dsimp [x]; gcongr
    _ = (4 * (b : ℝ) * C) * s := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
  obtain ⟨hK, hP⟩ := hparameters s x hs hx hxe
  let m := 4 * k ^ 2
  let U := s ^ (m + 1) * packetLogCeil s
  have hu : 1 ≤ s ^ m * packetLogCeil s := Nat.mul_pos (pow_pos hs _) (packetLogCeil_pos hs)
  have hsU : s ≤ U := by
    dsimp [U]; rw [pow_succ]; nlinarith [Nat.mul_le_mul_left s hu]
  have hU : 1 ≤ U := hs.trans hsU
  have hKp : parK k x⁻¹ ^ parP k x⁻¹ ≤ 2 ^ ((E * s) * (P * s ^ m * packetLogCeil s)) := calc
    _ ≤ (2 ^ (E * s)) ^ parP k x⁻¹ := Nat.pow_le_pow_left hK _
    _ = 2 ^ ((E * s) * parP k x⁻¹) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hP)
  have hceil : ⌈x⌉₊ ≤ 2 ^ (a * s) := (Nat.ceil_le.2 (by exact_mod_cast hxe : x ≤ ((a * s : ℕ) : ℝ))).trans
    (Nat.lt_two_pow_self (n := a * s)).le
  have hdepth : genieDepth k β C 1 ≤ 2 ^ (E * P * U + a * s) := by
    simp only [genieDepth, one_div, div_one]
    have h := mul_le_two_pow hKp hceil
    convert h using 1
    congr 2
    dsimp [U]; rw [pow_succ]; ring
  have hsize : s + k + (E * P * U + a * s) + 5 ≤ V * U := by
    dsimp [V]
    nlinarith [Nat.mul_le_mul_left a hsU, Nat.mul_le_mul_left k hU]
  calc
    _ ≤ ((s + k + (E * P * U + a * s) + 5 : ℕ) : ℝ) := degreeLogLog_packetIncidenceCap_le _ _ _ _ hdepth
    _ ≤ ((V * U : ℕ) : ℝ) := by exact_mod_cast hsize
    _ = ((V : ℝ) * (s : ℝ) ^ (m + 1)) * packetLogCeil s := by dsimp [U]; push_cast; ring
    _ ≤ ((V : ℝ) * (s : ℝ) ^ (m + 1)) * (2 * Real.logb 2 ((s : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (packetLogCeil_le_twice hs) (by positivity)
    _ = _ := by ring

theorem genie_packet_cap_degree_bound (k b : ℕ) {C : ℝ} (hC : 1 ≤ C) {β : ℕ → ℕ}
    (hβ : ∀ᶠ s : ℕ in atTop, 1 ≤ β s ∧ β s ≤ b * s) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ s : ℕ in atTop,
      degreeLogLog (packetIncidenceCap k s (genieDepth k (β s) C 1)) ≤
        B * (s : ℝ) ^ (4 * k ^ 2 + 1) * Real.logb 2 ((s : ℝ) + 1) := by
  obtain ⟨B,hB,h⟩ := genie_packet_cap_degree_bound_at k b hC
  exact ⟨B,hB,(hβ.and (eventually_ge_atTop 1)).mono fun s ⟨hw,hs⟩ => h s _ hs hw.1 hw.2⟩

/-- The full numerical contribution of the genie is discharged. A family at the explicit cap
with rate loss `A/s` supplies the packet hypothesis needed by the all-degree transfer. -/
theorem packetFamilyBounds_of_genieFamilies (k b : ℕ) {C A : ℝ} (hC : 1 ≤ C) (hA : 0 < A)
    {β : ℕ → ℕ} (hβ : ∀ᶠ s : ℕ in atTop, 1 ≤ β s ∧ β s ≤ b * s)
    (hfamily : ∀ᶠ s : ℕ in atTop,
      ∃ F : SeparatedBinaryFamily (packetIncidenceCap k s (genieDepth k (β s) C 1)),
        1 - A / s ≤ liminf (fun i => storageCodeRate (F.code i)) atTop) :
    PacketFamilyBounds k := by
  obtain ⟨B, hB, hdegree⟩ := genie_packet_cap_degree_bound k b hC hβ
  exact ⟨A, B, hA, hB, (hdegree.and hfamily).mono fun s h => ⟨_, h.1, h.2⟩⟩

end TapeStorageRates

import TransposeFollowup.CoveringPolynomialLoss

/-! Real arithmetic for converting the explicit covering profile and the
normalized Haar-ball bounds into a common power envelope. -/
namespace TransposeFollowup
set_option autoImplicit false

theorem covering_profile_power_envelope {h q η c n n₃ V v T F G : ℝ}
    (hlarge : 2 ^ 100 ≤ h) (hq : 0 < q) (hη : 0 < η) (hc : 0 < c)
    (hch : c ≤ h) (hci : c⁻¹ ≤ h) (hn : 0 ≤ n) (hV : 0 ≤ V) (hv : 0 ≤ v)
    (hT : T * (q⁻¹) ^ 2 ≤ h ^ 27499)
    (hF : F * q⁻¹ ≤ h ^ 319) (hG : G * (q⁻¹) ^ 3 ≤ h ^ 29411)
    (htrip : n₃ * q ^ 2 ≤ T * n)
    (hlo : q ≤ F * V * n * v) (hhi : n * q ^ 3 * V * v ≤ G)
    (hvlo : c * η ^ 3 / 512 ≤ v) (hvhi : v ≤ 96 * c * η ^ 3) :
    n₃ ≤ h ^ 30000 * n ∧ 1 ≤ h ^ 30000 * n * V * η ^ 3 ∧
      n * V * η ^ 3 ≤ h ^ 30000 := by
  have hh : 1 ≤ h := (by norm_num : (1 : ℝ) ≤ 2 ^ 100).trans hlarge
  have hh0 : 0 ≤ h := zero_le_one.trans hh
  have h96 : (96 : ℝ) ≤ h := (by norm_num : (96 : ℝ) ≤ 2 ^ 100).trans hlarge
  have h512 : (512 : ℝ) ≤ h := (by norm_num : (512 : ℝ) ≤ 2 ^ 100).trans hlarge
  have hvupper : v ≤ h ^ 2 * η ^ 3 := hvhi.trans (by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (mul_le_mul h96 hch hc.le hh0) (pow_nonneg hη.le 3))
  have hvlower : η ^ 3 ≤ h ^ 2 * v := by
    have hp := mul_le_mul_of_nonneg_left hvlo (show 0 ≤ 512 * c⁻¹ by positivity)
    have he : 512 * c⁻¹ * (c * η ^ 3 / 512) = η ^ 3 := by field_simp
    rw [he] at hp
    exact hp.trans (by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (mul_le_mul h512 hci (inv_nonneg.mpr hc.le) hh0) hv)
  have ht : n₃ ≤ (T * (q⁻¹) ^ 2) * n := by
    have hp := mul_le_mul_of_nonneg_right htrip (sq_nonneg q⁻¹)
    have he : n₃ * q ^ 2 * (q⁻¹) ^ 2 = n₃ := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hq.ne']; simp
    simpa only [he, mul_assoc, mul_comm, mul_left_comm] using hp
  have hl : 1 ≤ (F * q⁻¹) * n * V * v := by
    have hp := mul_le_mul_of_nonneg_right hlo (inv_nonneg.mpr hq.le)
    simpa only [mul_inv_cancel₀ hq.ne', mul_assoc, mul_comm, mul_left_comm] using hp
  have hu : n * V * v ≤ G * (q⁻¹) ^ 3 := by
    have hp := mul_le_mul_of_nonneg_right hhi (pow_nonneg (inv_nonneg.mpr hq.le) 3)
    have he : n * q ^ 3 * V * v * (q⁻¹) ^ 3 = n * V * v := by
      calc
        _ = (n * V * v) * (q * q⁻¹) ^ 3 := by ring
        _ = _ := by rw [mul_inv_cancel₀ hq.ne']; simp
    rwa [he] at hp
  refine ⟨ht.trans ((mul_le_mul_of_nonneg_right hT hn).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hh (by omega)) hn)), ?_, ?_⟩
  · calc
      1 ≤ (F * q⁻¹) * n * V * v := hl
      _ ≤ h ^ 319 * n * V * v := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hF (mul_nonneg (mul_nonneg hn hV) hv)
      _ ≤ h ^ 319 * n * V * (h ^ 2 * η ^ 3) :=
        mul_le_mul_of_nonneg_left hvupper (mul_nonneg (mul_nonneg (pow_nonneg hh0 319) hn) hV)
      _ = h ^ 321 * n * V * η ^ 3 := by ring
      _ ≤ h ^ 30000 * n * V * η ^ 3 := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (show h ^ 321 ≤ h ^ 30000 from pow_le_pow_right₀ hh (by omega))
          (mul_nonneg (mul_nonneg hn hV) (pow_nonneg hη.le 3))
  · calc
      n * V * η ^ 3 ≤ n * V * (h ^ 2 * v) := mul_le_mul_of_nonneg_left hvlower (mul_nonneg hn hV)
      _ = h ^ 2 * (n * V * v) := by ring
      _ ≤ h ^ 2 * h ^ 29411 := mul_le_mul_of_nonneg_left (hu.trans hG) (sq_nonneg h)
      _ = h ^ 29413 := by rw [← pow_add]
      _ ≤ h ^ 30000 := pow_le_pow_right₀ hh (by omega)

end TransposeFollowup

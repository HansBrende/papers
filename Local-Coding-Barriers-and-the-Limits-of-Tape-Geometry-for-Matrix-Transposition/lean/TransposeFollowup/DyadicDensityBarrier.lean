import TransposeFollowup.DyadicSmoothingScale

/-! A quantitative sufficient flatness threshold for the proved smoothed
walk coefficient bound. This is scalar arithmetic; it proves no density
flatness for any actual walk. -/
namespace TransposeFollowup
open Classical
set_option autoImplicit false

theorem exists_dyadic_density_barrier (Nmin : ℕ) {C r : ℝ} (hr : 0 < r) :
    ∃ N₀ J₀ : ℕ, 0 < N₀ ∧ Nmin ≤ N₀ ∧ 0 < J₀ ∧
      ∀ N j ell : ℕ, N₀ ≤ N → J₀ ≤ j → 2 * N * ell ≤ j →
        ∀ D : ℝ, D ^ 2 ≤ (2 : ℝ) ^ j →
          C * (16 : ℝ) ^ ell * D / (2 : ℝ) ^ j < (r ^ ell / 2) ^ 2 := by
  obtain ⟨N₀, J₀, hN₀, hmin, hJ₀, _, herror⟩ :=
    exists_dyadic_smoothing_integer_parameters Nmin
      (by positivity : (0 : ℝ) ≤ 32 * C ^ 2)
      (by positivity : (0 : ℝ) < r ^ 4 / 256)
  refine ⟨N₀, J₀, hN₀, hmin, hJ₀, ?_⟩
  intro N j ell hN hj hell D hDsq
  have hell₀ : 2 * N₀ * ell ≤ j := by
    calc
      _ ≤ 2 * N * ell := by gcongr
      _ ≤ _ := hell
  have he := herror j ell hj hell₀
  let p : ℝ := 2 ^ j
  let s : ℝ := 16 ^ ell
  let t : ℝ := r ^ ell
  have hp : 0 < p := by dsimp [p]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hpowers : (2 : ℝ) ^ j * (1 / 4 : ℝ) ^ j = p⁻¹ := by
    calc
      _ = (1 / 2 : ℝ) ^ j := by rw [← mul_pow]; congr 1; norm_num
      _ = _ := by simp only [p, one_div, inv_pow]
  have hpowers' : (r ^ 4 / 256) ^ ell = t ^ 4 / s ^ 2 := by
    have ht' : (r ^ 4) ^ ell = (r ^ ell) ^ 4 := by
      rw [← pow_mul, Nat.mul_comm 4 ell, pow_mul]
    have hs' : ((16 : ℝ) ^ ell) ^ 2 = (256 : ℝ) ^ ell := by
      rw [← pow_mul, Nat.mul_comm ell 2, pow_mul]
      norm_num
    rw [div_pow, ht', ← hs']
  rw [mul_assoc, hpowers, hpowers'] at he
  have he' : 32 * C ^ 2 / p ≤ t ^ 4 / (s ^ 2 * 2) := by
    simpa only [← div_eq_mul_inv, div_div] using he
  have hupper : 64 * C ^ 2 * s ^ 2 ≤ t ^ 4 * p := by
    have hh := (div_le_div_iff₀ hp (by positivity : (0 : ℝ) < s ^ 2 * 2)).mp he'
    nlinarith only [hh]
  by_contra hnot
  have hb : (t / 2) ^ 2 ≤ C * s * D / p := le_of_not_gt hnot
  have hb' := (le_div_iff₀ hp).mp hb
  have hb'' := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (t / 2) ^ 2 * p) hb' 2
  have hsq : t ^ 4 * p ^ 2 ≤ 16 * C ^ 2 * s ^ 2 * D ^ 2 := by
    nlinarith only [hb'']
  have hDsq' : D ^ 2 ≤ p := hDsq
  have hmono := mul_le_mul_of_nonneg_left hDsq'
    (by positivity : (0 : ℝ) ≤ 16 * C ^ 2 * s ^ 2)
  have hlower : t ^ 4 * p ≤ 16 * C ^ 2 * s ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right hp).mp
    nlinarith only [hsq.trans hmono]
  have hpos : 0 < t ^ 4 * p := by positivity
  have hnonneg : 0 ≤ C ^ 2 * s ^ 2 := by positivity
  nlinarith only [hupper, hlower, hpos, hnonneg]

end TransposeFollowup

import BoundedStackDepth.Machines

/-!
# Bounds for the explicit parameters of Paper 14

At a cut fraction `1/x`, with `x ≤ a s`, the number of digits is at most a constant times
`s^(4k²) ⌈log₂(s+1)⌉`. The radix is at most exponential in `s`. The estimates below are for
the actual natural parameters, including their ceilings.
-/

namespace TapeStorageRates

open BoundedStackDepth

set_option autoImplicit false

/-- An integer upper bound for the logarithmic factor in the packet estimates. -/
noncomputable def packetLogCeil (s : ℕ) : ℕ := ⌈Real.logb 2 ((s : ℝ) + 1)⌉₊

private theorem succ_le_pow_two (s : ℕ) : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self

private theorem one_le_packet_log {s : ℕ} (hs : 1 ≤ s) : 1 ≤ Real.logb 2 ((s : ℝ) + 1) := by
  have h : (2 : ℝ) ≤ (s : ℝ) + 1 := by exact_mod_cast (by omega : 2 ≤ s + 1)
  simpa using Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by norm_num) h

theorem packetLogCeil_pos {s : ℕ} (hs : 1 ≤ s) : 0 < packetLogCeil s :=
  Nat.ceil_pos.2 (zero_lt_one.trans_le (one_le_packet_log hs))

theorem packetLogCeil_le (s : ℕ) : packetLogCeil s ≤ s := by
  apply Nat.ceil_le.2
  apply (Real.logb_le_iff_le_rpow (by norm_num) (by positivity)).2
  rw [Real.rpow_natCast]
  exact_mod_cast succ_le_pow_two s

theorem packetLogCeil_le_twice {s : ℕ} (hs : 1 ≤ s) :
    (packetLogCeil s : ℝ) ≤ 2 * Real.logb 2 ((s : ℝ) + 1) := by
  have h := one_le_packet_log hs
  have ht := Nat.ceil_lt_add_one (zero_le_one.trans h)
  unfold packetLogCeil
  linarith

private theorem ceil_grid_le (z a s : ℕ) {x : ℝ} (hs : 1 ≤ s) (hx : x ≤ (a : ℝ) * s) :
    ⌈(z : ℝ) / (x⁻¹ / 4)⌉₊ + 1 ≤ (4 * z * a + 1) * s := by
  have h : ⌈(z : ℝ) / (x⁻¹ / 4)⌉₊ ≤ 4 * z * a * s := by
    apply Nat.ceil_le.2
    rw [div_div_eq_mul_div, div_inv_eq_mul]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg z : (0 : ℝ) ≤ z) (sub_nonneg.2 hx)]
  rw [Nat.add_mul, one_mul]
  exact Nat.add_le_add h hs

private theorem log_grid_le (z a s : ℕ) {x : ℝ} (hs : 1 ≤ s) (hx : x ≤ (a : ℝ) * s) :
    Real.log (max 1 ((z : ℝ) * x)) ≤ ((z * a + 2 : ℕ) : ℝ) * packetLogCeil s := by
  have hz : (0 : ℝ) ≤ z := Nat.cast_nonneg _
  have hza : (0 : ℝ) ≤ (z * a : ℕ) := Nat.cast_nonneg _
  have harg : max 1 ((z : ℝ) * x) ≤ ((z * a : ℕ) + 1 : ℝ) * ((s : ℝ) + 1) := by
    apply max_le
    · nlinarith [mul_nonneg hza (Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
    · push_cast
      nlinarith [mul_nonneg hz (sub_nonneg.2 hx), Nat.cast_nonneg s (α := ℝ)]
  have hlog : Real.log ((s : ℝ) + 1) ≤ Real.logb 2 ((s : ℝ) + 1) := by
    have hc : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hslog : 0 ≤ Real.log ((s : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg s (α := ℝ)])
    rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num))]
    nlinarith [mul_nonneg hslog (sub_nonneg.2 hc)]
  have hr := Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) harg
  rw [Real.log_mul (by positivity) (by positivity)] at hr
  have ht : (1 : ℝ) ≤ packetLogCeil s := by exact_mod_cast packetLogCeil_pos hs
  have hceil : Real.logb 2 ((s : ℝ) + 1) ≤ packetLogCeil s := Nat.le_ceil _
  have hzlog := Real.log_le_self (show 0 ≤ ((z * a : ℕ) + 1 : ℝ) by positivity)
  push_cast at *
  nlinarith [mul_nonneg (mul_nonneg hz (Nat.cast_nonneg a : (0 : ℝ) ≤ a)) (sub_nonneg.2 ht)]

/-- Paper 14's grid width and digit count, at a cut fraction reciprocal to a quantity of at most
linear growth. The constants are uniform in `s` and `x`. -/
theorem paper14_grid_bounds (k a : ℕ) : ∃ H P : ℕ, ∀ (s : ℕ) (x : ℝ), 1 ≤ s → 0 < x →
    x ≤ (a : ℝ) * s →
    parH k x⁻¹ ≤ H * s ∧ parP k x⁻¹ ≤ P * s ^ (4 * k ^ 2) * packetLogCeil s := by
  let n := k * 2
  let m := n * n
  let H := 4 * (14 * n + 80 * n ^ 2) * a + 1
  let Q := 4 * (2 * n ^ 2) * a + 1
  let J := (8 * n ^ 2 * a + 2) * Q ^ m
  let P := 1 + (n + n) * (J * n + 1)
  have hm : m = 4 * k ^ 2 := by dsimp [m, n]; ring
  refine ⟨H, P, ?_⟩
  intro s x hs _ hx
  have hH : parH k x⁻¹ ≤ H * s := by
    have h := ceil_grid_le (14 * n + 80 * n ^ 2) a s hs hx
    push_cast at h
    exact h
  have hQ : parQ k x⁻¹ ≤ Q * s := by
    have h := ceil_grid_le (2 * n ^ 2) a s hs hx
    push_cast at h
    exact h
  let u := s ^ m * packetLogCeil s
  have hu : 1 ≤ u := Nat.mul_pos (pow_pos hs _) (packetLogCeil_pos hs)
  have hJ : parJ k x⁻¹ ≤ J * u := by
    unfold parJ
    apply Nat.ceil_le.2
    simp only [div_inv_eq_mul]
    change Real.log (max 1 (8 * (n : ℝ) ^ 2 * x)) * (parQ k x⁻¹ : ℝ) ^ m ≤ _
    have hl := log_grid_le (8 * n ^ 2) a s hs hx
    push_cast at hl
    have hq : (parQ k x⁻¹ : ℝ) ^ m ≤ ((Q * s : ℕ) : ℝ) ^ m := by
      exact_mod_cast Nat.pow_le_pow_left hQ m
    calc
      _ ≤ (((8 : ℝ) * (n : ℝ) ^ 2 * a + 2) * packetLogCeil s) * ((Q * s : ℕ) : ℝ) ^ m := by
        gcongr
      _ = _ := by dsimp [J, u]; push_cast; rw [mul_pow]; ring
  refine ⟨hH, ?_⟩
  change 1 + (n + n) * (parJ k x⁻¹ * n + 1) ≤ _
  calc
    _ ≤ u + (n + n) * ((J * u) * n + u) := by gcongr
    _ = P * s ^ (4 * k ^ 2) * packetLogCeil s := by
      dsimp [P, u]; rw [← hm]; ring

/-- Two binary-exponential majorants multiply by adding their exponents. -/
theorem mul_le_two_pow {a b U V : ℕ} (ha : a ≤ 2 ^ U) (hb : b ≤ 2 ^ V) :
    a * b ≤ 2 ^ (U + V) := by rw [pow_add]; exact Nat.mul_le_mul ha hb

/-- A sum of two binary-exponentially bounded integers costs at most one further exponent bit. -/
theorem add_le_two_pow {a b U V : ℕ} (ha : a ≤ 2 ^ U) (hb : b ≤ 2 ^ V) :
    a + b ≤ 2 ^ (U + V + 1) := by
  have hA : a ≤ 2 ^ (U + V) := ha.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hB : b ≤ 2 ^ (U + V) := hb.trans (Nat.pow_le_pow_right (by decide) (by omega))
  rw [pow_succ]; omega

/-- At fixed tape count and width coefficient, Paper 14's radix is bounded by `2^(E s)`, and its
digit count retains the exact exponent `4k²` from the grid. -/
theorem paper14_radix_bounds (k a : ℕ) : ∃ E P : ℕ, ∀ (s : ℕ) (x : ℝ), 1 ≤ s → 0 < x →
    x ≤ (a : ℝ) * s →
    parK k x⁻¹ ≤ 2 ^ (E * s) ∧ parP k x⁻¹ ≤ P * s ^ (4 * k ^ 2) * packetLogCeil s := by
  obtain ⟨H, P, hgrid⟩ := paper14_grid_bounds k a
  let n := k * 2
  let m := 4 * k ^ 2
  let E := 4 + (5 + P + m + 1 + n + (140 + H + n * 2) + 1) + a + 1 + 1 + 1
  refine ⟨E, P, ?_⟩
  intro s x hs hx ha
  obtain ⟨hH, hP⟩ := hgrid s x hs hx ha
  have hnat : ∀ t : ℕ, t ≤ 2 ^ (t * s) := fun t =>
    (Nat.le_succ t).trans ((succ_le_pow_two t).trans <|
      Nat.pow_le_pow_right (by decide) (by nlinarith))
  have hsp : s ≤ 2 ^ s := (Nat.le_succ s).trans (succ_le_pow_two s)
  have hsPow : s ^ m ≤ 2 ^ (m * s) := by
    rw [mul_comm m s, pow_mul 2 s m]; exact Nat.pow_le_pow_left hsp _
  have ht : packetLogCeil s ≤ 2 ^ s := (packetLogCeil_le s).trans hsp
  have hPe : parP k x⁻¹ ≤ 2 ^ (P * s + m * s + s) :=
    hP.trans (mul_le_two_pow (mul_le_two_pow (hnat P) hsPow) ht)
  let z := 5 * parP k x⁻¹ * n + 140 * 2 ^ parH k x⁻¹ * n ^ 2
  have hz1 := mul_le_two_pow (mul_le_two_pow (hnat 5) hPe) (hnat n)
  have hn2 : n ^ 2 ≤ 2 ^ (n * s + n * s) := by simpa [sq] using mul_le_two_pow (hnat n) (hnat n)
  have hz2 := mul_le_two_pow
    (mul_le_two_pow (hnat 140) (Nat.pow_le_pow_right (n := 2) (by decide) hH)) hn2
  have hz := add_le_two_pow hz1 hz2
  have hK : parK k x⁻¹ ≤ (4 * z * a + 1) * s := by
    have h := ceil_grid_le z a s hs ha
    dsimp [z] at h
    push_cast at h
    exact h
  refine ⟨hK.trans ?_, hP⟩
  have hbig := mul_le_two_pow
    (add_le_two_pow (mul_le_two_pow (mul_le_two_pow (hnat 4) hz) (hnat a)) (hnat 1)) hsp
  apply hbig.trans (Nat.pow_le_pow_right (by decide) ?_)
  dsimp [E]
  nlinarith

end TapeStorageRates

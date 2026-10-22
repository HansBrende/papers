import TransposeFollowup.RationalOpcodeSize

/-! Clear the fixed coefficient denominators once. Evaluation on a fraction
then needs integer linear forms, without a rational-normalization step.
Zero output denominators retain Lean's totalized division convention. -/

namespace TransposeFollowup

set_option autoImplicit false

theorem rat_num_cast_eq (q : ℚ) : (q.num : ℚ) = q * q.den := by
  exact (div_eq_iff (by exact_mod_cast q.den_ne_zero)).mp q.num_div_den

namespace RationalMobius

variable (F : RationalMobius)

def integralScale : ℕ := F.a.den * F.b.den * F.c.den * F.d.den

def integralA : ℤ := F.a.num * F.b.den * F.c.den * F.d.den
def integralB : ℤ := F.a.den * F.b.num * F.c.den * F.d.den
def integralC : ℤ := F.a.den * F.b.den * F.c.num * F.d.den
def integralD : ℤ := F.a.den * F.b.den * F.c.den * F.d.num

theorem integralScale_pos : 0 < F.integralScale := by
  dsimp [integralScale]
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos F.a.den_pos F.b.den_pos) F.c.den_pos) F.d.den_pos

theorem integral_coefficients_cast :
    (F.integralA : ℚ) = F.integralScale * F.a ∧
    (F.integralB : ℚ) = F.integralScale * F.b ∧
    (F.integralC : ℚ) = F.integralScale * F.c ∧
    (F.integralD : ℚ) = F.integralScale * F.d := by
  dsimp [integralA, integralB, integralC, integralD, integralScale]
  push_cast
  rw [rat_num_cast_eq F.a, rat_num_cast_eq F.b, rat_num_cast_eq F.c, rat_num_cast_eq F.d]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

def integerNumerator (p q : ℤ) : ℤ := F.integralA * p + F.integralB * q
def integerDenominator (p q : ℤ) : ℤ := F.integralC * p + F.integralD * q

theorem evalQ_fraction_eq (p q : ℤ) (hq : q ≠ 0) :
    F.evalQ ((p : ℚ) / q) = (F.integerNumerator p q : ℚ) / F.integerDenominator p q := by
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hL : (F.integralScale : ℚ) ≠ 0 := by exact_mod_cast F.integralScale_pos.ne'
  obtain ⟨ha, hb, hc, hd⟩ := F.integral_coefficients_cast
  have hn : F.a * ((p : ℚ) / q) + F.b = (F.a * p + F.b * q) / q := by
    field_simp
  have hden : F.c * ((p : ℚ) / q) + F.d = (F.c * p + F.d * q) / q := by
    field_simp
  simp only [evalQ, hn, hden, integerNumerator, integerDenominator, Int.cast_add, Int.cast_mul,
    ha, hb, hc, hd]
  rw [div_div_div_cancel_right₀ hqQ]
  rw [show (F.integralScale : ℚ) * F.a * p + F.integralScale * F.b * q =
      F.integralScale * (F.a * p + F.b * q) by ring]
  rw [show (F.integralScale : ℚ) * F.c * p + F.integralScale * F.d * q =
      F.integralScale * (F.c * p + F.d * q) by ring]
  rw [mul_div_mul_left _ _ hL]

theorem integerNumerator_bound {p q : ℤ} {H : ℕ}
    (hp : p.natAbs ≤ H) (hq : q.natAbs ≤ H) :
    (F.integerNumerator p q).natAbs ≤ (F.integralA.natAbs + F.integralB.natAbs) * H := by
  have h := Int.natAbs_add_le (F.integralA * p) (F.integralB * q)
  simp only [Int.natAbs_mul] at h
  dsimp [integerNumerator]
  calc
    _ ≤ F.integralA.natAbs * p.natAbs + F.integralB.natAbs * q.natAbs := h
    _ ≤ F.integralA.natAbs * H + F.integralB.natAbs * H :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hp) (Nat.mul_le_mul_left _ hq)
    _ = _ := by ring

theorem integerDenominator_bound {p q : ℤ} {H : ℕ}
    (hp : p.natAbs ≤ H) (hq : q.natAbs ≤ H) :
    (F.integerDenominator p q).natAbs ≤ (F.integralC.natAbs + F.integralD.natAbs) * H := by
  have h := Int.natAbs_add_le (F.integralC * p) (F.integralD * q)
  simp only [Int.natAbs_mul] at h
  dsimp [integerDenominator]
  calc
    _ ≤ F.integralC.natAbs * p.natAbs + F.integralD.natAbs * q.natAbs := h
    _ ≤ F.integralC.natAbs * H + F.integralD.natAbs * H :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hp) (Nat.mul_le_mul_left _ hq)
    _ = _ := by ring

theorem evalQ_grid_eq {n : ℕ} (hn : 0 < n) (i : ℕ) :
    F.evalQ ((i : ℚ) / n) =
      (F.integerNumerator i n : ℚ) / F.integerDenominator i n := by
  simpa only [Int.cast_natCast] using F.evalQ_fraction_eq i n (by exact_mod_cast hn.ne')

theorem integer_grid_bounds {n i : ℕ} (hi : i ≤ n) :
    (F.integerNumerator i n).natAbs ≤ (F.integralA.natAbs + F.integralB.natAbs) * n ∧
    (F.integerDenominator i n).natAbs ≤ (F.integralC.natAbs + F.integralD.natAbs) * n :=
  ⟨F.integerNumerator_bound hi le_rfl, F.integerDenominator_bound hi le_rfl⟩

theorem denomQ_pos {x : ℚ} (hx : x ∈ Set.Icc F.lo F.hi) : 0 < F.c * x + F.d := by
  have h := F.denom_pos (x := (x : ℝ))
    ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩
  dsimp [denom] at h
  exact_mod_cast h

theorem integerDenominator_pos (p q : ℤ) (hq : 0 < q)
    (hx : (p : ℚ) / q ∈ Set.Icc F.lo F.hi) : 0 < F.integerDenominator p q := by
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hq0 := hqQ.ne'
  have hL : (0 : ℚ) < F.integralScale := by exact_mod_cast F.integralScale_pos
  obtain ⟨_, _, hc, hd⟩ := F.integral_coefficients_cast
  have he : (F.integerDenominator p q : ℚ) =
      F.integralScale * (F.c * ((p : ℚ) / q) + F.d) * q := by
    simp only [integerDenominator, Int.cast_add, Int.cast_mul, hc, hd]
    field_simp
  have hp := mul_pos (mul_pos hL (F.denomQ_pos hx)) hqQ
  rw [← he] at hp
  exact_mod_cast hp

end RationalMobius
end TransposeFollowup

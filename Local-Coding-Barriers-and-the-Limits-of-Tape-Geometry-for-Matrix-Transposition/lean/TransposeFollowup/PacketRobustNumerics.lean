import TransposeFollowup.DistanceNumerics

/-! Integer-radius consequences of an abstract robust packet budget. The
budget is an internal numerical interface; applications must supply it from
an actual code theorem. Natural logarithms are used in the explicit error. -/

namespace TransposeFollowup

set_option autoImplicit false

/-- Reuse the half-log power budget at squared base. -/
theorem quarter_log_power_budget (D d : ℕ) (hD : 2 ≤ D) (hd : 0 < d) :
    (Nat.log D d / 4 + 1) * D ^ (2 * (Nat.log D d / 4)) ≤ d := by
  have h := half_log_power_budget (D ^ 2) d (by nlinarith) hd
  simpa only [Nat.log_pow_left, Nat.div_div_eq_div_mul, Nat.reduceMul, ← pow_mul] using h

/-- The corresponding real-log comparison, also inherited from squared base. -/
theorem log_le_four_quarter_log (D d : ℕ) (hD : 2 ≤ D) (hd : 0 < d) :
    Real.log (d : ℝ) ≤
      4 * ((Nat.log D d / 4 : ℕ) + 2 : ℝ) * Real.log (D : ℝ) := by
  have h := log_le_twice_half_log (D ^ 2) d (by nlinarith) hd
  simp only [Nat.log_pow_left, Nat.div_div_eq_div_mul, Nat.reduceMul,
    Nat.cast_pow, Real.log_pow] at h
  convert h using 1; ring

/-- Both the linear and quadratic growth terms fit into the chosen radius. -/
theorem quarter_log_budgets (D d : ℕ) (hD : 2 ≤ D) (hd : 0 < d) :
    let k := Nat.log D d / 4
    k + 1 ≤ d ∧ (k + 1) * D ^ k ≤ d ∧ (k + 1) * D ^ (2*k) ≤ d := by
  let k := Nat.log D d / 4
  have h2 := quarter_log_power_budget D d hD hd
  change (k + 1) * D ^ (2*k) ≤ d at h2
  have hp : D ^ k ≤ D ^ (2*k) := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : (k + 1) * D ^ k ≤ d := (Nat.mul_le_mul_left _ hp).trans h2
  have h0 : k + 1 ≤ d := by
    calc
      _ ≤ (k + 1) * D ^ k := Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
      _ ≤ d := h1
  exact ⟨h0, h1, h2⟩

/-- A quarter-log scaled deficit implies an explicit logarithmic error. -/
theorem lower_bound_of_quarter_log_scaled (D d : ℕ) (hD : 2 ≤ D) (hd : 2 ≤ d)
    (P B C : ℝ) (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hs : ((Nat.log D d / 4 : ℕ) + 2 : ℝ) * (P - B) ≤ C * P) :
    B ≥ P - 4 * C * Real.log (D : ℝ) * P / Real.log (d : ℝ) := by
  let k := Nat.log D d / 4
  have hk : 0 < (k : ℝ) + 2 := by positivity
  have hln : 0 < Real.log (d : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < d by omega))
  have hlog := log_le_four_quarter_log D d hD (by omega)
  change Real.log (d : ℝ) ≤ 4 * ((k : ℝ) + 2) * Real.log (D : ℝ) at hlog
  have hratio : C / ((k : ℝ) + 2) ≤
      4 * C * Real.log (D : ℝ) / Real.log (d : ℝ) := by
    apply (div_le_div_iff₀ hk hln).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlog hC]
  have hgap : P - B ≤ C * P / ((k : ℝ) + 2) := by
    apply (le_div_iff₀ hk).mpr
    change ((k : ℝ) + 2) * (P - B) ≤ C * P at hs
    nlinarith
  have hbound : P - B ≤ 4 * C * Real.log (D : ℝ) * P / Real.log (d : ℝ) := by
    calc
      _ ≤ C * P / ((k : ℝ) + 2) := hgap
      _ = P * (C / ((k : ℝ) + 2)) := by ring
      _ ≤ P * (4 * C * Real.log (D : ℝ) / Real.log (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hratio hP
      _ = _ := by ring
  linarith

/-- Internal numerical form of the robust packet budget at the selected
integer radius. No lower bound on the expected length `B` is needed. -/
theorem robust_packet_scaled_bound (d b c e D : ℕ) (A B L : ℝ)
    (hD : 2 ≤ D) (hd : 0 < d) (hA : 0 ≤ A)
    (hL : L ≤ A * (d * b : ℕ))
    (hbudget : ∀ k : ℕ,
      ((k : ℝ) + 2) * ((d * d * b : ℕ) - B) ≤ (d * d * b : ℕ) +
        ((k : ℝ) + 1) * (2 * c * e * d * b * D^k : ℕ) +
        ((k : ℝ) + 1) * (1 + 64 * c^2 * e^2 * D^(2*k) : ℕ) * L) :
    ((Nat.log D d / 4 : ℕ) + 2 : ℝ) * ((d * d * b : ℕ) - B) ≤
      (1 + 2 * (c : ℝ) * e + A + 64 * (c : ℝ)^2 * e^2 * A) * (d * d * b : ℕ) := by
  let k := Nat.log D d / 4
  obtain ⟨h0, h1, h2⟩ := quarter_log_budgets D d hD hd
  change k + 1 ≤ d at h0
  change (k + 1) * D^k ≤ d at h1
  change (k + 1) * D^(2*k) ≤ d at h2
  have hnearNat : (k + 1) * (2*c*e*d*b*D^k) ≤ 2*c*e*(d*d*b) := by
    calc
      _ = (2*c*e*d*b) * ((k+1)*D^k) := by ring
      _ ≤ (2*c*e*d*b)*d := Nat.mul_le_mul_left _ h1
      _ = _ := by ring
  have hnear : ((k : ℝ)+1) * (2*c*e*d*b*D^k : ℕ) ≤
      2*(c : ℝ)*e*(d*d*b : ℕ) := by exact_mod_cast hnearNat
  have hcoefNat : (k+1)*(1+64*c^2*e^2*D^(2*k))*(d*b) ≤
      (1+64*c^2*e^2)*(d*d*b) := by
    calc
      _ = (d*b)*((k+1) + 64*c^2*e^2*((k+1)*D^(2*k))) := by ring
      _ ≤ (d*b)*(d+64*c^2*e^2*d) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add h0 (Nat.mul_le_mul_left _ h2))
      _ = _ := by ring
  have hdeficit : ((k : ℝ)+1) * (1+64*c^2*e^2*D^(2*k) : ℕ) * L ≤
      (A+64*(c : ℝ)^2*e^2*A)*(d*d*b : ℕ) := by
    calc
      _ = ((k+1)*(1+64*c^2*e^2*D^(2*k)) : ℕ) * L := by push_cast; ring
      _ ≤ ((k+1)*(1+64*c^2*e^2*D^(2*k)) : ℕ) * (A*(d*b : ℕ)) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
      _ = A*((k+1)*(1+64*c^2*e^2*D^(2*k))*(d*b) : ℕ) := by push_cast; ring
      _ ≤ A*((1+64*c^2*e^2)*(d*d*b) : ℕ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcoefNat) hA
      _ = _ := by push_cast; ring
  calc
    _ ≤ _ := hbudget k
    _ ≤ (d*d*b : ℕ) + 2*(c : ℝ)*e*(d*d*b : ℕ) +
        (A+64*(c : ℝ)^2*e^2*A)*(d*d*b : ℕ) :=
      add_le_add (add_le_add le_rfl hnear) hdeficit
    _ = _ := by ring

/-- Explicit finite robust bounded-degree numerical consequence. With fixed
`c,e,A,D` and a deficit at most `A*d*b`, the loss is `O(P/log d)` uniformly in
entry width. The abstract budget must be supplied by an actual code theorem. -/
theorem robust_packet_lower_bound (d b c e D : ℕ) (A B L : ℝ)
    (hD : 2 ≤ D) (hd : 2 ≤ d) (hA : 0 ≤ A)
    (hL : L ≤ A * (d * b : ℕ))
    (hbudget : ∀ k : ℕ,
      ((k : ℝ) + 2) * ((d * d * b : ℕ) - B) ≤ (d * d * b : ℕ) +
        ((k : ℝ) + 1) * (2 * c * e * d * b * D^k : ℕ) +
        ((k : ℝ) + 1) * (1 + 64 * c^2 * e^2 * D^(2*k) : ℕ) * L) :
    B ≥ (d*d*b : ℕ) -
      4 * (1 + 2*(c : ℝ)*e + A + 64*(c : ℝ)^2*e^2*A) *
        Real.log (D : ℝ) * (d*d*b : ℕ) / Real.log (d : ℝ) := by
  apply lower_bound_of_quarter_log_scaled D d hD hd _ B _ (by positivity) (by positivity)
  exact robust_packet_scaled_bound d b c e D A B L hD (by omega) hA hL hbudget

end TransposeFollowup

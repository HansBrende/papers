import SourceCovers.SerialPayment

set_option autoImplicit false

/-! Exact payment inside a bank window. Interior points of retained
windows survive every original outer-lower payment as well as the phase. -/

namespace SourceCovers.SerialGeometry.Parameters

open Classical Finset BoundedNesting
noncomputable section

variable (P : Parameters)

theorem bank_window_bounds (c : Fin 2) (j : Fin P.bankCount) {a : ℕ} (ha : a < P.width) :
    P.bankBase c ≤ P.bankBase c + j.val * P.width + a ∧
      P.bankBase c + j.val * P.width + a < P.bankBase c + P.length := by
  have hj := Nat.mul_le_mul_right P.width (show j.val + 1 ≤ P.bankCount by have := j.isLt; omega)
  change (j.val + 1) * P.width ≤ P.length at hj
  constructor
  · omega
  · nlinarith

theorem bank_range_copy_unique {c c' : Fin 2} {u : ℕ}
    (hc : P.bankBase c ≤ u ∧ u < P.bankBase c + P.length)
    (hc' : P.bankBase c' ≤ u ∧ u < P.bankBase c' + P.length) : c = c' := by
  fin_cases c <;> fin_cases c'
  · rfl
  · norm_num [bankBase] at hc hc'
    omega
  · norm_num [bankBase] at hc hc'
    omega
  · rfl

theorem bank_lower_range (c : Fin 2) (j : Fin P.bankCount) {u : ℕ}
    (hl : P.bankBase c + j.val * P.width ≤ u)
    (hu : u < P.bankBase c + (j.val + 1) * P.width) :
    P.bankBase c ≤ u ∧ u < P.bankBase c + P.length := by
  have hj := Nat.mul_le_mul_right P.width (show j.val + 1 ≤ P.bankCount by have := j.isLt; omega)
  change (j.val + 1) * P.width ≤ P.length at hj
  omega

/-- No outer boundary lies strictly inside a window. The only payment
there is the actual lower-endpoint interval of its own deleted family. -/
theorem bank_window_paid_iff (c : Fin 2) (j : Fin P.bankCount) {a : ℕ}
    (ha : 0 < a) (hah : a < P.width) :
    P.bankBase c + j.val * P.width + a ∈ P.payment ↔
      0 < j.val ∧ j.val % P.m = 0 := by
  have hb := P.bank_window_bounds c j hah
  have hconst : P.bankBase c + j.val * P.width + a ≠ 0 ∧
      P.bankBase c + j.val * P.width + a ≠ 2 * P.length ∧
      P.bankBase c + j.val * P.width + a ≠ 5 * P.length ∧
      P.bankBase c + j.val * P.width + a ≠ 7 * P.length := by
    fin_cases c <;> norm_num [bankBase] at hb ⊢ <;> omega
  constructor
  · intro hp
    rw [P.mem_payment] at hp
    rcases hp with (⟨c', i, he⟩ | he) | ⟨c', i, hi, hm, hl, hu⟩
    · have hb' : P.bankBase c' ≤ P.bankBase c + j.val * P.width + a ∧
          P.bankBase c + j.val * P.width + a < P.bankBase c' + P.length := by
        rw [he]
        simpa only [Nat.add_zero] using P.bank_window_bounds c' i P.width_pos
      have hc := P.bank_range_copy_unique hb hb'
      subst c'
      have he' : j.val * P.width + a = i.val * P.width := by omega
      have hr := congrArg (fun v : ℕ => v % P.width) he'
      simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt hah] at hr
      omega
    · omega
    · have hc := P.bank_range_copy_unique hb (P.bank_lower_range c' i hl hu)
      subst c'
      have hdj : (j.val * P.width + a) / P.width = j.val :=
        Nat.div_eq_of_lt_le (by omega) (by nlinarith)
      have hdi : (j.val * P.width + a) / P.width = i.val :=
        Nat.div_eq_of_lt_le (by omega) (by omega)
      have hij : i = j := Fin.ext (hdi.symm.trans hdj)
      subst i
      exact ⟨hi, hm⟩
  · rintro ⟨hj, hm⟩
    apply (P.mem_payment _).mpr
    right
    exact ⟨c, j, hj, hm, by omega, by nlinarith⟩

theorem bank_window_unpaid (c : Fin 2) (j : Fin P.bankCount) {a : ℕ}
    (ha : 0 < a) (hah : a < P.width) (hj : j.val = 0 ∨ j.val % P.m ≠ 0) :
    P.bankBase c + j.val * P.width + a ∉ P.payment := by
  intro hp
  have hh := (P.bank_window_paid_iff c j ha hah).mp hp
  rcases hj with hj | hj
  · omega
  · exact hj hh.2

end
end SourceCovers.SerialGeometry.Parameters

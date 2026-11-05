import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Finite alphabets encodable in linearly many bits -/

namespace TapeStorageRates.ResourceBounds

def expBound (f : ℕ → ℕ) : Prop :=
  ∃ a : ℕ, ∀ s, 0<s → f s ≤ 2^(a*s)

theorem exp_const (n : ℕ) : expBound (fun _ => n) := by
  refine ⟨n, fun s hs => (show n < 2^n from Nat.lt_two_pow_self).le.trans ?_⟩
  exact Nat.pow_le_pow_right (by decide) (by nlinarith)

theorem exp_self : expBound id := by
  refine ⟨1, fun s _ => ?_⟩
  simpa using (show s < 2^s from Nat.lt_two_pow_self).le

theorem exp_mul {f g : ℕ → ℕ} (hf : expBound f) (hg : expBound g) :
    expBound (fun s => f s*g s) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  refine ⟨a+b, fun s hs => ?_⟩
  rw [add_mul, pow_add]
  exact Nat.mul_le_mul (ha s hs) (hb s hs)

theorem exp_pow {f : ℕ → ℕ} (hf : expBound f) (n : ℕ) :
    expBound (fun s => f s ^ n) := by
  obtain ⟨a,ha⟩ := hf
  refine ⟨a*n, fun s hs => ?_⟩
  rw [show a*n*s = (a*s)*n by ring, pow_mul]
  exact Nat.pow_le_pow_left (ha s hs) n

theorem exp_array (n a : ℕ) : expBound (fun s => n ^ (a*s)) := by
  refine ⟨n*a, fun s _ => ?_⟩
  rw [Nat.mul_assoc, pow_mul]
  exact Nat.pow_le_pow_left (show n < 2^n from Nat.lt_two_pow_self).le _

theorem exp_mono {f g : ℕ → ℕ} (hg : expBound g)
    (h : ∀ s, 0<s → f s ≤ g s) : expBound f := by
  obtain ⟨k,hk⟩ := hg
  exact ⟨k, fun s hs => (h s hs).trans (hk s hs)⟩

end TapeStorageRates.ResourceBounds

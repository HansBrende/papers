import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.Tactic

/-! Nontrivial powers have length at least the absolute exponent, using
the native cyclic reduction formula for powers of a reduced word. -/
namespace TransposeFollowup.FreeWordFamily
open Classical FreeGroup
set_option autoImplicit false

variable {α : Type*} [DecidableEq α]

theorem exponent_le_norm_pow {x : FreeGroup α} (hx : x ≠ 1) (n : ℕ) :
    n ≤ FreeGroup.norm (x ^ n) := by
  have hc : 1 ≤ (reduceCyclically x.toWord).length := by
    by_contra hn
    have hz : reduceCyclically x.toWord = [] := List.length_eq_zero_iff.mp (by omega)
    have he := congrArg FreeGroup.mk (reduceCyclically.conj_conjugator_reduceCyclically x.toWord)
    simp only [hz, List.append_nil, ← mul_mk, ← inv_mk, mul_inv_cancel, mk_toWord] at he
    exact hx he.symm
  by_cases hn : n = 0
  · simp [hn]
  · have he : FreeGroup.norm (x ^ n) = (reduceCyclically.conjugator x.toWord).length +
        n * (reduceCyclically x.toWord).length + (reduceCyclically.conjugator x.toWord).length := by
      simp [FreeGroup.norm, toWord_pow, reduceCyclically.reduce_flatten_replicate,
        isReduced_toWord, hn, Nat.add_assoc]
    rw [he]
    nlinarith

theorem exponent_le_norm_zpow {x : FreeGroup α} (hx : x ≠ 1) (n : ℤ) :
    n.natAbs ≤ FreeGroup.norm (x ^ n) := by
  cases n with
  | ofNat n => simpa using exponent_le_norm_pow hx n
  | negSucc n => simpa using exponent_le_norm_pow hx (n + 1)

end TransposeFollowup.FreeWordFamily

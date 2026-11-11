import SharedDecoders.CapacityTripleSource
import SharedDecoders.CapacitySubcodeTransport

/-! # Actual finite binary extensions and every divisible lane width -/

namespace SharedDecoders.CapacityTriple

open Module CapacitySubcode

abbrev Bit := ZMod 2
abbrev Extension (s : ℕ) := CyclotomicField (3 * s) Bit

variable {s : ℕ} [NeZero s]

omit [NeZero s] in
private theorem odd_cast_ne_zero (hodd : Odd (3 * s)) : (3 * s : Bit) ≠ 0 := by
  intro h
  apply (Nat.not_even_iff_odd.mpr hodd)
  apply (ZMod.natCast_eq_zero_iff_even).mp
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

noncomputable def character (hodd : Odd (3 * s)) :
    AddChar (ZMod (3 * s)) (Extension s) := by
  letI : NeZero ((3 * s : ℕ) : Bit) := ⟨by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using odd_cast_ne_zero hodd⟩
  exact AddChar.zmodChar (3 * s) (IsCyclotomicExtension.zeta_pow (3 * s) Bit (Extension s))

theorem character_primitive (hodd : Odd (3 * s)) : (character hodd).IsPrimitive := by
  have : NeZero ((3 * s : ℕ) : Bit) := ⟨by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using odd_cast_ne_zero hodd⟩
  exact AddChar.zmodChar_primitive_of_primitive_root (3 * s)
    (IsCyclotomicExtension.zeta_spec (3 * s) Bit (Extension s))

theorem character_injective (hodd : Odd (3 * s)) :
    Function.Injective (character hodd) := by
  let χ := character hodd
  intro a c hac
  have hz : χ (a - c) = 1 := by
    calc
      _ = χ a * χ (-c) := by rw [sub_eq_add_neg, χ.map_add_eq_mul]
      _ = χ c * χ (-c) := by rw [hac]
      _ = 1 := by rw [← χ.map_add_eq_mul, add_neg_cancel, χ.map_zero_eq_one]
  exact sub_eq_zero.mp (((character_primitive hodd).zmod_char_eq_one_iff (3 * s) (a - c)).mp hz)

/-- The common extension width is positive and finite. For every multiple, the
hard source is a literal binary matrix source. The upper bound permits all
binary-linear mixing of its extension-coordinate blocks. -/
theorem exists_width_stable_hard_source {κ : Type*}
    (hodd : Odd (3 * s)) (p : ZMod (3 * s) → κ)
    (hp : ∀ c, p (c + (s : ZMod (3 * s))) = p c) :
    ∃ ell : ℕ, 0 < ell ∧ ∀ B : ℕ, ell ∣ B →
      ∃ H : Submodule Bit (State (3 * s) (Fin B → Bit)),
        IsSharedCode Bit p H ∧
        3 * finrank Bit H = B * (3 * s) * (3 * s) ∧
        ∀ C ≤ H, IsLinearSharedCode p C →
          9 * finrank Bit C ≤ 2 * B * (3 * s) * (3 * s) := by
  let E := Extension s
  have : NeZero ((3 * s : ℕ) : Bit) := ⟨by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using odd_cast_ne_zero hodd⟩
  have : FiniteDimensional Bit E := IsCyclotomicExtension.finite_of_singleton (3 * s) Bit E
  let χ := character hodd
  have hχ : Function.Injective χ := character_injective hodd
  let ell := finrank Bit E
  have hell : 0 < ell := Module.finrank_pos
  refine ⟨ell, hell, ?_⟩
  intro B hB
  obtain ⟨q, rfl⟩ := hB
  let e : (Fin q → E) ≃ₗ[Bit] (Fin (ell * q) → Bit) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [ell, Module.finrank_pi_fintype, mul_comm])
  let H := hardSource (F := Bit) (q := q) χ
  refine ⟨H.map (entryEquiv e).toLinearMap,
    shared_map (hardSource_shared χ hχ p) e, ?_, ?_⟩
  · rw [(entryEquiv e).finrank_map_eq, finrank_hardSource χ hχ]
    dsimp [ell]
    ring
  · intro C hC hlin
    have hh := subcode_bound_map H (2 * s * (q * s * finrank Bit E))
      (hardSource_linear_subcode_bound χ hχ p hp) e C hC hlin
    dsimp [ell]
    nlinarith

end SharedDecoders.CapacityTriple

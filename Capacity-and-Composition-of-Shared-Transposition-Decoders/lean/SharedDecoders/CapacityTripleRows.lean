import SharedDecoders.ConstructionFourier
import SharedDecoders.CapacityLinearization
import SharedDecoders.CapacityGluing
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-! # Spectral row pairs for the triple obstruction

The actual cyclic Fourier characters, rather than a supplied disjointness
hypothesis, give a row space with disjoint rotated copies and a three-view
linear dependence.
-/

namespace SharedDecoders.CapacityTriple

open Module
open scoped BigOperators

variable {E : Type*} [Field E] {s : ℕ} [NeZero s]

instance tripleNeZero : NeZero (3 * s) := ⟨by have := NeZero.ne s; omega⟩

def pairCoefficients : (Fin s → E) →ₗ[E] (Fin (3 * s) → E) where
  toFun x i := if i.val % 3 = 0 then 0 else x ⟨i.val / 3, by omega⟩
  map_add' x y := by
    ext i
    dsimp
    split_ifs <;> simp
  map_smul' a x := by
    ext i
    dsimp
    split_ifs <;> simp

def firstFrequency (j : Fin s) : Fin (3 * s) := ⟨3 * j.val + 1, by omega⟩
def secondFrequency (j : Fin s) : Fin (3 * s) := ⟨3 * j.val + 2, by omega⟩

omit [NeZero s] in
@[simp] theorem pairCoefficients_first (x : Fin s → E) (j : Fin s) :
    pairCoefficients x (firstFrequency j) = x j := by
  simp [pairCoefficients, firstFrequency]
  congr 1
  apply Fin.ext
  change (3 * j.val + 1) / 3 = j.val
  omega

omit [NeZero s] in
@[simp] theorem pairCoefficients_second (x : Fin s → E) (j : Fin s) :
    pairCoefficients x (secondFrequency j) = x j := by
  simp [pairCoefficients, secondFrequency]
  congr 1
  apply Fin.ext
  change (3 * j.val + 2) / 3 = j.val
  omega

omit [NeZero s] in
theorem pairCoefficients_injective : Function.Injective (pairCoefficients (E := E) (s := s)) := by
  intro x y h
  funext j
  simpa using congrFun h (firstFrequency j)

noncomputable def pairRowMap (χ : AddChar (ZMod (3 * s)) E) :
    (Fin s → E) →ₗ[E] (ZMod (3 * s) → E) :=
  (fourierSynthesis χ).comp pairCoefficients

omit [NeZero s] in
theorem pairRowMap_injective (χ : AddChar (ZMod (3 * s)) E)
    (hχ : Function.Injective χ) : Function.Injective (pairRowMap χ) :=
  (fourierSynthesis_injective χ hχ).comp pairCoefficients_injective

noncomputable def rowSpace (χ : AddChar (ZMod (3 * s)) E) :
    Submodule E (ZMod (3 * s) → E) := LinearMap.range (pairRowMap χ)

omit [NeZero s] in
theorem finrank_rowSpace (χ : AddChar (ZMod (3 * s)) E)
    (hχ : Function.Injective χ) : finrank E (rowSpace χ) = s := by
  rw [rowSpace, LinearMap.finrank_range_of_inj (pairRowMap_injective χ hχ)]
  simp

omit [NeZero s] in
private theorem char_ne_zero (χ : AddChar (ZMod (3 * s)) E) (a : ZMod (3 * s)) :
    χ a ≠ 0 := by
  intro h
  have h1 := χ.map_add_eq_mul a (-a)
  simp [h] at h1

omit [NeZero s] in
private theorem synthesis_shift (χ : AddChar (ZMod (3 * s)) E)
    (x : Fin (3 * s) → E) (c : ZMod (3 * s)) :
    (fun t => fourierSynthesis χ x (t + c)) =
      fourierSynthesis χ (fun i => χ ((i.val : ZMod (3 * s)) * c) * x i) := by
  funext t
  simp only [fourierSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    mul_add, χ.map_add_eq_mul, mul_assoc]

omit [NeZero s] in
theorem rotated_pairRowMap_eq_zero (χ : AddChar (ZMod (3 * s)) E)
    (hχ : Function.Injective χ) (x y : Fin s → E) (c e : ZMod (3 * s))
    (hce : c ≠ e)
    (h : (fun t => pairRowMap χ x (t + c)) = fun t => pairRowMap χ y (t + e)) :
    x = 0 ∧ y = 0 := by
  change (fun t => fourierSynthesis χ (pairCoefficients x) (t + c)) =
    (fun t => fourierSynthesis χ (pairCoefficients y) (t + e)) at h
  rw [synthesis_shift, synthesis_shift] at h
  have hc := fourierSynthesis_injective χ hχ h
  have hz (j : Fin s) : x j = 0 ∧ y j = 0 := by
    have h1 := congrFun hc (firstFrequency j)
    have h2 := congrFun hc (secondFrequency j)
    simp only [pairCoefficients_first, pairCoefficients_second] at h1 h2
    have hid : ((secondFrequency j).val : ZMod (3 * s)) =
        ((firstFrequency j).val : ZMod (3 * s)) + 1 := by
      simp [firstFrequency, secondFrequency, Nat.cast_add]
      ring
    rw [hid, add_mul, add_mul, χ.map_add_eq_mul, χ.map_add_eq_mul,
      one_mul, one_mul] at h2
    have heq : χ c * (χ (((firstFrequency j).val : ZMod (3 * s)) * c) * x j) =
        χ e * (χ (((firstFrequency j).val : ZMod (3 * s)) * c) * x j) := by
      calc
        _ = χ (((firstFrequency j).val : ZMod (3 * s)) * c) * χ c * x j := by ring
        _ = χ (((firstFrequency j).val : ZMod (3 * s)) * e) * χ e * y j := h2
        _ = χ e * (χ (((firstFrequency j).val : ZMod (3 * s)) * e) * y j) := by ring
        _ = _ := by rw [h1]
    have hx : x j = 0 := by
      have hn : χ c ≠ χ e := fun hh => hce (hχ hh)
      have hz := (mul_eq_mul_right_iff.mp heq).resolve_left hn
      exact (mul_eq_zero.mp hz).resolve_left (char_ne_zero χ _)
    have hy : y j = 0 := by
      rw [hx, mul_zero] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left (char_ne_zero χ _)
    exact ⟨hx, hy⟩
  exact ⟨funext (fun j => (hz j).1), funext (fun j => (hz j).2)⟩

omit [NeZero s] in
private theorem frequency_cube (χ : AddChar (ZMod (3 * s)) E) (n : ℕ) :
    χ ((n : ZMod (3 * s)) * (s : ZMod (3 * s))) ^ 3 = 1 := by
  rw [← χ.map_nsmul_eq_pow]
  have hz : (3 : ℕ) • ((n : ZMod (3 * s)) * (s : ZMod (3 * s))) = 0 := by
    rw [nsmul_eq_mul]
    have hm : (3 : ZMod (3 * s)) * (s : ZMod (3 * s)) = 0 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using (ZMod.natCast_self (3 * s))
    calc
      _ = (n : ZMod (3 * s)) * (3 * (s : ZMod (3 * s))) := by ring
      _ = 0 := by rw [hm, mul_zero]
  rw [hz, χ.map_zero_eq_one]

private theorem frequency_sum (χ : AddChar (ZMod (3 * s)) E)
    (hχ : Function.Injective χ) (n : ℕ) (hn : n % 3 ≠ 0) :
    1 + χ ((n : ZMod (3 * s)) * (s : ZMod (3 * s))) +
      χ ((n : ZMod (3 * s)) * (s : ZMod (3 * s))) ^ 2 = 0 := by
  have hne : χ ((n : ZMod (3 * s)) * (s : ZMod (3 * s))) ≠ 1 := by
    intro h
    have hz : ((n : ZMod (3 * s)) * (s : ZMod (3 * s))) = 0 :=
      hχ (h.trans χ.map_zero_eq_one.symm)
    have hh : 3 * s ∣ n * s := (ZMod.natCast_eq_zero_iff _ _).mp (by
      simpa only [Nat.cast_mul] using hz)
    exact hn (Nat.mod_eq_zero_of_dvd ((mul_dvd_mul_iff_right (NeZero.ne s)).mp hh))
  have hc := frequency_cube χ n
  have hz : (χ ((n : ZMod (3 * s)) * (s : ZMod (3 * s))) - 1) *
      (1 + χ ((n : ZMod (3 * s)) * (s : ZMod (3 * s))) +
        χ ((n : ZMod (3 * s)) * (s : ZMod (3 * s))) ^ 2) = 0 := by
    calc
      _ = χ ((n : ZMod (3 * s)) * (s : ZMod (3 * s))) ^ 3 - 1 := by ring
      _ = 0 := by rw [hc, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

theorem pairRowMap_triple (χ : AddChar (ZMod (3 * s)) E)
    (hχ : Function.Injective χ) (x : Fin s → E) :
    pairRowMap χ x + (fun t => pairRowMap χ x (t + (s : ZMod (3 * s)))) +
      (fun t => pairRowMap χ x (t + 2 * (s : ZMod (3 * s)))) = 0 := by
  change fourierSynthesis χ (pairCoefficients x) +
    (fun t => fourierSynthesis χ (pairCoefficients x) (t + (s : ZMod (3 * s)))) +
    (fun t => fourierSynthesis χ (pairCoefficients x) (t + 2 * (s : ZMod (3 * s)))) = 0
  rw [synthesis_shift, synthesis_shift, ← map_add, ← map_add]
  have hz : pairCoefficients x +
      (fun i => χ ((i.val : ZMod (3 * s)) * (s : ZMod (3 * s))) * pairCoefficients x i) +
      (fun i => χ ((i.val : ZMod (3 * s)) * (2 * (s : ZMod (3 * s)))) * pairCoefficients x i) = 0 := by
    funext i
    have hdouble : χ ((i.val : ZMod (3 * s)) * (2 * (s : ZMod (3 * s)))) =
        χ ((i.val : ZMod (3 * s)) * (s : ZMod (3 * s))) ^ 2 := by
      rw [show (i.val : ZMod (3 * s)) * (2 * (s : ZMod (3 * s))) =
        (i.val : ZMod (3 * s)) * (s : ZMod (3 * s)) +
          (i.val : ZMod (3 * s)) * (s : ZMod (3 * s)) by ring,
        χ.map_add_eq_mul, pow_two]
    change pairCoefficients x i + _ * pairCoefficients x i + _ * pairCoefficients x i = 0
    rw [hdouble]
    by_cases hn : i.val % 3 = 0
    · simp [pairCoefficients, hn]
    · calc
        _ = (1 + χ ((i.val : ZMod (3 * s)) * (s : ZMod (3 * s))) +
          χ ((i.val : ZMod (3 * s)) * (s : ZMod (3 * s))) ^ 2) * pairCoefficients x i := by ring
        _ = 0 := by rw [frequency_sum χ hχ i.val hn, zero_mul]
  rw [hz, map_zero]

end SharedDecoders.CapacityTriple

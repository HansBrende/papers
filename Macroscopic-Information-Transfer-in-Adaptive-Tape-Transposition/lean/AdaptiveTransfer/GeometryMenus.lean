import LeanMachine.BoundedTuples
import BoundedNesting.Families
import Mathlib.Data.Fintype.Powerset

/-! Finite geometry menus with their actual increment and counter encoders.
These declarations do not assert the adaptive fragment replay theorem: the
native extraction and reconstruction obligations remain separate. -/

namespace AdaptiveTransfer

open LeanMachine BoundedNesting
open scoped BigOperators

/-- Ordered samples of an actual unit walk have the required joint variation
budget. All positions, including the public initial position, are retained. -/
def sampledWalk {m T : ℕ} (y : ℕ → ℤ) (hy : IsWalk y) (hy0 : y 0 = 0)
    (t : Fin (m + 1) → ℕ) (ht : Monotone t)
    (ht0 : t 0 = 0) (htT : t (Fin.last m) ≤ T) : SampledPositions m T :=
  sampleUnitPath y (fun a b hab => by
    have h := hy.lip hab
    have h' : |y b - y a| ≤ ((b - a : ℕ) : ℤ) := abs_le.mpr ⟨by omega, h.1⟩
    rw [← Int.natCast_natAbs] at h'
    exact_mod_cast h') t ht ht0 hy0 htT

abbrev HeadDescription (s T : ℕ) :=
  ((Fin s → Bool) × BoundedTuple s T) × (Fin s → Fin 3)

def headDescription {s T : ℕ}
    (data : SampledPositions s T × (Fin s → Fin 3)) : HeadDescription s T :=
  (signedTupleEncode (sampledPositionIncrements data.1), data.2)

theorem headDescription_injective (s T : ℕ) :
    Function.Injective (@headDescription s T) := by
  intro x y h
  apply Prod.ext
  · apply sampledPositionIncrements_injective s T
    apply signedTupleEncode_injective s T
    exact congrArg Prod.fst h
  · simpa only [headDescription] using congrArg Prod.snd h

theorem headDescription_card (s T : ℕ) :
    Fintype.card (HeadDescription s T) = 6 ^ s * (T + s).choose s := by
  simp only [HeadDescription, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool, boundedTuple_card]
  rw [show (6 : ℕ) = 2 * 3 from rfl, mul_pow]
  ring

/-- The global cut geometry description. Counter samples are stored as their
multiset; monotonicity gives their unique chronological ordering. -/
abbrev GlobalGeometryMenu (k P T s : ℕ) :=
  Fin (T + 1) × {B : Finset (Fin T) // B.card = s} ×
    BoundedTuple (s + 1) T × (Fin (k + 1) → HeadDescription s T) ×
    BoundedTuple (2 * (s + 1)) T × Sym (Fin (P + 1)) (4 * s + 2)

def globalGeometryMenuSize (k P T s : ℕ) : ℕ :=
  (T + 1) * T.choose s * (T + (s + 1)).choose (s + 1) *
    (6 ^ s * (T + s).choose s) ^ (k + 1) *
    (T + 2 * (s + 1)).choose (2 * (s + 1)) *
    (P + 4 * s + 2).choose (4 * s + 2)

theorem globalGeometryMenu_card (k P T s : ℕ) :
    Fintype.card (GlobalGeometryMenu k P T s) = globalGeometryMenuSize k P T s := by
  simp only [GlobalGeometryMenu, globalGeometryMenuSize, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_finset_len, boundedTuple_card,
    Fintype.card_fun, Fintype.card_bool, Sym.card_sym_eq_choose]
  have h : P + 1 + (4 * s + 2) - 1 = P + 4 * s + 2 := by omega
  have hsix : (6 : ℕ) ^ s = 2 ^ s * 3 ^ s := by rw [← mul_pow]; rfl
  rw [h, hsix]
  ring

/-- The localized menu has `N+s` retained intervals and no independent
raw-extremum field, exactly as in the off-carrier proof. -/
abbrev LocalGeometryMenu (k P T N s : ℕ) :=
  Fin (T + 1) × {B : Finset (Fin T) // B.card = s} ×
    BoundedTuple (N + s) T × (Fin (k + 1) → HeadDescription s T) ×
    Sym (Fin (P + 1)) (4 * s + 2 * N)

def localGeometryMenuSize (k P T N s : ℕ) : ℕ :=
  (T + 1) * T.choose s * (T + N + s).choose (N + s) *
    (6 ^ s * (T + s).choose s) ^ (k + 1) *
    (P + 4 * s + 2 * N).choose (4 * s + 2 * N)

theorem localGeometryMenu_card (k P T N s : ℕ) :
    Fintype.card (LocalGeometryMenu k P T N s) =
      localGeometryMenuSize k P T N s := by
  simp only [LocalGeometryMenu, localGeometryMenuSize, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_finset_len, boundedTuple_card,
    Fintype.card_fun, Fintype.card_bool, Sym.card_sym_eq_choose]
  have h : P + 1 + (4 * s + 2 * N) - 1 = P + 4 * s + 2 * N := by omega
  have hsix : (6 : ℕ) ^ s = 2 ^ s * 3 ^ s := by rw [← mul_pow]; rfl
  rw [h, ← Nat.add_assoc T N s, hsix]
  ring

end AdaptiveTransfer

import SharedDecoders.CompositionWordAction
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # The literal anchored difference and its transported fixed set -/

namespace SharedDecoders

variable {d : ℕ} [NeZero d] {F : Type*} [Field F]

/-- One untouched coordinate closes the cyclic difference chain. -/
def anchoredDifferenceLinear (F : Type*) [Field F] (d : ℕ) [NeZero d] :
    ScalarWord d F →ₗ[F] ScalarWord d F where
  toFun x i := if i = 0 then x 0 else x i + x (i + 1)
  map_add' x y := by
    funext i
    by_cases hi : i = 0
    · simp [hi]
    · simp [hi]
      ring
  map_smul' t x := by
    funext i
    by_cases hi : i = 0 <;> simp [hi, mul_add]

theorem anchoredDifferenceLinear_injective :
    Function.Injective (anchoredDifferenceLinear F d) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hz : x 0 = 0 := by simpa [anchoredDifferenceLinear] using congrFun hx 0
  have hn : ∀ n : ℕ, x (-(n : ZMod d)) = 0 := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih =>
        by_cases he : (-(↑(n + 1) : ZMod d)) = 0
        · rw [he]
          exact hz
        · have h := congrFun hx (-(↑(n + 1) : ZMod d))
          have hpos : (-(↑(n + 1) : ZMod d)) + 1 = -(n : ZMod d) := by
            push_cast
            ring
          change (if (-(↑(n + 1) : ZMod d)) = 0 then x 0 else
            x (-(↑(n + 1) : ZMod d)) + x (-(↑(n + 1) : ZMod d) + 1)) = 0 at h
          simp only [he, ite_false, hpos, ih, add_zero] at h
          exact h
  funext i
  have h := hn (-i).val
  simpa using h

noncomputable def anchoredDifference (F : Type*) [Field F] (d : ℕ) [NeZero d] :
    Equiv.Perm (ScalarWord d F) :=
  (LinearEquiv.ofInjectiveEndo (anchoredDifferenceLinear F d)
    anchoredDifferenceLinear_injective).toEquiv

@[simp] lemma anchoredDifference_apply (x : ScalarWord d F) (i : ZMod d) :
    anchoredDifference F d x i = if i = 0 then x 0 else x i + x (i + 1) := rfl

@[simp] lemma anchoredDifference_zero : anchoredDifference F d (fun _ => 0) = fun _ => 0 := by
  funext i
  simp

/-- Fixed scalar words of the one-step shift are the literal constant words. -/
lemma scalarRotation_one_fixed {S : Type*} (x : ScalarWord d S)
    (hx : scalarRotation 1 x = x) : ∀ i, x i = x 0 := by
  have hn : ∀ n : ℕ, x (n : ZMod d) = x 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have he := congrFun hx (n : ZMod d)
        change x ((n : ZMod d) + 1) = x (n : ZMod d) at he
        simpa only [Nat.cast_add, Nat.cast_one] using he.trans ih
  intro i
  simpa using hn i.val

lemma anchoredDifference_constant [CharP F 2] (a : F) :
    anchoredDifference F d (fun _ => a) = Pi.single 0 a := by
  funext i
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi, CharTwo.add_self_eq_zero]

/-- The transported fixed set is exactly the anchor-coordinate axis. -/
lemma anchored_fixed_image [CharP F 2] (y : ScalarWord d F) :
    (∃ x, scalarRotation 1 x = x ∧ anchoredDifference F d x = y) ↔
      ∃ a, y = Pi.single 0 a := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x 0, ?_⟩
    have he : x = fun _ => x 0 := funext (scalarRotation_one_fixed x hx)
    rw [he, anchoredDifference_constant]
  · rintro ⟨a, rfl⟩
    exact ⟨fun _ => a, rfl, anchoredDifference_constant a⟩

/-- No nonzero scalar shift commutes with the actual conjugated shift. -/
theorem anchored_conjugate_no_period [CharP F 2] (s : ZMod d)
    (h : ∀ y, anchoredDifference F d (scalarRotation 1
      ((anchoredDifference F d).symm (scalarRotation s y))) =
        scalarRotation s (anchoredDifference F d (scalarRotation 1
          ((anchoredDifference F d).symm y)))) : s = 0 := by
  have hfixed : ∃ x, scalarRotation 1 x = x ∧
      anchoredDifference F d x = Pi.single 0 (1 : F) :=
    (anchored_fixed_image _).mpr ⟨1, rfl⟩
  have hpres := fixed_image_preserved (anchoredDifference F d)
    (scalarRotation 1) (scalarRotation s) h hfixed
  obtain ⟨a, ha⟩ := (anchored_fixed_image _).mp hpres
  by_contra hs
  have he := congrFun ha (-s)
  have hneg : -s ≠ 0 := neg_ne_zero.mpr hs
  change (Pi.single 0 (1 : F) : ScalarWord d F) (-s + s) =
    (Pi.single 0 a : ScalarWord d F) (-s) at he
  simp [hneg] at he


/-- The literal anchored map forbids every nonzero final mask period, even with
an equivariant outer stage. This uses only fixed-set transport, not the later
adjacent-pair group-generation calculation. -/
theorem anchored_final_mask_aperiodic [Finite F] [CharP F 2]
    {b : ℕ} [NeZero b] {κ : Type*}
    (p : ZMod d → κ) (U K B H : State d (Fin b → F) → State d (Fin b → F))
    (hU : Equivariant U) (hB : Equivariant B) (hH : Equivariant H)
    (hK : ClassUniform p K)
    (hexact : ∀ X, U (K (B (wordwise (anchoredDifference F d) (H X)))) = swap X)
    (s : ZMod d) (hp : ∀ c, p (c + s) = p c) : s = 0 := by
  obtain ⟨LE, hLE, hcomm⟩ := literal_period_complete hU hB hH hK hexact
  have heq : LE = wordwise (anchoredDifference F d) := Equiv.ext hLE
  subst LE
  apply anchored_conjugate_no_period (F := F) s
  intro y
  funext j
  let X : State d (Fin b → F) := fun _ c _ => y c
  exact congrFun (congrFun (congrFun (hcomm s hp X) 0) j) 0

end SharedDecoders

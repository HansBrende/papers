import SharedDecoders.CompositionOrbitResidues
import SharedDecoders.CompositionWordAction
import Mathlib.GroupTheory.PGroup

/-! # An actual nontransitive binary example

The displayed four-bit operation is an explicit order-five permutation.
All identities below are checked directly on the sixteen literal binary
words by the kernel; no field-coordinate identification is assumed.
-/

namespace SharedDecoders

open MulAction

abbrev FourBitWord := ScalarWord 4 (ZMod 2)

def orderFiveMap (x : FourBitWord) : FourBitWord := fun i =>
  if i = 0 then x 2 else if i = 1 then x 2 + x 3
  else if i = 2 then x 1 + x 2 else x 0 + x 2

private theorem orderFiveMap_fifth : ∀ x : FourBitWord, orderFiveMap^[5] x = x := by
  decide +kernel

def orderFivePerm : Equiv.Perm FourBitWord where
  toFun := orderFiveMap
  invFun := orderFiveMap^[4]
  left_inv x := by simpa [Function.iterate_succ_apply] using orderFiveMap_fifth x
  right_inv x := by simpa [Function.iterate_succ_apply'] using orderFiveMap_fifth x

theorem orderFivePerm_zero : orderFivePerm 0 = 0 := by decide +kernel

theorem orderFivePerm_fixed : ∀ x : FourBitWord, orderFivePerm x = x ↔ x = 0 := by
  decide +kernel

theorem orderFivePerm_order : orderOf orderFivePerm = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply Equiv.ext
    exact orderFiveMap_fifth
  · intro h
    have hx := congrArg (fun g : Equiv.Perm FourBitWord => g (fun i => if i=0 then 1 else 0)) h
    exact (by decide +kernel : orderFivePerm (fun i => if i=0 then 1 else 0) ≠
      (fun i => if i=0 then 1 else 0)) hx

/-- The difference of the two actual adjacent conjugates is the order-five
multiplier, so equal covariance phases force invariance under it. -/
theorem orderFive_conjugate_difference :
    conjugateWordRotation orderFivePerm 0 *
      (conjugateWordRotation orderFivePerm 1)⁻¹ = orderFivePerm := by
  apply Equiv.ext
  decide +kernel

private def fiveWordSet (x : FourBitWord) : Prop :=
  x = (fun _ => 1) ∨ ∃ i : ZMod 4, x = fun j => if j=i then 1 else 0

private instance : DecidablePred fiveWordSet := fun x => by
  unfold fiveWordSet
  infer_instance

private def fiveWordPreserving : Subgroup (Equiv.Perm FourBitWord) where
  carrier := {g | ∀ x, fiveWordSet (g x) ↔ fiveWordSet x}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun hg hh x => (hg _).trans (hh x)
  inv_mem' := by
    intro g hg x
    simpa using (hg (g⁻¹ x)).symm

private theorem adjacent_preserves_five :
    conjugatePairGroup orderFivePerm 0 1 ≤ fiveWordPreserving := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact (by decide +kernel : ∀ x, fiveWordSet (conjugateWordRotation orderFivePerm 0 x) ↔
      fiveWordSet x)
  · exact (by decide +kernel : ∀ x, fiveWordSet (conjugateWordRotation orderFivePerm 1 x) ↔
      fiveWordSet x)

/-- The actual adjacent-pair group fails scalar nonzero-word transitivity. -/
theorem orderFive_pair_nontransitive :
    ¬ ∀ x : FourBitWord, x ≠ 0 → ∀ y : FourBitWord, y ≠ 0 →
      ∃ g : conjugatePairGroup orderFivePerm 0 1, g.val x = y := by
  intro h
  let x : FourBitWord := fun i => if i=0 then 1 else 0
  let y : FourBitWord := fun i => if i=0 ∨ i=1 then 1 else 0
  obtain ⟨g, hg⟩ := h x (by decide +kernel) y (by decide +kernel)
  have hp := adjacent_preserves_five g.property x
  rw [hg] at hp
  exact (by decide +kernel : ¬fiveWordSet y) (hp.mpr (by decide +kernel))

private theorem orderFive_orbit_divisor (x : FourBitWord) (hx : x ≠ 0) :
    5 ∣ (orbit (Subgroup.zpowers orderFivePerm) x).ncard := by
  classical
  let := Fintype.ofFinite (orbit (Subgroup.zpowers orderFivePerm) x)
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hG : IsPGroup 5 (Subgroup.zpowers orderFivePerm) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderFivePerm_order, pow_one])
  obtain ⟨n, hn⟩ := hG.card_orbit x
  have hn0 : n ≠ 0 := by
    intro h
    have hc : Fintype.card (orbit (Subgroup.zpowers orderFivePerm) x) = 1 := by
      simpa [h, Nat.card_eq_fintype_card] using hn
    have hf := mem_fixedPoints_iff_card_orbit_eq_one.mpr hc
    have he := hf ⟨orderFivePerm, Subgroup.mem_zpowers orderFivePerm⟩
    exact hx ((orderFivePerm_fixed x).mp he)
  change 5 ∣ Nat.card (orbit (Subgroup.zpowers orderFivePerm) x)
  rw [hn]
  exact dvd_pow_self _ hn0

/-- Equal output phases under the two actual conjugates exclude balanced
power-of-two fibres for every tuple length, despite nontransitivity. -/
theorem orderFive_no_balanced_covariance {ι Z : Type*} [Finite ι]
    (σ : Equiv.Perm Z) (f : (ι → FourBitWord) → Z)
    (hzero : ∀ x, f (fun i => conjugateWordRotation orderFivePerm 0 (x i)) = σ (f x))
    (hone : ∀ x, f (fun i => conjugateWordRotation orderFivePerm 1 (x i)) = σ (f x))
    (z : Z) (hz : z ≠ f 0) (n : ℕ)
    (hbal : Nat.card {x : ι → FourBitWord // f x = z} = 2 ^ n) : False := by
  have hL (x : ι → FourBitWord) : f (fun i => orderFivePerm (x i)) = f x := by
    let y : ι → FourBitWord := fun i => (conjugateWordRotation orderFivePerm 1)⁻¹ (x i)
    have he : (fun i => conjugateWordRotation orderFivePerm 1 (y i)) = x := by
      funext i
      exact Equiv.apply_symm_apply _ _
    have hd : (fun i => conjugateWordRotation orderFivePerm 0 (y i)) =
        fun i => orderFivePerm (x i) := by
      funext i
      exact congrArg (fun g : Equiv.Perm FourBitWord => g (x i)) orderFive_conjugate_difference
    have h := (hzero y).trans (hone y).symm
    rwa [he, hd] at h
  have hinv (g : Subgroup.zpowers orderFivePerm) (x : ι → FourBitWord) :
      f (g • x) = f x := by
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr g.property)
    have hp (k : ℕ) (x : ι → FourBitWord) :
        f (fun i => (orderFivePerm ^ k) (x i)) = f x := by
      induction k generalizing x with
      | zero => rfl
      | succ k ih =>
        simp only [pow_succ', Equiv.Perm.mul_apply]
        exact (hL _).trans (ih x)
    change f (fun i => g.val (x i)) = f x
    rw [← hk]
    exact hp k x
  apply no_balanced_semiregular (G := Subgroup.zpowers orderFivePerm) (0 : FourBitWord)
    (fun g => ?_) 5 2 n (by decide) (by decide) orderFive_orbit_divisor f hinv z hz hbal
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr g.property)
  change g.val 0 = 0
  have hp (k : ℕ) : (orderFivePerm ^ k) (0 : FourBitWord) = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, orderFivePerm_zero]
  simpa only [hk] using hp k

/-- The example's actual complete two-stage application, with arbitrary
nonlinear lane mixing in the surrounding maps. -/
theorem orderFive_adjacent_class_impossible {b : ℕ} [NeZero b] {κ : Type*}
    (p : ZMod 4 → κ) (K H : State 4 (Fin b → ZMod 2) → State 4 (Fin b → ZMod 2))
    (hH : Equivariant H) (hK : ClassUniform p K) (hp : p 0 = p 1)
    (hexact : ∀ X, K (wordwise orderFivePerm (H X)) = swap X) : False := by
  classical
  obtain ⟨f, hf⟩ := hK
  have hHi : Function.Injective H := by
    intro X Y h
    apply swapEquiv.injective
    change swap X = swap Y
    rw [← hexact X, ← hexact Y, h]
  let HE := Equiv.ofBijective H (Finite.injective_iff_bijective.mp hHi)
  have hKs : Function.Surjective K := by
    intro Y
    exact ⟨wordwise orderFivePerm (H (swap Y)), by rw [hexact, swap_swap]⟩
  have hKb : Function.Bijective K := Finite.injective_iff_bijective.mp
    (Finite.injective_iff_surjective.mpr hKs)
  have hQ := conjugate_intertwining (F := K) (wordwise orderFivePerm) HE hH hexact
  let E : State 4 (Fin b → ZMod 2) ≃ ((ZMod 4 × Fin b) → FourBitWord) := matrixWordEquiv
  let φ : ((ZMod 4 × Fin b) → FourBitWord) → (ZMod 4 → Fin b → ZMod 2) := f (p 0) ∘ E.symm
  have hc (c : ZMod 4) (x : (ZMod 4 × Fin b) → FourBitWord) :
      f (p c) (E.symm (fun i => conjugateWordRotation orderFivePerm c (x i))) =
        fun j => f (p c) (E.symm x) (j+1) := by
    change f (p c) (wordwise (conjugateWordRotation orderFivePerm c) (E.symm x)) = _
    rw [wordwise_conjugate]
    exact complete_decoder_covariance p K _ f hf hQ c (E.symm x)
  obtain ⟨z, hz⟩ := exists_ne (φ 0)
  have hb : Nat.card {x : (ZMod 4 × Fin b) → FourBitWord // φ x = z} = 2 ^ (b*4*3) := by
    have he := Nat.card_congr (E.symm.subtypeEquiv
      (p := fun x => φ x=z) (q := fun X => f (p 0) X=z) (fun _ => Iff.rfl))
    rw [he, complete_decoder_fiber_card p K f hf hKb 0 z]
    simp [← pow_mul, ZMod.card]
  apply orderFive_no_balanced_covariance (scalarRotation (S := Fin b → ZMod 2) 1)
    φ (fun x => hc 0 x) (fun x => ?_) z hz (b*4*3) hb
  change f (p 0) (E.symm (fun i => conjugateWordRotation orderFivePerm 1 (x i))) =
    fun j => f (p 0) (E.symm x) (j+1)
  simpa only [hp] using hc 1 x

end SharedDecoders

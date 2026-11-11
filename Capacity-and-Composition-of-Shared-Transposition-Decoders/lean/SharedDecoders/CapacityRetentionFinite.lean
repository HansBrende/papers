import SharedDecoders.CapacityRetentionOrbit
import Mathlib.Basic.Real.Basic

/-! # Finite symmetric-retention bounds

The exact retained-space invoice is bounded using the dimensions of actual
symmetric intersections. No assumption is made on decoder linearity or lanes.
-/

namespace SharedDecoders

open Module

variable {F A κ : Type*} [Field F] [AddCommGroup A] [Module F A]
  [FiniteDimensional F A] {d : ℕ} [NeZero d]

/-- The retained symmetric sum has at most twice the missing symmetric
codimension in excess of the exact full-symmetric cost. -/
theorem retained_sum_defect_bound (C : Submodule F (State d A)) (s : ZMod d) :
    let S : Submodule F (State d A) := symmetricSpace
    let S₀ := C ⊓ S
    let η := finrank F S - finrank F S₀
    2 * (d * d * finrank F A - finrank F (S₀ ⊔ S₀.map (rotLinear F s) : Submodule F (State d A))) +
      d * finrank F A ≤ 4 * η + d * Nat.gcd d s.val * finrank F A := by
  let S : Submodule F (State d A) := symmetricSpace
  let S₀ := C ⊓ S
  have hmap : finrank F (S₀.map (rotLinear F s)) = finrank F S₀ :=
    (rotLinearEquiv F (A := A) s).finrank_map_eq S₀
  have hgrass := Submodule.finrank_sup_add_finrank_inf_eq S₀ (S₀.map (rotLinear F s))
  rw [hmap] at hgrass
  have hpair : finrank F (S₀ ⊓ S₀.map (rotLinear F s) : Submodule F (State d A)) ≤
      finrank F (RetentionOrbit.pairedSymmetric (F := F) (A := A) s) :=
    Submodule.finrank_mono (inf_le_inf inf_le_right (Submodule.map_mono inf_le_right))
  have hpairdim := RetentionOrbit.twice_finrank_pairedSymmetric (F := F) (A := A) s
  have hsym := two_mul_finrank_symmetricSpace (F := F) (A := A) (I := ZMod d)
  simp only [ZMod.card] at hsym
  have hle : finrank F S₀ ≤ finrank F S := Submodule.finrank_mono inf_le_right
  have hamb : finrank F (S₀ ⊔ S₀.map (rotLinear F s) : Submodule F (State d A)) ≤
      d * d * finrank F A := (Submodule.finrank_le _).trans_eq finrank_state
  change 2 * (d * d * finrank F A -
    finrank F (S₀ ⊔ S₀.map (rotLinear F s) : Submodule F (State d A))) +
    d * finrank F A ≤ 4 * (finrank F S - finrank F S₀) +
      d * Nat.gcd d s.val * finrank F A
  change 2 * finrank F S = _ at hsym
  have hη := Nat.sub_add_cancel hle
  have hdef := Nat.sub_add_cancel hamb
  nlinarith

/-- Doubled natural-number form, also valid for an empty family of shifts. -/
theorem IsSharedCode.retention_bound_nat {p : ZMod d → κ}
    {C : Submodule F (State d A)} (hC : IsSharedCode F p C)
    {J : Type*} [Fintype J] (t : J → ZMod d) :
    let S : Submodule F (State d A) := symmetricSpace
    let η := finrank F S - finrank F (C ⊓ S : Submodule F (State d A))
    let U := uncoveredRows (fun j => coveredRows p (t j))
    2 * finrank F C + 2 * η + d * Fintype.card J * finrank F A + U.card * finrank F A ≤
      2 * finrank F S + 4 * Fintype.card J * η +
        d * (∑ j, Nat.gcd d (t j).val) * finrank F A + U.card * U.card * finrank F A := by
  classical
  let S : Submodule F (State d A) := symmetricSpace
  let η := finrank F S - finrank F (C ⊓ S : Submodule F (State d A))
  let U := uncoveredRows (fun j => coveredRows p (t j))
  have hint := hC.intrinsic_retention_bound t
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => retained_sum_defect_bound C (t j))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  have hη : η + finrank F (C ⊓ S : Submodule F (State d A)) = finrank F S :=
    Nat.sub_add_cancel (Submodule.finrank_mono inf_le_right)
  change 2 * finrank F C + 2 * η + d * Fintype.card J * finrank F A + U.card * finrank F A ≤ _
  change 2 * finrank F C + U.card * finrank F A ≤ _ at hint
  change 2 * (∑ j, (d * d * finrank F A -
    finrank F ((C ⊓ S) ⊔ (C ⊓ S).map (rotLinear F (t j)) : Submodule F (State d A)))) +
    d * (Fintype.card J * finrank F A) ≤
    4 * (Fintype.card J * η) + d * (∑ j, Nat.gcd d (t j).val) * finrank F A at hsum
  nlinarith

/-- The finite bound in the paper, with real division and no positivity
requirement on the number of shifts. -/
theorem IsSharedCode.retention_bound {p : ZMod d → κ}
    {C : Submodule F (State d A)} (hC : IsSharedCode F p C)
    {J : Type*} [Fintype J] (t : J → ZMod d) :
    let S : Submodule F (State d A) := symmetricSpace
    let η : ℝ := finrank F S - finrank F (C ⊓ S : Submodule F (State d A))
    let u : ℝ := (uncoveredRows (fun j => coveredRows p (t j))).card
    (finrank F C : ℝ) ≤ finrank F S + (2 * Fintype.card J - 1) * η +
      (d : ℝ) * finrank F A / 2 * (∑ j, ((Nat.gcd d (t j).val : ℝ) - 1)) +
      (finrank F A : ℝ) / 2 * u * (u - 1) := by
  classical
  have hh := hC.retention_bound_nat t
  dsimp only at hh ⊢
  have hle : finrank F (C ⊓ symmetricSpace : Submodule F (State d A)) ≤
      finrank F (symmetricSpace (F := F) (A := A) (I := ZMod d)) :=
    Submodule.finrank_mono inf_le_right
  have hc := (Nat.cast_le (α := ℝ)).mpr hh
  push_cast [Nat.cast_sub hle] at hc
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  nlinarith

end SharedDecoders

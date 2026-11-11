import SharedDecoders.CompositionCyclicKernel
import Mathlib.Algebra.Group.AddChar
import Mathlib.LinearAlgebra.Vandermonde

/-! # Actual frequency bands and the second-stage forced row ambient -/

namespace SharedDecoders

open Module
open scoped BigOperators

variable {F : Type*} [Field F] {d b k : ℕ} [NeZero d]

omit [NeZero d] in
lemma character_nat_mul (χ : AddChar (ZMod d) F) (a : ZMod d) (j : ℕ) :
    χ (a * (j : ZMod d)) = χ a ^ j := by
  simpa [nsmul_eq_mul, mul_comm] using χ.map_nsmul_eq_pow j a

/-- Coefficients of `k` consecutive characters, in the literal matrix coordinates. -/
def bandMap (χ : AddChar (ZMod d) F) (k : ℕ) :
    (Fin k → ZMod d → Fin b → F) →ₗ[F] State d (Fin b → F) where
  toFun a i c l := ∑ ν, χ ((ν.val : ZMod d) * c) * a ν i l
  map_add' a a' := by
    funext i c l
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' t a := by
    funext i c l
    simp [Finset.mul_sum, mul_left_comm]

omit [NeZero d] in
@[simp] lemma bandMap_apply (χ : AddChar (ZMod d) F) (k : ℕ)
    (a : Fin k → ZMod d → Fin b → F) (i c : ZMod d) (l : Fin b) :
    bandMap χ k a i c l = ∑ ν, χ ((ν.val : ZMod d) * c) * a ν i l := rfl

omit [NeZero d] in
theorem bandMap_injective (χ : AddChar (ZMod d) F) (hχ : Function.Injective χ)
    (hk : k ≤ d) : Function.Injective (bandMap (b := b) χ k) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hinj : Function.Injective (fun ν : Fin k => χ (ν.val : ZMod d)) := by
    intro u v huv
    apply Fin.ext
    have h := congrArg ZMod.val (hχ huv)
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_le u.isLt hk),
      Nat.mod_eq_of_lt (lt_of_lt_of_le v.isLt hk)] using h
  funext ν i l
  have hz : (fun μ : Fin k => a μ i l) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj
    intro j
    have h := congrFun (congrFun (congrFun ha i) (j.val : ZMod d)) l
    simp only [bandMap_apply, Pi.zero_apply, character_nat_mul] at h
    simpa only [mul_comm] using h
  exact congrFun hz ν

theorem bandMap_finrank (χ : AddChar (ZMod d) F) (hχ : Function.Injective χ)
    (hk : k ≤ d) : finrank F (LinearMap.range (bandMap (b := b) χ k)) = k * d * b := by
  rw [LinearMap.finrank_range_of_inj (bandMap_injective χ hχ hk)]
  simp [Module.finrank_pi_fintype, ZMod.card, mul_assoc]

def bandComponent (χ : AddChar (ZMod d) F) (ν : Fin k)
    (v : ZMod d → Fin b → F) : State d (Fin b → F) :=
  fun i c l => χ ((ν.val : ZMod d) * c) * v i l

omit [NeZero d] in
lemma rot_bandMap (χ : AddChar (ZMod d) F) (c : ZMod d)
    (a : Fin k → ZMod d → Fin b → F) :
    rot c (bandMap χ k a) =
      ∑ ν, χ ((ν.val : ZMod d) * c) • bandComponent χ ν (a ν) := by
  funext i j l
  simp only [rot_apply, bandMap_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, bandComponent, mul_add, χ.map_add_eq_mul]
  apply Finset.sum_congr rfl
  intro ν _
  ring

/-- The actual row patterns produced by a class-uniform second stage on the band. -/
def bandPatternMap {κ : Type*} (χ : AddChar (ZMod d) F) (p : ZMod d → κ) (k : ℕ) :
    (κ → Fin k → Fin b → F) →ₗ[F] (ZMod d → Fin b → F) where
  toFun a c l := ∑ ν, χ ((ν.val : ZMod d) * c) * a (p c) ν l
  map_add' a a' := by
    funext c l
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' t a := by
    funext c l
    simp [Finset.mul_sum, mul_left_comm]

def bandRowSpace {κ : Type*} (χ : AddChar (ZMod d) F) (p : ZMod d → κ) (k : ℕ) :
    Submodule F (ZMod d → Fin b → F) := LinearMap.range (bandPatternMap χ p k)

omit [NeZero d] in
theorem bandRowSpace_finrank_le {κ : Type*} [Fintype κ]
    (χ : AddChar (ZMod d) F) (p : ZMod d → κ) (k : ℕ) :
    finrank F (bandRowSpace (b := b) χ p k) ≤ Fintype.card κ * k * b := by
  change finrank F (LinearMap.range (bandPatternMap (b := b) χ p k)) ≤ _
  calc
    _ ≤ finrank F (κ → Fin k → Fin b → F) := (bandPatternMap χ p k).finrank_range_le
    _ = Fintype.card κ * k * b := by simp [Module.finrank_pi_fintype, mul_assoc]

omit [NeZero d] in
theorem swap_second_band_column_mem {κ : Type*}
    (χ : AddChar (ZMod d) F) (p : ZMod d → κ)
    (K : State d (Fin b → F) →ₗ[F] State d (Fin b → F))
    (hK : LinearClassUniform p K)
    (a : Fin k → ZMod d → Fin b → F) (j : ZMod d) :
    (fun i => swap (K (bandMap χ k a)) i j) ∈ bandRowSpace χ p k := by
  obtain ⟨f, hf⟩ := hK
  refine ⟨fun J ν l => f J (bandComponent χ ν (a ν)) j l, ?_⟩
  funext i l
  change (∑ ν, χ ((ν.val : ZMod d) * i) *
    f (p i) (bandComponent χ ν (a ν)) j l) = K (bandMap χ k a) j i l
  rw [hf, rot_bandMap, map_sum]
  simp [map_smul, Finset.sum_apply]

end SharedDecoders

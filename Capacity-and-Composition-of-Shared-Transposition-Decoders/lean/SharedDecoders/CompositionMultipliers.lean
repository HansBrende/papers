import SharedDecoders.CompositionOrbitResidues
import Mathlib.FieldTheory.Finite.Basic

/-! Field multipliers in the balanced-intertwiner interface. Invariance under
one nontrivial multiplier already contradicts a coprime power-sized fibre;
scalar or tuple transitivity is unnecessary. -/

namespace SharedDecoders

open MulAction

variable {E I Z : Type*} [Field E] [Finite E] [Finite I]

theorem multiplier_invariance_impossible (μ : Eˣ) (hμ : μ ≠ 1)
    (a n : ℕ) (hcop : Nat.Coprime (Nat.card E - 1) a)
    (f : (I → E) → Z) (hinv : ∀ x, f (fun i => (μ : E) * x i) = f x)
    (z : Z) (hz : z ≠ f 0)
    (hcard : Nat.card {x : I → E // f x = z} = a ^ n) : False := by
  classical
  have horder : 1 < orderOf μ := by
    have hp := orderOf_pos μ
    have hn : orderOf μ ≠ 1 := fun h => hμ (_root_.orderOf_eq_one_iff.mp h)
    omega
  have hd : orderOf μ ∣ Nat.card E - 1 := by
    simpa only [Nat.card_units] using orderOf_dvd_natCard μ
  have hi (g : Subgroup.zpowers μ) (x : I → E) : f (g • x) = f x := by
    obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.mpr g.2
    have hp (k : ℕ) (x : I → E) : f (fun i => ((μ ^ k : Eˣ) : E) * x i) = f x := by
      induction k generalizing x with
      | zero => simp only [pow_zero, Units.val_one, one_mul]
      | succ k ih =>
        simp only [pow_succ', Units.val_mul, mul_assoc]
        exact (hinv _).trans (ih x)
    change f (fun i => (g.1 : E) * x i) = f x
    rw [← hk]
    exact hp k x
  apply no_balanced_free_off_zero (G := Subgroup.zpowers μ) (0 : E)
    (fun _ => mul_zero _) (orderOf μ) a n (Nat.card_zpowers μ)
    horder (hcop.of_dvd_left hd) ?_ f hi z hz hcard
  intro w hw g hg
  apply Subtype.ext
  apply Units.ext
  change (g.1 : E) * w = w at hg
  exact mul_right_cancel₀ hw (hg.trans (one_mul w).symm)

/-- Equal output covariance under two semilinear maps forces the same
multiplier for every balanced decoder with coprime power-sized fibres. -/
theorem semilinear_covariance_multipliers_equal (φ : E ≃+* E) (μ ν : Eˣ)
    (σ : Z → Z) (a n : ℕ) (hcop : Nat.Coprime (Nat.card E - 1) a)
    (f : (I → E) → Z)
    (hμ : ∀ x, f (fun i => (μ : E) * φ (x i)) = σ (f x))
    (hν : ∀ x, f (fun i => (ν : E) * φ (x i)) = σ (f x))
    (z : Z) (hz : z ≠ f 0)
    (hcard : Nat.card {x : I → E // f x = z} = a ^ n) : μ = ν := by
  by_contra hne
  apply multiplier_invariance_impossible (μ / ν) (fun h => hne (_root_.div_eq_one.mp h))
    a n hcop f ?_ z hz hcard
  intro x
  let y : I → E := fun i => φ.symm ((ν⁻¹ : Eˣ) * x i)
  have hv := (hμ y).trans (hν y).symm
  have hn : (fun i => (ν : E) * φ (y i)) = x := by
    funext i
    simp only [y, RingEquiv.apply_symm_apply, ← mul_assoc, Units.val_inv_eq_inv_val,
      mul_inv_cancel₀ (Units.ne_zero ν), one_mul]
  have hm : (fun i => (μ : E) * φ (y i)) = fun i => ((μ / ν : Eˣ) : E) * x i := by
    funext i
    simp only [y, RingEquiv.apply_symm_apply, div_eq_mul_inv, Units.val_mul,
      Units.val_inv_eq_inv_val, mul_assoc]
  rwa [hm, hn] at hv

omit [Field E] [Finite E] in
theorem extension_card_coprime (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hE : Nat.card E = a ^ d) : Nat.Coprime (Nat.card E - 1) a := by
  rw [hE]
  have hc : Nat.Coprime (a ^ d - 1) (a ^ d) :=
    (Nat.coprime_self_sub_left (Nat.one_le_pow _ _ ha)).mpr (Nat.coprime_one_left _)
  exact hc.of_dvd_right (dvd_pow_self a (Nat.ne_of_gt hd))

end SharedDecoders

import SharedDecoders.CompositionChannels
import SharedDecoders.CompositionRecurrence

/-!
# A coordinate bound for polynomial kernels on cyclic channels

A monic degree-`k` recurrence sampled with positive step `s` is determined by
its first `k*s` positions. This supplies the kernel bound needed by the robust
composition argument without diagonalizing the cyclic operator.
-/

namespace SharedDecoders

open Module
open scoped BigOperators

variable {F A I : Type*} [Field F] [AddCommGroup A] [Module F A]
  {d : ℕ} [NeZero d]

theorem polynomial_channel_zero_of_prefix {k s : ℕ} (hs : 0 < s)
    (coeff : Fin (k + 1) → F) (hmonic : coeff (Fin.last k) = 1)
    (x : I → ZMod d → A)
    (hx : boundedPolynomial (channelRotation (F := F) (s : ZMod d)) coeff x = 0)
    (hz : ∀ i (j : ℕ), j < k * s → x i (j : ZMod d) = 0) : x = 0 := by
  have hn : ∀ n : ℕ, ∀ i, x i (n : ZMod d) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i
      by_cases hnk : n < k * s
      · exact hz i n hnk
      · have hle : k * s ≤ n := by omega
        have he := congrFun (congrFun hx i) ((n - k * s : ℕ) : ZMod d)
        simp only [boundedPolynomial, LinearMap.sum_apply, LinearMap.smul_apply,
          Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at he
        simp_rw [channelRotation_pow] at he
        change (∑ t : Fin (k + 1), coeff t •
          x i (((n - k * s : ℕ) : ZMod d) + (t.val : ZMod d) * (s : ZMod d))) = 0 at he
        rw [Fin.sum_univ_castSucc] at he
        have hsmall (t : Fin k) :
            x i (((n - k * s : ℕ) : ZMod d) + (t.castSucc.val : ZMod d) *
              (s : ZMod d)) = 0 := by
          have ht : n - k * s + t.val * s < n := by
            have hsum := Nat.sub_add_cancel hle
            have hlt := Nat.mul_lt_mul_of_pos_right t.isLt hs
            omega
          simpa [Nat.cast_add, Nat.cast_mul] using ih _ ht i
        simp_rw [hsmall, smul_zero] at he
        simp only [Finset.sum_const_zero, zero_add, hmonic, one_smul,
          Fin.val_last] at he
        have hcast : ((n - k * s : ℕ) : ZMod d) + (k : ZMod d) * (s : ZMod d) =
            (n : ZMod d) := by
          rw [← Nat.cast_mul, ← Nat.cast_add, Nat.sub_add_cancel hle]
        rwa [hcast] at he
  funext i j
  simpa using hn j.val i

def polynomialChannelRestriction (k s : ℕ) (coeff : Fin (k + 1) → F) :
    LinearMap.ker (boundedPolynomial
      (channelRotation (F := F) (I := I) (A := A) (d := d) (s : ZMod d)) coeff) →ₗ[F]
        (I → Fin (k * s) → A) where
  toFun x i j := x.val i (j.val : ZMod d)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem polynomialChannelRestriction_injective {k s : ℕ} (hs : 0 < s)
    (coeff : Fin (k + 1) → F) (hmonic : coeff (Fin.last k) = 1) :
    Function.Injective (polynomialChannelRestriction (F := F) (I := I) (A := A)
      (d := d) k s coeff) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply Subtype.ext
  apply polynomial_channel_zero_of_prefix hs coeff hmonic x.val x.property
  intro i j hj
  exact congrFun (congrFun hx i) ⟨j, hj⟩

theorem polynomial_channel_kernel_finrank_le [Fintype I] [FiniteDimensional F A]
    {k s : ℕ} (hs : 0 < s)
    (coeff : Fin (k + 1) → F) (hmonic : coeff (Fin.last k) = 1) :
    finrank F (LinearMap.ker (boundedPolynomial
      (channelRotation (F := F) (I := I) (A := A) (d := d) (s : ZMod d)) coeff)) ≤
        Fintype.card I * (k * s) * finrank F A := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (polynomialChannelRestriction_injective (F := F) (I := I) (A := A)
      (d := d) hs coeff hmonic)
  simpa [Module.finrank_pi_fintype, mul_assoc] using h

end SharedDecoders

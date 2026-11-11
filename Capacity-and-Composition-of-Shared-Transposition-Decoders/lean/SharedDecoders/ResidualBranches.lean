import SharedDecoders.ResidualReplay
import TransposeFollowup.ConditionalEntropyFibers

/-! Input-dependent branches retain their own complete baseline and kernel.
Only attained branches are counted; entropy averages the actual kernel budget. -/

namespace SharedDecoders

open Module Classical TransposeFollowup
open scoped BigOperators

variable {F V W Ω : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
  [Fintype F] [Fintype V] [Fintype Ω] [FiniteDimensional F V]

omit [Fintype Ω] in
theorem residual_branch_fiber_card_le (S : Set V) (A : Ω → V →ₗ[F] W)
    (z : V → Ω) (offset : Ω → W)
    (h : ∀ x ∈ S, A (z x) x = offset (z x)) (ω : Ω) :
    Nat.card {x : S // z x.1 = ω} ≤ Fintype.card F ^ finrank F (A ω).ker := by
  simpa only [Nat.card_eq_fintype_card] using
    equation_record_fiber_card_le S (A ω) z ω (offset ω)
      (fun x hx hz => by simpa only [hz] using h x hx)

theorem residual_branch_card_le (S : Set V) (A : Ω → V →ₗ[F] W)
    (z : V → Ω) (offset : Ω → W)
    (h : ∀ x ∈ S, A (z x) x = offset (z x)) :
    Nat.card S ≤ ∑ ω ∈ Finset.univ.filter (fun ω => ω ∈ z '' S),
      Fintype.card F ^ finrank F (A ω).ker := by
  have he : Nat.card S = ∑ ω : Ω, Nat.card {x : S // z x.1 = ω} := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv (fun x : S => z x.1)).symm
  rw [he, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro ω _
  split_ifs with hω
  · exact residual_branch_fiber_card_le S A z offset h ω
  · have : IsEmpty {x : S // z x.1 = ω} :=
      ⟨fun x => hω ⟨x.1.1, x.1.2, x.2⟩⟩
    simp only [Nat.card_of_isEmpty, le_refl]

theorem residual_branch_entropy_lower (S : Set V) (A : Ω → V →ₗ[F] W)
    (z : V → Ω) (offset : Ω → W)
    (h : ∀ x ∈ S, A (z x) x = offset (z x))
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) :
    entropy p - (∑ x, p x * (finrank F (A (z x.1)).ker : ℝ)) *
      Real.log (Fintype.card F) ≤ observationEntropy p (fun x : S => z x.1) := by
  have he := entropy_sub_mean_log_fiber_card_le_observationEntropy p hp
    (fun x : S => z x.1) (fun ω => Fintype.card F ^ finrank F (A ω).ker)
    (fun ω => by
      simpa only [Nat.card_eq_fintype_card] using residual_branch_fiber_card_le S A z offset h ω)
  simp only [Nat.cast_pow, Real.log_pow, ← mul_assoc, ← Finset.sum_mul] at he
  rw [show (∑ ω, helperMass p (fun x : S => z x.1) ω * (finrank F (A ω).ker : ℝ)) =
      ∑ x, p x * (finrank F (A (z x.1)).ker : ℝ) by
    exact sum_pushforward_mul p (fun x : S => z x.1) (fun ω => (finrank F (A ω).ker : ℝ))] at he
  exact he

end SharedDecoders

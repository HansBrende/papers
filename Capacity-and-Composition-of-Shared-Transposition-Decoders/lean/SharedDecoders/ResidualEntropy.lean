import SharedDecoders.ResidualReplay
import SharedDecoders.ResidualProgram
import SharedDecoders.ResidualSpan
import TransposeFollowup.ConditionalEntropyFibers
import TransposeFollowup.UniformEntropy

/-! Entropy invoices for one attained joint record and one propagated span.
Entropy is in natural logarithms; dividing by `log (card F)` gives base-`q`
entropy. A probability law on the correctness subtype is an arbitrary law
supported there, not a uniformity or linear-source assumption. -/

namespace SharedDecoders

open Module TransposeFollowup
open scoped BigOperators

variable {F V W Ω : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem residual_entropy_lower [Fintype F] [Fintype V] [Fintype Ω]
    [FiniteDimensional F V]
    (S : Set V) [Fintype S] (A : V →ₗ[F] W) (z : V → Ω)
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (h : ∀ x ∈ S, ∀ y ∈ S, z x = z y → A x = A y) :
    entropy p - (finrank F A.ker : ℝ) * Real.log (Fintype.card F) ≤
      observationEntropy p (fun x : S => z x.1) := by
  classical
  have he := entropy_sub_log_fiber_card_le_observationEntropy p hp hp1
    (fun x : S => z x.1) (Fintype.card F ^ finrank F A.ker)
    (fun ω => by
      simpa only [Nat.card_eq_fintype_card] using same_record_fiber_card_le S A z h ω)
  simpa only [Nat.cast_pow, Real.log_pow] using he

/-- Uniform correctness sets pay the log-cardinality deficit, without needing
to be linear or affine sets. -/
theorem residual_uniform_entropy_lower [Fintype F] [Fintype V] [Fintype Ω]
    [FiniteDimensional F V]
    (S : Set V) [Fintype S] [Nonempty S] (A : V →ₗ[F] W) (z : V → Ω)
    (h : ∀ x ∈ S, ∀ y ∈ S, z x = z y → A x = A y) :
    Real.log (Fintype.card S) - (finrank F A.ker : ℝ) * Real.log (Fintype.card F) ≤
      observationEntropy (uniformWeight S) (fun x : S => z x.1) := by
  simpa only [entropy_uniformWeight] using
    residual_entropy_lower S A z (uniformWeight S) (uniformWeight_nonneg S)
      (sum_uniformWeight S) h

/-- The entropy invoice for the actual nonlinear computation, with no separate
affine-equation certificate assumed. -/
theorem actual_correct_entropy_lower {Y : Type*} [AddCommGroup Y] [Module F Y]
    [Fintype F] [Fintype W] [Fintype Ω] [FiniteDimensional F W]
    (T : ℕ → V → V) (L : ℕ → V →ₗ[F] V) (g : ℕ → V)
    (J : W →ₗ[F] V) (j : V) (O : V →ₗ[F] Y) (o : Y) (n : ℕ)
    (τ : W →ₗ[F] Y) (S : Set W) [Fintype S] (z : W → Ω)
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hcorrect : ∀ x ∈ S, O (actualRun T J j x n) + o = τ x)
    (hrecord : ∀ x ∈ S, ∀ y ∈ S, z x = z y →
      ∀ i < n, actualResidual T L g J j i x = actualResidual T L g J j i y) :
    entropy p - (finrank F (τ - O.comp (residualLinearPart L J n)).ker : ℝ) *
      Real.log (Fintype.card F) ≤ observationEntropy p (fun x : S => z x.1) :=
  residual_entropy_lower S _ z p hp hp1
    (actual_correct_same_record T L g J j O o n τ S z hcorrect hrecord)

/-- The joint propagated span satisfies the same log-cardinality invoice;
its intersection with the baseline image can be retained for a sharper bound. -/
theorem residual_span_information [Fintype F] [Fintype V]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (S : Set V) [Fintype S] [Nonempty S]
    (A : V →ₗ[F] W) (U : Submodule F W) (c : W)
    (h : ∀ x ∈ S, A x - c ∈ U) :
    Real.log (Fintype.card S) - (finrank F A.ker : ℝ) * Real.log (Fintype.card F) ≤
      (finrank F (U ⊓ A.range : Submodule F W) : ℝ) * Real.log (Fintype.card F) := by
  have hc := residual_span_card_le S A U c h
  simp only [Nat.card_eq_fintype_card] at hc
  have hc' : (Fintype.card S : ℝ) ≤ (Fintype.card F : ℝ) ^
      (finrank F A.ker + finrank F (U ⊓ A.range : Submodule F W)) := by
    exact_mod_cast hc
  have hl := Real.log_le_log (by exact_mod_cast Fintype.card_pos (α := S)) hc'
  rw [Real.log_pow, Nat.cast_add, add_mul] at hl
  linarith

end SharedDecoders

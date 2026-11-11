import SharedDecoders.ResidualPropagation
import SharedDecoders.ResidualSpan

/-! The joint span formed from the actual insertion maps, with the complete
chronological replay as its source. No output-span membership is assumed. -/

namespace SharedDecoders

open Module
open scoped BigOperators

variable {F V W Y : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup Y] [Module F Y]
  {U : ℕ → Type*} [∀ i, AddCommGroup (U i)] [∀ i, Module F (U i)]

noncomputable def propagatedOutputSpan (L : ℕ → V →ₗ[F] V)
    (O : V →ₗ[F] Y) (E : ∀ i, U i →ₗ[F] V) (n : ℕ) : Submodule F Y :=
  ⨆ i : Fin n, ((O.comp (residualPropagation L n i)).comp (E i)).range

theorem actual_correct_mem_outputSpan
    (T : ℕ → V → V) (L : ℕ → V →ₗ[F] V) (g : ℕ → V)
    (J : W →ₗ[F] V) (j : V) (O : V →ₗ[F] Y) (o : Y)
    (E : ∀ i, U i →ₗ[F] V) (u : ∀ i, W → U i) (n : ℕ)
    (τ : W →ₗ[F] Y) (x : W)
    (he : ∀ i < n, actualResidual T L g J j i x = E i (u i x))
    (hcorrect : O (actualRun T J j x n) + o = τ x) :
    (τ - O.comp (residualLinearPart L J n)) x -
      (O (baselineOffset L g j n) + o) ∈ propagatedOutputSpan L O E n := by
  have hx := actual_readout_insertions T L g J j O o E u x n he
  rw [hcorrect] at hx
  have heq : (τ - O.comp (residualLinearPart L J n)) x -
      (O (baselineOffset L g j n) + o) =
        ∑ i ∈ Finset.range n,
          ((O.comp (residualPropagation L n i)).comp (E i)) (u i x) := by
    simp only [LinearMap.sub_apply]
    rw [hx]
    abel
  rw [heq]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.mem_iSup_of_mem (⟨i, Finset.mem_range.mp hi⟩ : Fin n) ⟨u i x, rfl⟩

/-- Correctness and the actual inserted residuals imply the sharp joint-span
cardinality bound, retaining its intersection with the baseline defect image. -/
theorem actual_correct_span_card_le [Finite F] [Finite W]
    [FiniteDimensional F W] [FiniteDimensional F Y]
    (T : ℕ → V → V) (L : ℕ → V →ₗ[F] V) (g : ℕ → V)
    (J : W →ₗ[F] V) (j : V) (O : V →ₗ[F] Y) (o : Y)
    (E : ∀ i, U i →ₗ[F] V) (u : ∀ i, W → U i) (n : ℕ)
    (τ : W →ₗ[F] Y) (S : Set W)
    (he : ∀ x ∈ S, ∀ i < n, actualResidual T L g J j i x = E i (u i x))
    (hcorrect : ∀ x ∈ S, O (actualRun T J j x n) + o = τ x) :
    Nat.card S ≤ Nat.card F ^
      (finrank F (τ - O.comp (residualLinearPart L J n)).ker +
       finrank F (propagatedOutputSpan L O E n ⊓
         (τ - O.comp (residualLinearPart L J n)).range : Submodule F Y)) :=
  residual_span_card_le S _ _ (O (baselineOffset L g j n) + o)
    (fun x hx => actual_correct_mem_outputSpan T L g J j O o E u n τ x
      (he x hx) (hcorrect x hx))

end SharedDecoders

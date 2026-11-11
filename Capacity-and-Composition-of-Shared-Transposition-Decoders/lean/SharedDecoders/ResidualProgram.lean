import SharedDecoders.ResidualReplay

/-! # Actual nonlinear updates replayed around a complete affine baseline -/

namespace SharedDecoders

variable {F V W Y : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup Y] [Module F Y]

def actualRun (T : ℕ → V → V) (J : W →ₗ[F] V) (j : V) (x : W) : ℕ → V
  | 0 => J x + j
  | n+1 => T n (actualRun T J j x n)

def actualResidual (T : ℕ → V → V) (L : ℕ → V →ₗ[F] V) (g : ℕ → V)
    (J : W →ₗ[F] V) (j : V) (n : ℕ) (x : W) : V :=
  T n (actualRun T J j x n) - (L n (actualRun T J j x n) + g n)

theorem actualRun_eq_residualRun (T : ℕ → V → V) (L : ℕ → V →ₗ[F] V)
    (g : ℕ → V) (J : W →ₗ[F] V) (j : V) (x : W) (n : ℕ) :
    actualRun T J j x n = residualRun L g J j (actualResidual T L g J j) x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [actualRun, residualRun, actualResidual, ← ih]
    abel

/-- Initialization, every actual update and the final affine readout are included. -/
theorem actual_readout_eq (T : ℕ → V → V) (L : ℕ → V →ₗ[F] V)
    (g : ℕ → V) (J : W →ₗ[F] V) (j : V) (O : V →ₗ[F] Y) (o : Y)
    (x : W) (n : ℕ) :
    O (actualRun T J j x n) + o =
      (O.comp (residualLinearPart L J n)) x +
        (O (residualOffset L g j (actualResidual T L g J j) x n) + o) := by
  rw [actualRun_eq_residualRun, residualRun_eq, map_add]
  simp only [LinearMap.comp_apply]
  abel

/-- Equal chronological residual records leave the same offset after readout. -/
theorem actual_readout_offset_eq (T : ℕ → V → V) (L : ℕ → V →ₗ[F] V)
    (g : ℕ → V) (J : W →ₗ[F] V) (j : V) (O : V →ₗ[F] Y) (o : Y)
    (x y : W) (n : ℕ)
    (h : ∀ i < n, actualResidual T L g J j i x = actualResidual T L g J j i y) :
    O (residualOffset L g j (actualResidual T L g J j) x n) + o =
      O (residualOffset L g j (actualResidual T L g J j) y n) + o := by
  rw [residualOffset_eq_of_records L g j (actualResidual T L g J j) x y n h]

/-- Equal joint records give equal complete-baseline defects on correct inputs. -/
theorem actual_correct_same_record {Ω : Type*}
    (T : ℕ → V → V) (L : ℕ → V →ₗ[F] V) (g : ℕ → V)
    (J : W →ₗ[F] V) (j : V) (O : V →ₗ[F] Y) (o : Y) (n : ℕ)
    (τ : W →ₗ[F] Y) (S : Set W) (z : W → Ω)
    (hcorrect : ∀ x ∈ S, O (actualRun T J j x n) + o = τ x)
    (hrecord : ∀ x ∈ S, ∀ y ∈ S, z x = z y →
      ∀ i < n, actualResidual T L g J j i x = actualResidual T L g J j i y) :
    ∀ x ∈ S, ∀ y ∈ S, z x = z y →
      (τ - O.comp (residualLinearPart L J n)) x =
        (τ - O.comp (residualLinearPart L J n)) y := by
  intro x hx y hy hxy
  have ex := actual_readout_eq T L g J j O o x n
  have ey := actual_readout_eq T L g J j O o y n
  rw [hcorrect x hx] at ex
  rw [hcorrect y hy] at ey
  have eo := actual_readout_offset_eq T L g J j O o x y n (hrecord x hx y hy hxy)
  simp only [LinearMap.sub_apply]
  rw [ex, ey, eo]
  abel


/-- The attained joint record bounds the correctness set for the complete
program. The record need only determine its actual residuals on correct inputs;
it can include input-dependent choices and take values in any type. -/
theorem actual_correct_card_le {Ω : Type*}
    [Finite F] [Finite W] [FiniteDimensional F W]
    (T : ℕ → V → V) (L : ℕ → V →ₗ[F] V) (g : ℕ → V)
    (J : W →ₗ[F] V) (j : V) (O : V →ₗ[F] Y) (o : Y) (n : ℕ)
    (τ : W →ₗ[F] Y) (S : Set W) (z : W → Ω)
    (hcorrect : ∀ x ∈ S, O (actualRun T J j x n) + o = τ x)
    (hrecord : ∀ x ∈ S, ∀ y ∈ S, z x = z y →
      ∀ i < n, actualResidual T L g J j i x = actualResidual T L g J j i y) :
    Nat.card S ≤ Nat.card (z '' S) *
      Nat.card F ^ Module.finrank F (τ - O.comp (residualLinearPart L J n)).ker :=
  same_record_card_le S _ z
    (actual_correct_same_record T L g J j O o n τ S z hcorrect hrecord)

end SharedDecoders

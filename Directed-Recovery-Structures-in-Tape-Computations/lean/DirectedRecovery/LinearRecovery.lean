import LeanMachine.LinearRecovery
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Linear storage spaces and finite matrix witnesses

These results prove the finite algebraic implication behind the appendix's
linear-code corollary. A linear storage space has a supported linear recovery
matrix even if its original decoders are nonlinear. Full-rank matched labels,
rank-one incidence labels, and a degree bound then imply the claimed rate.

The existence and expansion of the particular graph family in the manuscript
are separate hypotheses and are not established by this file.
-/

open Module

namespace DirectedRecovery

/-- Nonlinear determination on a linear storage space admits a linear recovery
matrix with exactly the prescribed directed block support. -/
theorem linear_recovery_matrix_exists {F : Type*} [Field F] {N t : ℕ}
    (E : Fin N → Fin N → Prop) [DecidableRel E]
    (C : Submodule F ((Fin N × Fin t) → F))
    (hC : LeanMachine.LinearRecovery.IsBlockRecoverable E C) :
    ∃ A : Matrix (Fin N × Fin t) (Fin N × Fin t) F,
      (∀ q p, ¬ E p q → A.submatrix (Prod.mk q) (Prod.mk p) = 0) ∧
      C ≤ LinearMap.ker (1 - A).mulVecLin :=
  hC.exists_recovery_matrix

/-- The appendix's linear-code rate bound follows from its finite matrix-label
witnesses. Witnesses may lie in any extension field; the code dimension is over
the original field and the bound is uniform in its block width `t`. -/
theorem linear_code_rate_of_matrix_labels {F K : Type*} [Field F] [Field K]
    {N t m : ℕ} (hN : 0 < N) (ht : 0 < t) (hm : 0 < m)
    (f : F →+* K) (E : Fin N → Fin N → Prop) [DecidableRel E]
    (C : Submodule F ((Fin N × Fin t) → F))
    (hC : LeanMachine.LinearRecovery.IsBlockRecoverable E C)
    (X Y : Fin N → Matrix (Fin m) (Fin m) K) (Δ : ℕ)
    (hmatch : ∀ p, (X p - Y p).rank = m)
    (hedge : ∀ p q, E p q → (X p - Y q).rank ≤ 1)
    (hdegree : ∀ q, (Finset.univ.filter (fun p => E p q)).card ≤ Δ) :
    (finrank F C : ℝ) / ((N : ℝ) * (t : ℝ)) ≤
      1 / 2 + (Δ : ℝ) / (2 * (m : ℝ)) := by
  have h := hC.finrank_bound_of_matrix_labels f X Y Δ 1
    (by simpa only [Fintype.card_fin] using hmatch) hedge hdegree
  simp only [Fintype.card_fin, Nat.mul_one] at h
  have hreal : 2 * (m : ℝ) * (finrank F C : ℝ) ≤
      (N : ℝ) * (t : ℝ) * ((m : ℝ) + (Δ : ℝ)) := by exact_mod_cast h
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) * (t : ℝ))).mpr
  apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).mp
  calc
    _ ≤ (N : ℝ) * (t : ℝ) * ((m : ℝ) + (Δ : ℝ)) := hreal
    _ = 2 * (m : ℝ) * ((1 / 2 + (Δ : ℝ) / (2 * (m : ℝ))) *
        ((N : ℝ) * (t : ℝ))) := by
      have hmR : (m : ℝ) ≠ 0 := by positivity
      field_simp

end DirectedRecovery

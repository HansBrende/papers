import AboveHalfRate.Undirected
import LeanMachine.LinearRecovery

/-! # The explicit seed hypothesis for odd-majority amplification

This file does not construct an above-half-rate family. Its structure records
the precise finite-field, growing-size, bounded-degree, long-odd-walk and
linear-storage inputs supplied on paper by Corollary U(a,b) of Paper 13.
That paper's arithmetic seed existence is not formalized.

The conversion from these inputs to supported recovery matrices is formalized
here by reusing `LeanMachine.LinearRecovery`. Neither a rate above one half nor
odd characteristic is needed for this conversion; those are separate inputs to
the amplification theorem.
-/

namespace TapeStorageRates

open Filter MotionDepthCodes

set_option autoImplicit false

open Classical in
/-- A fixed-degree family of linear storage codes with growing coordinate sets
and no bounded-length odd closed walks eventually. Existence is an explicit
hypothesis, separate from every subsequent amplification theorem. -/
structure OddGirthLinearSeed (F : Type) [Field F] [Fintype F] (D : ℕ) (ρ : ℝ) where
  size : ℕ → ℕ
  growing : Tendsto size atTop atTop
  graph : (j : ℕ) → SimpleGraph (Fin (size j))
  code : (j : ℕ) → Submodule F (Fin (size j) → F)
  degree : ∀ j v, (graph j).degree v ≤ D
  long_odd : ∀ K : ℕ, ∀ᶠ j in atTop,
    ∀ v (w : (graph j).Walk v v), Odd w.length → K < w.length
  storage : ∀ j, IsStorageCode (nbhd (graph j)) (AboveHalf.wordsOf (code j))
  dimension : ∀ j, ρ * (size j : ℝ) ≤ Module.finrank F (code j)

namespace OddGirthLinearSeed

variable {F : Type} [Field F] [Fintype F] {D : ℕ} {ρ : ℝ}
variable (S : OddGirthLinearSeed F D ρ)

/-- Positive lengths follow eventually from growth; they are not an additional
seed hypothesis. -/
theorem eventually_size_pos : ∀ᶠ j in atTop, 0 < S.size j :=
  S.growing.eventually_gt_atTop 0

open Classical in
/-- Original-coordinate determination on each seed code is the existing
linear-recovery predicate, even if no linear decoder was initially supplied. -/
theorem recoverable (j : ℕ) :
    LeanMachine.LinearRecovery.IsRecoverable
      (fun p q => (S.graph j).Adj q p) (S.code j) := by
  intro q x hx y hy hagree
  apply S.storage j x (AboveHalf.mem_wordsOf.mpr hx)
    y (AboveHalf.mem_wordsOf.mpr hy) q
  intro p hp
  exact hagree p (Finset.mem_filter.mp hp).2

open Classical in
/-- A supported matrix fixes the entire seed code. This is the finite algebraic
adapter, not a proof that the seed family exists. -/
theorem exists_recovery_matrix (j : ℕ) :
    ∃ A : Matrix (Fin (S.size j)) (Fin (S.size j)) F,
      (∀ q p, ¬ (S.graph j).Adj q p → A q p = 0) ∧
      S.code j ≤ LinearMap.ker (1 - A).mulVecLin :=
  (S.recoverable j).exists_recovery_matrix

/-- Choose one supported recovery matrix at each level. This is an existence
construction and makes no claim about coefficient-generation time. -/
noncomputable def recoveryMatrix (j : ℕ) :
    Matrix (Fin (S.size j)) (Fin (S.size j)) F :=
  Classical.choose (S.exists_recovery_matrix j)

theorem recoveryMatrix_supported (j : ℕ) (q p : Fin (S.size j))
    (h : ¬ (S.graph j).Adj q p) : S.recoveryMatrix j q p = 0 :=
  (Classical.choose_spec (S.exists_recovery_matrix j)).1 q p h

theorem recoveryMatrix_diagonal (j : ℕ) (q : Fin (S.size j)) :
    S.recoveryMatrix j q q = 0 :=
  S.recoveryMatrix_supported j q q ((S.graph j).loopless.irrefl q)

theorem code_le_kernel (j : ℕ) :
    S.code j ≤ LinearMap.ker (1 - S.recoveryMatrix j).mulVecLin :=
  (Classical.choose_spec (S.exists_recovery_matrix j)).2

/-- The entire seed dimension survives in the fixed space of the recovery
matrix. -/
theorem dimension_le_kernel (j : ℕ) :
    ρ * (S.size j : ℝ) ≤
      Module.finrank F (LinearMap.ker (1 - S.recoveryMatrix j).mulVecLin) :=
  (S.dimension j).trans (Nat.cast_le.mpr (Submodule.finrank_mono (S.code_le_kernel j)))

/-- A direct rank-nullity budget for the selected fitting matrix. -/
theorem finrank_add_check_rank_le (j : ℕ) :
    Module.finrank F (S.code j) + (1 - S.recoveryMatrix j).rank ≤ S.size j := by
  simpa only [Fintype.card_fin] using
    LeanMachine.LinearRecovery.finrank_add_rank_le (S.code j)
      (S.recoveryMatrix j) (S.code_le_kernel j)

end OddGirthLinearSeed

end TapeStorageRates

import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Whole-row recovery codes and the constraints exposed by an order of the rows. -/

namespace LeanMachine.WholeRow

open Module
open scoped Matrix

variable {F ι : Type*} [Field F] [Fintype ι]

/-- A column is recovered as the prescribed linear combination of its helper rows. -/
def rowCode (ρ : ι → Finset ι) (M : ι → ι → Matrix ι ι F) : Submodule F (Matrix ι ι F) where
  carrier := {X | ∀ r i, X i r = ∑ s ∈ ρ r, ∑ j, M r s i j * X s j}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY r i
    simp only [Matrix.add_apply, hX r i, hY r i, mul_add, Finset.sum_add_distrib]
  smul_mem' := by
    intro a X hX r i
    simp only [Matrix.smul_apply, smul_eq_mul, hX r i, Finset.mul_sum, mul_left_comm]

@[simp] theorem mem_rowCode {ρ : ι → Finset ι} {M : ι → ι → Matrix ι ι F} {X : Matrix ι ι F} :
    X ∈ rowCode ρ M ↔ ∀ r i, X i r = ∑ s ∈ ρ r, ∑ j, M r s i j * X s j := Iff.rfl

/-- Candidate row vectors: completed-column entries vanish, and every frontier
block vanishes on the already known rows. -/
def rowSpace (A B R : Finset ι) (M : ι → Matrix ι ι F) : Submodule F (ι → F) where
  carrier := {x | (∀ j ∈ B, x j = 0) ∧ ∀ r ∈ R, ∀ i ∈ A, (M r *ᵥ x) i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    constructor
    · intro j hj; simp [hx.1 j hj, hy.1 j hj]
    · intro r hr i hi
      simp [Matrix.mulVec_add, hx.2 r hr i hi, hy.2 r hr i hi]
  smul_mem' := by
    intro a x hx
    constructor
    · intro j hj; simp [hx.1 j hj]
    · intro r hr i hi
      simp [Matrix.mulVec_smul, hx.2 r hr i hi]

@[simp] theorem mem_rowSpace {A B R : Finset ι} {M : ι → Matrix ι ι F} {x : ι → F} :
    x ∈ rowSpace A B R M ↔
      (∀ j ∈ B, x j = 0) ∧ ∀ r ∈ R, ∀ i ∈ A, (M r *ᵥ x) i = 0 := Iff.rfl

/-- Vanishing helper rows force the corresponding column to vanish. -/
theorem column_zero_of_known {ρ : ι → Finset ι} {M : ι → ι → Matrix ι ι F}
    {X : Matrix ι ι F} (hX : X ∈ rowCode ρ M) {A : Finset ι}
    (hA : ∀ s ∈ A, X s = 0) {r : ι} (hr : ρ r ⊆ A) (i : ι) : X i r = 0 := by
  rw [hX r i]
  apply Finset.sum_eq_zero
  intro s hs
  simp [hA s (hr hs)]

/-- If all but one helper row vanish, only its block contributes to the column. -/
theorem column_eq_single_of_known [DecidableEq ι] {ρ : ι → Finset ι} {M : ι → ι → Matrix ι ι F}
    {X : Matrix ι ι F} (hX : X ∈ rowCode ρ M) {A : Finset ι}
    (hA : ∀ u ∈ A, X u = 0) {r s : ι} (hs : s ∈ ρ r) (hr : ρ r ⊆ insert s A) (i : ι) :
    X i r = (M r s *ᵥ X s) i := by
  classical
  rw [hX r i, Finset.sum_eq_single s]
  · rfl
  · intro u hu hus
    have huA : u ∈ A := (Finset.mem_insert.mp (hr hu)).resolve_left hus
    simp [hA u huA]
  · exact fun hn => (hn hs).elim

variable [LinearOrder ι]

/-- Rows strictly earlier than the current row in the prescribed order. -/
def known (σ : Equiv.Perm ι) (t : ι) : Finset ι :=
  (Finset.univ.filter fun u => u < t).image σ

/-- Columns all of whose helper rows are already known. -/
def complete (ρ : ι → Finset ι) (σ : Equiv.Perm ι) (t : ι) : Finset ι :=
  Finset.univ.filter fun r => ρ r ⊆ known σ t

/-- Columns whose only potentially unknown helper is the current row. -/
def frontier (ρ : ι → Finset ι) (σ : Equiv.Perm ι) (t : ι) : Finset ι :=
  Finset.univ.filter fun r => σ t ∈ ρ r ∧ ρ r ⊆ insert (σ t) (known σ t)

/-- The necessary linear constraints on the next row after earlier rows vanish. -/
def stepSpace (ρ : ι → Finset ι) (M : ι → ι → Matrix ι ι F) (σ : Equiv.Perm ι) (t : ι) :
    Submodule F (ι → F) :=
  rowSpace (known σ t) (complete ρ σ t) (frontier ρ σ t) (fun r => M r (σ t))

/-- The recovery equations imply all completed-column and frontier constraints. -/
theorem row_mem_stepSpace {ρ : ι → Finset ι} {M : ι → ι → Matrix ι ι F}
    (σ : Equiv.Perm ι) (t : ι) {X : Matrix ι ι F} (hX : X ∈ rowCode ρ M)
    (hpre : ∀ u, u < t → X (σ u) = 0) : X (σ t) ∈ stepSpace ρ M σ t := by
  have hA : ∀ s ∈ known σ t, X s = 0 := by
    intro s hs
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
    exact hpre u (Finset.mem_filter.mp hu).2
  constructor
  · intro r hr
    exact column_zero_of_known hX hA (Finset.mem_filter.mp hr).2 (σ t)
  · intro r hr i hi
    have hr' := (Finset.mem_filter.mp hr).2
    rw [← column_eq_single_of_known hX hA hr'.1 hr'.2 i]
    exact congrFun (hA i hi) r

end LeanMachine.WholeRow

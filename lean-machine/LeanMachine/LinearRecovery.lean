import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import LeanMachine.MatrixRankCertificate

/-!
# Linear recovery from arbitrary deterministic determination

On a linear subspace, any coordinate determined by specified coordinates
is a linear combination of them. The recovery relation may be directed,
may contain loops, and may act on blocks of arbitrary width. No linearity
of the originally supplied recovery functions is assumed.
-/

open Module
open scoped BigOperators

namespace LeanMachine.LinearRecovery

variable {F V : Type*} [Field F] [Fintype V]

/-- Equality on the prescribed input coordinates determines each output
coordinate on the subspace. An incidence `E p q` allows `p` to recover `q`. -/
def IsRecoverable (E : V → V → Prop) (C : Submodule F (V → F)) : Prop :=
  ∀ q, ∀ x ∈ C, ∀ y ∈ C, (∀ p, E p q → x p = y p) → x q = y q

/-- Arbitrary deterministic recovery on a linear subspace admits linear
coefficients with exactly the prescribed directed support. -/
theorem IsRecoverable.exists_coeffs {E : V → V → Prop} [DecidableRel E]
    {C : Submodule F (V → F)} (hC : IsRecoverable E C) (q : V) :
    ∃ d : V → F, (∀ p, ¬ E p q → d p = 0) ∧
      ∀ x ∈ C, x q = ∑ p, d p * x p := by
  let L : V → C →ₗ[F] F := fun p =>
    if E p q then (LinearMap.proj p).comp C.subtype else 0
  let K : C →ₗ[F] F := (LinearMap.proj q).comp C.subtype
  have h : ⨅ p, LinearMap.ker (L p) ≤ LinearMap.ker K := by
    intro x hx
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    refine hC q x x.property 0 C.zero_mem (fun p hp => ?_)
    simpa [L, hp] using hx p
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp
    (mem_span_of_iInf_ker_le_ker h)
  refine ⟨fun p => if E p q then d p else 0, fun p hp => by simp [hp], ?_⟩
  intro x hx
  have heq := congrArg (fun f => f ⟨x, hx⟩) hd
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    K, LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.proj_apply] at heq
  rw [← heq]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : E p q <;> simp [L, hp]

/-- There is an ambient linear recovery matrix with the prescribed support
which fixes every codeword. Thus the code lies in the kernel of `1 - A`. -/
theorem IsRecoverable.exists_recovery_matrix [DecidableEq V]
    {E : V → V → Prop} [DecidableRel E] {C : Submodule F (V → F)}
    (hC : IsRecoverable E C) :
    ∃ A : Matrix V V F, (∀ q p, ¬ E p q → A q p = 0) ∧
      C ≤ LinearMap.ker (1 - A).mulVecLin := by
  classical
  choose d hd0 hd using hC.exists_coeffs
  refine ⟨Matrix.of fun q p => d q p, hd0, ?_⟩
  intro x hx
  rw [LinearMap.mem_ker]
  ext q
  change ((1 : Matrix V V F) - Matrix.of (fun q p => d q p)).mulVec x q = 0
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact sub_eq_zero.mpr (hd q x hx)

/-- Rank-nullity bounds every subspace fixed by a recovery matrix. -/
theorem finrank_add_rank_le [DecidableEq V] (C : Submodule F (V → F))
    (A : Matrix V V F) (hC : C ≤ LinearMap.ker (1 - A).mulVecLin) :
    finrank F C + (1 - A).rank ≤ Fintype.card V := by
  have hle := Submodule.finrank_mono hC
  have hnull := (1 - A).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at hnull
  change (1 - A).rank + finrank F (LinearMap.ker (1 - A).mulVecLin) =
    Fintype.card V at hnull
  omega

section Blocks

variable {Q T : Type*} [Fintype Q] [Fintype T]

/-- Whole-block recovery, expressed on the flattened coordinate space.
Every lane in output block `q` is determined by every lane of its input blocks. -/
def IsBlockRecoverable (E : Q → Q → Prop)
    (C : Submodule F ((Q × T) → F)) : Prop :=
  IsRecoverable (fun p q : Q × T => E p.1 q.1) C

omit [Fintype Q] [Fintype T] in
/-- Arbitrary supplied block decoders imply the determination property.
The decoders have no algebraic hypotheses. -/
theorem isBlockRecoverable_of_decoder {E : Q → Q → Prop}
    (C : Submodule F ((Q × T) → F))
    (decode : (q : Q) → (({p // E p q}) → T → F) → T → F)
    (hdecode : ∀ x ∈ C, ∀ q i,
      decode q (fun p j => x (p.val, j)) i = x (q, i)) :
    IsBlockRecoverable E C := by
  intro qi x hx y hy hxy
  rw [← hdecode x hx qi.1 qi.2, ← hdecode y hy qi.1 qi.2]
  congr 1
  funext p j
  exact hxy (p.val, j) p.property

/-- Whole-block determination admits a block recovery matrix of the same width.
This includes initially nonlinear block recovery functions. -/
theorem IsBlockRecoverable.exists_recovery_matrix [DecidableEq Q] [DecidableEq T]
    {E : Q → Q → Prop} [DecidableRel E]
    {C : Submodule F ((Q × T) → F)} (hC : IsBlockRecoverable E C) :
    ∃ A : Matrix (Q × T) (Q × T) F,
      (∀ q p, ¬ E p q → A.submatrix (Prod.mk q) (Prod.mk p) = 0) ∧
      C ≤ LinearMap.ker (1 - A).mulVecLin := by
  obtain ⟨A, hA, hker⟩ := IsRecoverable.exists_recovery_matrix hC
  refine ⟨A, ?_, hker⟩
  intro q p hp
  ext i j
  exact hA (q, i) (p, j) hp

/-- Full-rank matched labels and low-rank incidence labels bound the dimension
of every linear storage space, even with initially nonlinear recovery.
The labels may be over an arbitrary field extension of the code field. -/
theorem IsBlockRecoverable.finrank_bound_of_matrix_labels
    [DecidableEq Q] [DecidableEq T] {K M : Type*} [Field K] [Fintype M]
    [DecidableEq M] (f : F →+* K)
    {E : Q → Q → Prop} [DecidableRel E]
    {C : Submodule F ((Q × T) → F)} (hC : IsBlockRecoverable E C)
    (X Y : Q → Matrix M M K) (Δ r : ℕ)
    (hmatch : ∀ p, (X p - Y p).rank = Fintype.card M)
    (hedge : ∀ p q, E p q → (X p - Y q).rank ≤ r)
    (hdegree : ∀ q, (Finset.univ.filter (fun p => E p q)).card ≤ Δ) :
    2 * Fintype.card M * finrank F C ≤
      Fintype.card Q * Fintype.card T * (Fintype.card M + Δ * r) := by
  obtain ⟨A, hA, hker⟩ := hC.exists_recovery_matrix
  have hcert := MatrixRankCertificate.supported_matrix_label_certificate_extension
    f E A hA X Y
  have hbudget := finrank_add_rank_le C A hker
  rw [Fintype.card_prod] at hbudget
  have hdefect : (∑ q, ∑ p ∈ Finset.univ.filter (fun p => E p q),
      (A.submatrix (Prod.mk q) (Prod.mk p)).rank * (X p - Y q).rank) ≤
      Fintype.card Q * (Fintype.card T * r * Δ) := by
    calc
      _ ≤ ∑ _q : Q, Fintype.card T * r * Δ := by
        apply Finset.sum_le_sum
        intro q _
        calc
          _ ≤ ∑ _p ∈ Finset.univ.filter (fun p => E p q), Fintype.card T * r := by
            apply Finset.sum_le_sum
            intro p hp
            exact Nat.mul_le_mul (Matrix.rank_le_card_width _)
              (hedge p q (Finset.mem_filter.mp hp).2)
          _ = (Fintype.card T * r) * (Finset.univ.filter (fun p => E p q)).card := by
            simp [Nat.mul_comm]
          _ ≤ _ := Nat.mul_le_mul_left _ (hdegree q)
      _ = _ := by simp [Nat.mul_comm]
  simp only [hmatch, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hcert
  nlinarith only [hcert, hbudget, hdefect]

end Blocks

end LeanMachine.LinearRecovery

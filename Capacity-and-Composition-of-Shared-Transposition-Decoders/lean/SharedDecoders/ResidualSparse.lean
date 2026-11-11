import SharedDecoders.ResidualProgram
import LeanMachine.SparseRecords
import LeanMachine.SparseBinomial

/-! Sparse corrections pay their joint support/value menu. Port alphabets and
dimensions may vary, and support selection can depend arbitrarily on the input. -/

namespace SharedDecoders

open Module Classical LeanMachine
open scoped BigOperators

variable {F V W I : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem residual_sparse_card_le [Fintype F] [Fintype V] [Fintype I]
    [FiniteDimensional F V] {U : I → Type*}
    [∀ i, AddCommGroup (U i)] [∀ i, Module F (U i)]
    [∀ i, Fintype (U i)] [∀ i, FiniteDimensional F (U i)]
    (S : Set V) (A : V →ₗ[F] W) (z : V → ∀ i, U i) (r s : ℕ)
    (hrank : ∀ i, finrank F (U i) ≤ r)
    (hsparse : ∀ x ∈ S, (recordSupport (fun _ => 0) (z x)).card ≤ s)
    (hrecord : ∀ x ∈ S, ∀ y ∈ S, z x = z y → A x = A y) :
    Nat.card S ≤ Fintype.card F ^ finrank F A.ker *
      ∑ j ∈ Finset.range (min s (Fintype.card I) + 1),
        (Fintype.card I).choose j * (Fintype.card F ^ r - 1) ^ j := by
  have hnz (i : I) : Fintype.card {a : U i // a ≠ 0} ≤ Fintype.card F ^ r - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    apply Nat.sub_le_sub_right
    have hc := Module.natCard_eq_pow_finrank (K := F) (V := U i)
    simp only [Nat.card_eq_fintype_card] at hc
    rw [hc]
    exact Nat.pow_le_pow_right (Fintype.card_pos (α := F)) (hrank i)
  have hs (x : V) (hx : x ∈ S) :
      (recordSupport (fun _ => 0) (z x)).card ≤ min s (Fintype.card I) :=
    le_min (hsparse x hx) (Finset.card_le_univ _)
  have hi : Nat.card (z '' S) ≤
      Nat.card {u : ∀ i, U i // (recordSupport (fun _ => 0) u).card ≤
        min s (Fintype.card I)} := by
    refine Nat.card_le_card_of_injective (fun u => ⟨u.1, ?_⟩) ?_
    · obtain ⟨x, hx, he⟩ := u.2
      simpa only [← he] using hs x hx
    · intro x y he
      have hv : (x.1 : ∀ i, U i) = y.1 := congrArg (fun u => u.1) he
      exact Subtype.ext hv
  have hc := sparse_record_card_le (fun i => (0 : U i))
    (Fintype.card F ^ r - 1) (min s (Fintype.card I)) hnz
  have hb := same_record_card_le S A z hrecord
  simp only [Nat.card_eq_fintype_card] at hb
  calc
    Nat.card S ≤ Nat.card (z '' S) * Fintype.card F ^ finrank F A.ker := by
      simpa only [Nat.card_eq_fintype_card] using hb
    _ ≤ _ := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (hi.trans hc)

/-- A residual in a port image is recorded by its value in that image. Values
outside the image receive a default; correctness hypotheses exclude that case
on the source being counted. -/
noncomputable def rangeRecord {U : Type*} [AddCommGroup U] [Module F U]
    (E : U →ₗ[F] V) (v : V) : E.range :=
  if h : v ∈ E.range then ⟨v, h⟩ else 0

theorem rangeRecord_val {U : Type*} [AddCommGroup U] [Module F U]
    (E : U →ₗ[F] V) (v : V) (h : v ∈ E.range) : (rangeRecord E v).val = v := by
  simp only [rangeRecord, dite_eq_left h]

/-- The advertised rank-of-port bound for the actual nonlinear program.
Only correct inputs must have their residuals in the displayed port images. -/
theorem actual_sparse_card_le {Y : Type*} [AddCommGroup Y] [Module F Y]
    [Fintype F] [Fintype V] [Fintype W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : ℕ → V → V) (L : ℕ → V →ₗ[F] V) (g : ℕ → V)
    (J : W →ₗ[F] V) (j : V) (O : V →ₗ[F] Y) (o : Y) (n : ℕ)
    {U : Fin n → Type*} [∀ i, AddCommGroup (U i)] [∀ i, Module F (U i)]
    (E : ∀ i, U i →ₗ[F] V) (τ : W →ₗ[F] Y) (S : Set W) (r s : ℕ)
    (hrank : ∀ i, finrank F (E i).range ≤ r)
    (hports : ∀ x ∈ S, ∀ i : Fin n, actualResidual T L g J j i x ∈ (E i).range)
    (hsparse : ∀ x ∈ S, (recordSupport (fun _ : Fin n => (0 : V))
      (fun i => actualResidual T L g J j i x)).card ≤ s)
    (hcorrect : ∀ x ∈ S, O (actualRun T J j x n) + o = τ x) :
    Nat.card S ≤ Fintype.card F ^
      finrank F (τ - O.comp (residualLinearPart L J n)).ker *
        ∑ k ∈ Finset.range (min s n + 1), n.choose k * (Fintype.card F ^ r - 1) ^ k := by
  let R (x : W) (i : Fin n) : (E i).range :=
    rangeRecord (E i) (actualResidual T L g J j i x)
  let (i : Fin n) : Fintype (E i).range := Fintype.ofFinite _
  have hs (x : W) (hx : x ∈ S) : (recordSupport (fun i => (0 : (E i).range)) (R x)).card ≤ s := by
    have he : recordSupport (fun i => (0 : (E i).range)) (R x) =
        recordSupport (fun _ : Fin n => (0 : V)) (fun i => actualResidual T L g J j i x) := by
      ext i
      simp only [mem_recordSupport]
      have hv := rangeRecord_val (E i) (actualResidual T L g J j i x) (hports x hx i)
      have heq : R x i = 0 ↔ actualResidual T L g J j i x = 0 := by
        constructor
        · intro h
          exact hv.symm.trans (congrArg Subtype.val h)
        · intro h
          apply Subtype.ext
          exact hv.trans h
      exact heq.not
    rw [he]
    exact hsparse x hx
  have hrecord := actual_correct_same_record T L g J j O o n τ S R hcorrect
    (by
      intro x hx y hy hxy i hi
      have hv := congrArg (fun z => (z (⟨i, hi⟩ : Fin n)).val) hxy
      simpa only [R, rangeRecord_val _ _ (hports x hx _),
        rangeRecord_val _ _ (hports y hy _)] using hv)
  simpa only [Fintype.card_fin] using
    residual_sparse_card_le S _ R r s hrank hs hrecord

end SharedDecoders

import SharedDecoders.ResidualSeparable

/-! # Diagonal sharpness of the separable rank defect -/

namespace SharedDecoders.Separable

open Matrix Module
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] {d r : ℕ}

/-- The literal diagonal matrix `diag(I_r,0)` in the ambient `d`-square. -/
def initialProjection (d r : ℕ) : Matrix (Fin d) (Fin d) F :=
  Matrix.diagonal (fun i => if i.val < r then 1 else 0)

theorem projected_entry (X : Matrix (Fin d) (Fin d) F) (i j : Fin d) :
    baseline (initialProjection (F := F) d r) (initialProjection (F := F) d r) X i j =
      if i.val < r ∧ j.val < r then X i j else 0 := by
  by_cases hi : i.val < r <;> by_cases hj : j.val < r <;>
    simp [baseline, initialProjection, Matrix.diagonal_mul, Matrix.mul_diagonal, hi, hj]

theorem projection_kernel_iff (X : Matrix (Fin d) (Fin d) F) :
    X ∈ (defect (initialProjection (F := F) d r) (initialProjection (F := F) d r)).ker ↔
      (∀ i j, X i j = X j i) ∧ (∀ i j, ¬(i.val < r ∧ j.val < r) → X i j = 0) := by
  have he : X ∈ (defect (initialProjection (F := F) d r) (initialProjection (F := F) d r)).ker ↔
      ∀ i j, X j i = if i.val < r ∧ j.val < r then X i j else 0 := by
    rw [LinearMap.mem_ker, defect, LinearMap.sub_apply, sub_eq_zero]
    change X.transpose = _ ↔ _
    rw [← Matrix.ext_iff]
    simp only [Matrix.transpose_apply, projected_entry]
  rw [he]
  constructor
  · intro h
    have hz (i j : Fin d) (hij : ¬(i.val < r ∧ j.val < r)) : X i j = 0 := by
      have hh := h j i
      simpa only [and_comm, ite_eq_right hij] using hh
    refine ⟨?_, hz⟩
    intro i j
    by_cases hij : i.val < r ∧ j.val < r
    · simpa only [ite_eq_left hij] using (h i j).symm
    · rw [hz i j hij, hz j i (by simpa only [and_comm] using hij)]
  · rintro ⟨hs, hz⟩ i j
    by_cases hij : i.val < r ∧ j.val < r
    · simpa only [ite_eq_left hij] using hs j i
    · rw [ite_eq_right hij]
      exact hz j i (by simpa only [and_comm] using hij)

/-- Every unordered pair of active coordinates is an independent kernel coordinate. -/
def embedSymmetric (_hr : r ≤ d) :
    (Sym2 (Fin r) → F) →ₗ[F] Matrix (Fin d) (Fin d) F where
  toFun f := Matrix.of (fun i j => if hi : i.val < r then
    if hj : j.val < r then f s(⟨i.val, hi⟩, ⟨j.val, hj⟩) else 0 else 0)
  map_add' f g := by
    funext i j
    simp only [Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
    split_ifs <;> simp_all
  map_smul' a f := by
    funext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply]
    split_ifs <;> simp_all

@[simp] theorem embedSymmetric_apply (hr : r ≤ d) (f : Sym2 (Fin r) → F) (i j : Fin d) :
    embedSymmetric hr f i j = if hi : i.val < r then
      if hj : j.val < r then f s(⟨i.val, hi⟩, ⟨j.val, hj⟩) else 0 else 0 := rfl

theorem embedSymmetric_injective (hr : r ≤ d) : Function.Injective (embedSymmetric (F := F) hr) := by
  intro f g h
  funext z
  induction z using Sym2.ind with
  | _ i j =>
    have hh := congrFun (congrFun h (Fin.castLE hr i)) (Fin.castLE hr j)
    simpa [embedSymmetric_apply, i.isLt, j.isLt] using hh

theorem range_embedSymmetric (hr : r ≤ d) :
    (embedSymmetric (F := F) hr).range =
      (defect (initialProjection (F := F) d r) (initialProjection (F := F) d r)).ker := by
  ext X
  rw [LinearMap.mem_range, projection_kernel_iff]
  constructor
  · rintro ⟨f, rfl⟩
    constructor
    · intro i j
      by_cases hi : i.val < r <;> by_cases hj : j.val < r <;>
        simp [embedSymmetric_apply, hi, hj, Sym2.eq_swap]
    · intro i j hij
      by_cases hi : i.val < r <;> by_cases hj : j.val < r <;>
        simp_all [embedSymmetric_apply]
  · rintro ⟨hs, hz⟩
    let f : Sym2 (Fin r) → F := Sym2.lift ⟨fun i j => X (Fin.castLE hr i) (Fin.castLE hr j),
      fun i j => hs _ _⟩
    refine ⟨f, ?_⟩
    funext i j
    by_cases hi : i.val < r <;> by_cases hj : j.val < r
    · simp only [embedSymmetric_apply,
        dite_eq_left hi, dite_eq_left hj, f, Sym2.lift_mk]
      rfl
    · have hzero := hz i j (by simp [hj])
      simp [embedSymmetric_apply, hi, hj, hzero]
    · have hzero := hz i j (by simp [hi])
      simp [embedSymmetric_apply, hi, hzero]
    · have hzero := hz i j (by simp [hi])
      simp [embedSymmetric_apply, hi, hzero]

theorem projection_kernel_finrank (hr : r ≤ d) :
    finrank F (defect (initialProjection (F := F) d r) (initialProjection (F := F) d r)).ker = r * (r + 1) / 2 := by
  rw [← range_embedSymmetric hr, LinearMap.finrank_range_of_inj (embedSymmetric_injective hr),
    Module.finrank_fintype_fun_eq_card, RowColumn.sym2_card]

theorem initialProjection_rank (hr : r ≤ d) : (initialProjection (F := F) d r).rank = r := by
  classical
  rw [initialProjection, Matrix.rank_diagonal]
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
  exact Fintype.card_fin_lt_of_le hr

/-- Equality is attained at every rank, in every characteristic. -/
theorem rank_defect_sharp (hr : r ≤ d) :
    finrank F (defect (initialProjection (F := F) d r) (initialProjection (F := F) d r)).range =
      d * d - r * (r + 1) / 2 := by
  have hn := (defect (initialProjection (F := F) d r) (initialProjection (F := F) d r)).finrank_range_add_finrank_ker
  rw [projection_kernel_finrank hr] at hn
  simp only [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at hn
  omega

end SharedDecoders.Separable

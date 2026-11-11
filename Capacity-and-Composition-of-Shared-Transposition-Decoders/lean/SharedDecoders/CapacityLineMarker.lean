import SharedDecoders.CapacitySetConsistency
import SwapRigidity.Line
import Mathlib.Logic.Equiv.Prod
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! # Actual zero-padded line views and a high-density marker code -/

namespace SharedDecoders.LineMarker

attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d] {A : Type*} [Zero A]

abbrev Matrix (d : ℕ) (A : Type*) := Fin d → Fin d → A

/-- The full integer-offset view, defined for a completely arbitrary pointed alphabet. -/
def view (c : Fin d) (X : Matrix d A) : Fin d → ℤ → A := fun i e =>
  if h : 0 ≤ e + c.val ∧ e + c.val < d then
    X i ⟨(e + c.val).toNat, by omega⟩ else 0

omit [NeZero d] in
@[simp] theorem view_entry (c : Fin d) (X : Matrix d A) (i j : Fin d) :
    view c X i (j.val - c.val) = X i j := by
  have h : 0 ≤ (j.val : ℤ) - c.val + c.val ∧ (j.val : ℤ) - c.val + c.val < d := by
    have := j.isLt
    omega
  simp only [view, dite_eq_left h]
  congr 1
  apply Fin.ext
  change ((j.val : ℤ) - c.val + c.val).toNat = j.val
  omega

omit [NeZero d] in
@[simp] theorem view_zero (c : Fin d) : view c (0 : Matrix d A) = 0 := by
  funext i e
  unfold view
  split_ifs <;> rfl

omit [NeZero d] in
theorem view_injective (c : Fin d) : Function.Injective (view (A := A) c) := by
  intro X Y h
  funext i j
  simpa only [view_entry] using congrFun (congrFun h i) (j.val - c.val)

def firstColumn (X : Matrix d A) : Fin d → A := fun i => X i 0

def Code : Set (Matrix d A) := {X | firstColumn X ≠ 0 ∨ X = 0}

/-- A nonzero first column exposes the exact left boundary of the complete view. -/
theorem receiver_le_of_equal_views {X Y : Matrix d A} {c e : Fin d}
    (hX : firstColumn X ≠ 0) (h : view c X = view e Y) : c.val ≤ e.val := by
  obtain ⟨i, hi⟩ : ∃ i, X i 0 ≠ 0 := by
    by_contra hh
    apply hX
    funext i
    by_contra hi
    exact hh ⟨i, hi⟩
  by_contra hle
  have hlt : e.val < c.val := by omega
  have hv := congrFun (congrFun h i) (-(c.val : ℤ))
  have hz : ¬ (0 ≤ -(c.val : ℤ) + e.val ∧ -(c.val : ℤ) + e.val < d) := by omega
  have hleft : view c X i (-(c.val : ℤ)) = X i 0 := by
    simpa using view_entry c X i (0 : Fin d)
  rw [hleft] at hv
  simp only [view, dite_eq_right hz] at hv
  exact hi hv

theorem marked_equal_views {X Y : Matrix d A} {c e : Fin d}
    (hX : firstColumn X ≠ 0) (hY : firstColumn Y ≠ 0) (h : view c X = view e Y) :
    c = e ∧ X = Y := by
  have hce : c = e := Fin.ext (Nat.le_antisymm
    (receiver_le_of_equal_views hX h) (receiver_le_of_equal_views hY h.symm))
  subst e
  exact ⟨rfl, view_injective c h⟩

/-- One total decoder handles all marked matrices and the zero matrix simultaneously. -/
theorem exists_decoder :
    ∃ f : (Fin d → ℤ → A) → (Fin d → A),
      ∀ X ∈ Code (d := d) (A := A), ∀ c, f (view c X) = X c := by
  apply (exists_decoder_iff_consistent Code view (fun c X => X c)).mpr
  intro X hX Y hY c e hv
  rcases hX with hX | rfl
  · rcases hY with hY | rfl
    · obtain ⟨rfl, rfl⟩ := marked_equal_views hX hY hv
      rfl
    · have hx0 : X = 0 := view_injective c (by simpa only [view_zero] using hv)
      simp [hx0]
  · have hy0 : Y = 0 := view_injective e (by simpa only [view_zero] using hv.symm)
    simp [hy0]

omit [NeZero d] in
/-- This generic alphabet view is literally the established linear line-view interface. -/
theorem view_eq_lineView {F : Type*} [Field F] (c : Fin d) (X : Matrix d F) :
    view c X = SwapRigidity.lineView (c.val : ℤ) X := rfl

/-- Splitting off the first physical column leaves all remaining columns free. -/
noncomputable def columnsEquiv : Matrix d A ≃
    (Fin d → A) × ({j : Fin d // j ≠ 0} → Fin d → A) :=
  (Equiv.piComm (fun _ _ : Fin d => A)).trans (Equiv.funSplitAt 0 (Fin d → A))

noncomputable def markedEquiv : {X : Matrix d A // firstColumn X ≠ 0} ≃
    {v : Fin d → A // v ≠ 0} × ({j : Fin d // j ≠ 0} → Fin d → A) where
  toFun X := (⟨(columnsEquiv X.val).1, X.property⟩, (columnsEquiv X.val).2)
  invFun p := ⟨columnsEquiv.symm (p.1.val, p.2), by
    change (columnsEquiv (columnsEquiv.symm (p.1.val, p.2))).1 ≠ 0
    simpa only [Equiv.apply_symm_apply] using p.1.property⟩
  left_inv X := Subtype.ext (columnsEquiv.symm_apply_apply X.val)
  right_inv p := by
    have h := columnsEquiv.apply_symm_apply (p.1.val, p.2)
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · change (columnsEquiv (columnsEquiv.symm (p.1.val, p.2))).2 = p.2
      exact congrArg (fun z : (Fin d → A) × ({j : Fin d // j ≠ 0} → Fin d → A) => z.2) h

theorem marked_card [Fintype A] :
    Nat.card {X : Matrix d A // firstColumn X ≠ 0} =
      (Fintype.card A ^ d - 1) * Fintype.card A ^ (d * (d - 1)) := by
  classical
  rw [Nat.card_congr markedEquiv, Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    Fintype.card_fun, Fintype.card_fin, ← pow_mul]

/-- Exact cardinal of the proposed line correctness set. -/
theorem code_card [Fintype A] :
    Nat.card (Code (d := d) (A := A)) =
      (Fintype.card A ^ d - 1) * Fintype.card A ^ (d * (d - 1)) + 1 := by
  classical
  have he : Code (d := d) (A := A) = {X | firstColumn X ≠ 0} ∪ {0} := rfl
  have hdj : Disjoint {X : Matrix d A | firstColumn X ≠ 0} {0} := by
    rw [Set.disjoint_singleton_right]
    exact fun h => h rfl
  rw [Nat.card_coe_set_eq, he, Set.ncard_union_eq hdj, Set.ncard_singleton]
  change Nat.card {X : Matrix d A // firstColumn X ≠ 0} + 1 = _
  rw [marked_card]

section Field
variable {F : Type*} [Field F]

def entry00 : Matrix d F →ₗ[F] F where
  toFun X := X 0 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def affineMarker : AffineSubspace F (Matrix d F) :=
  AffineSubspace.mk' (fun _ _ => 1) (entry00 (d := d) (F := F)).ker

@[simp] theorem mem_affineMarker (X : Matrix d F) : X ∈ affineMarker (d := d) (F := F) ↔ X 0 0 = 1 := by
  simp [affineMarker, AffineSubspace.mem_mk', LinearMap.mem_ker, entry00, sub_eq_zero]

theorem affineMarker_subset_code : (affineMarker (d := d) (F := F) : Set (Matrix d F)) ⊆ Code := by
  intro X hX
  left
  intro hz
  have h := congrFun hz (0 : Fin d)
  change X 0 0 = 0 at h
  rw [(mem_affineMarker X).mp hX] at h
  exact one_ne_zero h

/-- The displayed affine slice has the claimed actual direction dimension. -/
theorem affineMarker_finrank :
    Module.finrank F (affineMarker (d := d) (F := F)).direction = d * d - 1 := by
  rw [affineMarker, AffineSubspace.direction_mk']
  have hr : (entry00 (d := d) (F := F)).range = ⊤ := LinearMap.range_eq_top.mpr
    (fun a => ⟨fun _ _ => a, rfl⟩)
  have h := (entry00 (d := d) (F := F)).finrank_range_add_finrank_ker
  rw [hr] at h
  simp only [Matrix, Module.finrank_pi_fintype, Module.finrank_self, finrank_top,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
  omega

theorem affineMarker_exceeds_half (hd : 3 ≤ d) :
    d * d + d < 2 * Module.finrank F (affineMarker (d := d) (F := F)).direction := by
  rw [affineMarker_finrank]
  have hdim : d * d - 1 + 1 = d * d := Nat.sub_add_cancel (by nlinarith)
  nlinarith

end Field
end SharedDecoders.LineMarker

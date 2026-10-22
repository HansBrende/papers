import TransposeFollowup.TriangularRows

/-! Public suffixes in arbitrary row orders, with exact finite cardinalities. -/

namespace TransposeFollowup

set_option autoImplicit false
open Classical

def rowSuffix {n : ℕ} (order : Equiv.Perm (Fin n)) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => n - r ≤ (order i).val)

@[simp] theorem mem_rowSuffix {n : ℕ} (order : Equiv.Perm (Fin n))
    (r : ℕ) (i : Fin n) : i ∈ rowSuffix order r ↔ n - r ≤ (order i).val := by
  simp [rowSuffix]

theorem rowSuffix_card {n r : ℕ} (order : Equiv.Perm (Fin n)) (hr : r ≤ n) :
    (rowSuffix order r).card = r := by
  have himage : (rowSuffix order r).image order = rowSuffix (Equiv.refl _) r := by
    ext i
    simp only [Finset.mem_image, mem_rowSuffix, Equiv.refl_apply]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hi
      exact ⟨order.symm i, by simpa using hi, order.apply_symm_apply i⟩
  have hcard : (rowSuffix order r).card = (rowSuffix (Equiv.refl (Fin n)) r).card := by
    rw [← himage, Finset.card_image_of_injective _ order.injective]
  rw [hcard]
  have he : rowSuffix (Equiv.refl (Fin n)) r =
      (Finset.univ.filter (fun i : Fin n => i.val < n - r))ᶜ := by
    ext i
    simp [not_lt]
  rw [he, Finset.card_compl, Fintype.card_fin, Fin.card_filter_val_lt, min_eq_right (Nat.sub_le _ _)]
  omega

theorem CausalRows.suffix_support {n : ℕ} {Q : Type*} (G : CausalRows n Q)
    (r : ℕ) {x y : Fin n → Q}
    (he : ∀ i ∉ rowSuffix G.order r, x i = y i) :
    ∀ i ∉ rowSuffix G.order r, G.apply x i = G.apply y i := by
  intro i hi
  apply G.prefix_eq
  intro j hj
  apply he
  simp only [mem_rowSuffix, not_le] at hi ⊢
  exact lt_of_le_of_lt hj hi

end TransposeFollowup

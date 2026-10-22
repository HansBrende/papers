import TransposeFollowup.MatchingExcursion

/-! Split a finite ordered bipartite edge set into monotone matchings by
map tag and endpoint residues. Bounded spans, not merely bounded degrees,
justify this particular explicit coloring. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

theorem eq_of_same_residue_close {a b M : ℕ} (hm : a % M = b % M)
    (hab : a < b + M) (hba : b < a + M) : a = b := by
  apply Nat.ModEq.eq_of_abs_lt hm
  rw [abs_lt]
  constructor <;> omega

structure ResidueMatchingInput {m : ℕ} (edges : Finset (Fin m × Fin m)) (c M : ℕ) where
  modulus_pos : 0 < M
  tag : edges → Fin c
  ordered : ∀ e f, tag e = tag f → e.val.1.val < f.val.1.val → e.val.2.val ≤ f.val.2.val
  row_span : ∀ e f, tag e = tag f → e.val.1 = f.val.1 → e.val.2.val < f.val.2.val + M
  column_span : ∀ e f, tag e = tag f → e.val.2 = f.val.2 → e.val.1.val < f.val.1.val + M

namespace ResidueMatchingInput

variable {m c M : ℕ} {edges : Finset (Fin m × Fin m)} (D : ResidueMatchingInput edges c M)

def color (e : edges) : Fin (c * (M * M)) :=
  finProdFinEquiv (D.tag e, finProdFinEquiv
    (⟨e.val.1.val % M, Nat.mod_lt _ D.modulus_pos⟩,
      ⟨e.val.2.val % M, Nat.mod_lt _ D.modulus_pos⟩))

theorem color_data {e f : edges} (h : D.color e = D.color f) :
    D.tag e = D.tag f ∧ e.val.1.val % M = f.val.1.val % M ∧
      e.val.2.val % M = f.val.2.val % M := by
  have hp := finProdFinEquiv.injective h
  have ht := congrArg Prod.fst hp
  have hr := finProdFinEquiv.injective (congrArg Prod.snd hp)
  exact ⟨ht, congrArg (fun p : Fin M × Fin M => p.1.val) hr,
    congrArg (fun p : Fin M × Fin M => p.2.val) hr⟩

theorem same_color_row_injective {e f : edges} (h : D.color e = D.color f)
    (he : e.val.1 = f.val.1) : e = f := by
  obtain ⟨htag, _, hmod⟩ := D.color_data h
  have hd : e.val.2 = f.val.2 := Fin.ext
    (eq_of_same_residue_close hmod (D.row_span e f htag he) (D.row_span f e htag.symm he.symm))
  exact Subtype.ext (Prod.ext he hd)

theorem same_color_column_injective {e f : edges} (h : D.color e = D.color f)
    (he : e.val.2 = f.val.2) : e = f := by
  obtain ⟨htag, hmod, _⟩ := D.color_data h
  have hs : e.val.1 = f.val.1 := Fin.ext
    (eq_of_same_residue_close hmod (D.column_span e f htag he)
      (D.column_span f e htag.symm he.symm))
  exact Subtype.ext (Prod.ext hs he)

theorem same_color_strict {e f : edges} (h : D.color e = D.color f)
    (he : e.val.1.val < f.val.1.val) : e.val.2.val < f.val.2.val := by
  have hle := D.ordered e f (D.color_data h).1 he
  have hne : e.val.2.val ≠ f.val.2.val := by
    intro hval
    have hef := D.same_color_column_injective h (Fin.ext hval)
    subst f
    exact lt_irrefl _ he
  omega

theorem same_color_order {e f : edges} (hne : e ≠ f) (h : D.color e = D.color f) :
    (e.val.1.val < f.val.1.val ∧ e.val.2.val < f.val.2.val) ∨
    (f.val.1.val < e.val.1.val ∧ f.val.2.val < e.val.2.val) := by
  have hs : e.val.1.val ≠ f.val.1.val := by
    intro he
    exact hne (D.same_color_row_injective h (Fin.ext he))
  rcases lt_or_gt_of_ne hs with ho | ho
  · exact Or.inl ⟨ho, D.same_color_strict h ho⟩
  · exact Or.inr ⟨ho, D.same_color_strict h.symm ho⟩

end ResidueMatchingInput
end TransposeFollowup

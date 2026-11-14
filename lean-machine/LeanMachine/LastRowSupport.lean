import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Finset.Card

/-!
# New columns after adjoining one spanning row

If old vectors vanish on a set of columns, adjoining one vector makes every
spanned vector proportional to that vector on those columns. For matrix rows
with nonzero diagonal, two such columns outside the adjoined row would force
the four arcs `v → j`, `v → k`, `j → k`, and `k → j`.

This is the last-independent-row step of the sparse half-rank argument.
The support argument works over any semiring without zero divisors, hence
over every field. It does not formalize the traversal, the full rank bound,
or code capacity.
-/

namespace LeanMachine.LastRowSupport

set_option autoImplicit false

variable {F V : Type*} [Semiring F]

/-- On coordinates annihilating the old vectors, one adjoined vector spans
all restrictions. No finiteness assumption is needed. -/
theorem exists_mul_on_of_mem_span_insert
    (old : Set (V → F)) (u x : V → F) (T : Set V)
    (hx : x ∈ Submodule.span F (insert u old))
    (hzero : ∀ y ∈ old, ∀ j ∈ T, y j = 0) :
    ∃ a : F, ∀ j ∈ T, x j = a * u j := by
  obtain ⟨a, z, hz, rfl⟩ := Submodule.mem_span_insert.mp hx
  clear hx
  refine ⟨a, ?_⟩
  intro j hj
  have hzj : z j = 0 := by
    induction hz using Submodule.span_induction with
    | mem y hy => exact hzero y hy j hj
    | zero => rfl
    | add y z hy hz ihy ihz =>
        change y j + z j = 0
        rw [ihy, ihz, add_zero]
    | smul a y hy ih =>
        change a * y j = 0
        rw [ih, mul_zero]
  change a * u j + z j = a * u j
  rw [hzj, add_zero]

/-- Exclude two mutual neighbours sharing an outgoing predecessor.
Triangle-free actual undirected support implies this weaker condition. -/
def NoFourArcPattern (B : V → V → F) : Prop :=
  ∀ ⦃v j k : V⦄, v ≠ j → v ≠ k → j ≠ k →
    ¬ (B v j ≠ 0 ∧ B v k ≠ 0 ∧ B j k ≠ 0 ∧ B k j ≠ 0)

variable [NoZeroDivisors F]

/-- Only the rows and diagonal entries indexed by `T` need the hypotheses.
The nonzero entries of the adjoined row on `T` follow from these premises. -/
theorem subsingleton_of_rows_mem_span_insert
    (B : V → V → F) (old : Set (V → F)) (v : V) (T : Set V)
    (hpattern : NoFourArcPattern B)
    (hspan : ∀ j ∈ T, B j ∈ Submodule.span F (insert (B v) old))
    (hzero : ∀ y ∈ old, ∀ j ∈ T, y j = 0)
    (hdiag : ∀ j ∈ T, B j j ≠ 0) (hv : v ∉ T) :
    T.Subsingleton := by
  intro j hj k hk
  by_contra hjk
  obtain ⟨a, ha⟩ := exists_mul_on_of_mem_span_insert old (B v) (B j) T
    (hspan j hj) hzero
  obtain ⟨b, hb⟩ := exists_mul_on_of_mem_span_insert old (B v) (B k) T
    (hspan k hk) hzero
  have haj : a * B v j ≠ 0 := by
    rw [← ha j hj]
    exact hdiag j hj
  have hbk : b * B v k ≠ 0 := by
    rw [← hb k hk]
    exact hdiag k hk
  have ha0 : a ≠ 0 := (mul_ne_zero_iff.mp haj).1
  have hvj : B v j ≠ 0 := (mul_ne_zero_iff.mp haj).2
  have hb0 : b ≠ 0 := (mul_ne_zero_iff.mp hbk).1
  have hvk : B v k ≠ 0 := (mul_ne_zero_iff.mp hbk).2
  have hjkne : B j k ≠ 0 := by
    rw [ha k hk]
    exact mul_ne_zero ha0 hvk
  have hkjne : B k j ≠ 0 := by
    rw [hb j hj]
    exact mul_ne_zero hb0 hvj
  exact hpattern (v := v) (j := j) (k := k)
    (fun h => hv (h.symm ▸ hj)) (fun h => hv (h.symm ▸ hk)) hjk
    ⟨hvj, hvk, hjkne, hkjne⟩

/-- Finite cardinality form of the same support bound. The ambient type
may still be infinite, and only the displayed columns are counted. -/
theorem card_le_one_of_rows_mem_span_insert
    (B : V → V → F) (old : Set (V → F)) (v : V) (T : Finset V)
    (hpattern : NoFourArcPattern B)
    (hspan : ∀ j ∈ T, B j ∈ Submodule.span F (insert (B v) old))
    (hzero : ∀ y ∈ old, ∀ j ∈ T, y j = 0)
    (hdiag : ∀ j ∈ T, B j j ≠ 0) (hv : v ∉ T) :
    T.card ≤ 1 :=
  Finset.card_le_one_iff_subsingleton.mpr
    (subsingleton_of_rows_mem_span_insert B old v (T : Set V)
      hpattern hspan hzero hdiag hv)

/-- Direct last-row form: all rows lie in the span after the new row is
adjoined, and its own column already occurred in an old vector. -/
theorem new_columns_subsingleton
    (B : V → V → F) (old : Set (V → F)) (v : V)
    (hpattern : NoFourArcPattern B)
    (hspan : ∀ j, B j ∈ Submodule.span F (insert (B v) old))
    (hdiag : ∀ j, B j j ≠ 0)
    (hown : ∃ y ∈ old, y v ≠ 0) :
    {j | B v j ≠ 0 ∧ ∀ y ∈ old, y j = 0}.Subsingleton := by
  apply subsingleton_of_rows_mem_span_insert B old v _ hpattern
  · exact fun j _ => hspan j
  · exact fun y hy j hj => hj.2 y hy
  · exact fun j _ => hdiag j
  · rintro ⟨_, hzero⟩
    obtain ⟨y, hy, hyv⟩ := hown
    exact hyv (hzero y hy)

end LeanMachine.LastRowSupport

#print axioms LeanMachine.LastRowSupport.exists_mul_on_of_mem_span_insert
#print axioms LeanMachine.LastRowSupport.subsingleton_of_rows_mem_span_insert
#print axioms LeanMachine.LastRowSupport.card_le_one_of_rows_mem_span_insert
#print axioms LeanMachine.LastRowSupport.new_columns_subsingleton

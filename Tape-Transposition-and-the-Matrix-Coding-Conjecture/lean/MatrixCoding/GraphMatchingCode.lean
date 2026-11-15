import LeanMachine.WholeRow.GraphMatchings
import MatrixCoding.InducedMatchings

/-!
# From graph induced matchings to whole-row codes

The finite conversion used in the growing-window remark. Graph edges are
partitioned into nonempty induced matchings using Mathlib's definitions.
Each part supplies one equation on both orientations of its edges. The
helper map contains the diagonal and all non-neighbours; its width is
exactly d minus the graph degree. Graph-existence results remain cited.
-/

namespace LeanBacklog.GraphMatchingCode

open Finset LeanMachine.WholeRow
open scoped BigOperators Classical
noncomputable section

variable {d : ℕ} {κ A : Type*} [Fintype κ] [AddCommGroup A] [Fintype A]
variable {G : SimpleGraph (Fin d)} (P : GraphMatchingPartition G κ)

/-- One prescribed sum for each matching, including both orders of its edges. -/
def code (s : κ → A) : Finset (Fin d × Fin d → A) := P.toInducedMatchingPartition.code s

theorem mem_code_iff (s : κ → A) (x : Fin d × Fin d → A) :
    x ∈ code P s ↔ ∀ k, ∑ e ∈ (univ.filter fun e : Fin d × Fin d =>
      (P.part k).Adj e.1 e.2), x e = s k := by
  simp only [code, InducedMatchingPartition.code, mem_filter, mem_univ, true_and,
    funext_iff, LeanMachine.DisjointSums.encode_apply,
    GraphMatchingPartition.toInducedMatchingPartition]

/-- The actual whole-row recovery predicate used by the matrix-coding bridge. -/
theorem isWholeRowCode (s : κ → A) :
    RowSpread.IsWholeRowCodeExcept (graphHelpers G) ∅ (code P s) :=
  InducedMatchingCodes.isWholeRowCode P.toInducedMatchingPartition s

/-- Exactly one independent equation per nonempty graph matching. -/
theorem cardinality (s : κ → A) :
    (code P s).card = Fintype.card A ^ (d * d - Fintype.card κ) :=
  InducedMatchingCodes.cardinality P.toInducedMatchingPartition s

/-- Every diagonal or non-edge coordinate is free. -/
theorem update_nonedge (s : κ → A) {x : Fin d × Fin d → A}
    (hx : x ∈ code P s) {e : Fin d × Fin d} (he : ¬ G.Adj e.1 e.2) (a : A) :
    Function.update x e a ∈ code P s := by
  have hfree : ∀ k, e ∉ P.toInducedMatchingPartition.support k := by
    intro k hk
    exact he ((P.mem_support k e).mp hk).adj_sub
  have h := P.toInducedMatchingPartition.toDisjointSums.encode_update hfree x a
  simpa only [code, InducedMatchingPartition.code, mem_filter, mem_univ, true_and, h]
    using hx

omit [Fintype κ] [AddCommGroup A] [Fintype A] in
/-- Minimum degree d-w is exactly the window-w condition, including the diagonal. -/
theorem window_iff (w : ℕ) :
    (∀ j, (graphHelpers G j).card ≤ w) ↔ ∀ j, d ≤ G.degree j + w := by
  simp only [graphHelpers_card_le_iff, Fintype.card_fin]

include P in
/-- The finite construction, with its window and exact code size together. -/
theorem exists_code (w : ℕ) (hdegree : ∀ j, d ≤ G.degree j + w) :
    ∃ C : Finset (Fin d × Fin d → A),
      RowSpread.IsWholeRowCodeExcept (graphHelpers G) ∅ C ∧
      (∀ j, (graphHelpers G j).card ≤ w) ∧
      C.card = Fintype.card A ^ (d * d - Fintype.card κ) :=
  ⟨code P 0, isWholeRowCode P 0, (window_iff w).mpr hdegree, cardinality P 0⟩

/-- The zero-sum construction as a linear subspace, over any field. -/
def linearCode (F : Type*) [Field F] : Submodule F (Fin d × Fin d → F) :=
  (P.linearChecks (F := F)).ker

theorem mem_linearCode_iff_code {F : Type*} [Field F] [Fintype F]
    (x : Fin d × Fin d → F) :
    x ∈ linearCode P F ↔ x ∈ code P (0 : κ → F) := by
  simp only [linearCode, LinearMap.mem_ker, code, InducedMatchingPartition.code,
    mem_filter, mem_univ, true_and]
  rfl

/-- Codimension is exactly the number of matching parts, without assuming
that the field is finite. -/
theorem finrank_linearCode_add (F : Type*) [Field F] :
    Module.finrank F (linearCode P F) + Fintype.card κ = d * d := by
  change Module.finrank F (P.linearChecks (F := F)).ker + Fintype.card κ = d * d
  convert P.finrank_ker_add (F := F) using 1
  simp

end
end LeanBacklog.GraphMatchingCode

import LuckApproximation.Construction
import LuckApproximation.Data
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.NormNum.Ineq

/-!
# The Goren–Oort Tanner operator at ℓ = 11, p = 3, over `𝔽₃[F]`

`F = FreeGroup (Fin 89)` is the fundamental group of the base graph `X₀ = Γ⁺(λ₀)\T` (11 + 11
vertices, 110 edges), free on the 89 edges outside a spanning tree. The operator `opA` is the
Tanner operator of the Goren–Oort configuration at weight 2 (parallel weight `(p+1)/2`), restricted
from `𝔽₉` to `𝔽₃`. Its incidences and blocks are the construction of `Construction.lean` (`Con.edgeOf`,
`Con.blockNat`); the generators of the non-tree edges come from `Data.edgeGen`, whose tree `ConChecks.lean` checks to
be a spanning tree:
row `10 v₀ + 2c + a` is coefficient `c` (component `a`) of the binary quartic form at even vertex
`v₀`; column `10 v₁ + 2r + b` is parity check `r` (component `b`) at odd vertex `v₁`. Each entry is a
single group element times a scalar, because `X₀` has no multiple edges.

Along a cyclic 3-power cover with voltage `volt` the entries of `opA` become
`c · t^v = c (1 + v u + [v = 2] u²)` with `u = t − 1`, giving the matrices `B₀, B₁, B₂`
(`CyclicTower.lean`).
-/

namespace Luck.Op

open Luck.Data

/-- The free group of rank 89, `π₁(X₀)`. -/
abbrev F := FreeGroup (Fin 89)

/-- Block (vertex) and slot of a row or column index. -/
def blk (i : Fin 110) : Fin 11 := ⟨i.val / 10, by omega⟩
def slot (i : Fin 110) : Fin 10 := ⟨i.val % 10, Nat.mod_lt _ (by norm_num)⟩

/-- The edge joining the even vertex of row `i` to the odd vertex of column `j`, if any. -/
def entryEdge (i j : Fin 110) : Option (Fin 110) := Con.edgeOf (blk i) (blk j)

/-- The 10 × 10 block of an edge over `𝔽₃`, from the construction. -/
def coupling (e : Fin 110) (a b : Fin 10) : ZMod 3 := (Con.blockNat e a b : ZMod 3)

/-- The group element of an edge: its free generator, or `1` on spanning-tree edges. -/
noncomputable def gamma (e : Fin 110) : F :=
  match edgeGen e with
  | none => 1
  | some g => FreeGroup.of g

/-- The operator `A` over `𝔽₃[F]` (rows: unknowns, columns: checks; `x ↦ x A`). -/
noncomputable def opA : Matrix (Fin 110) (Fin 110) (MonoidAlgebra (ZMod 3) F) :=
  Matrix.of fun i j =>
    match entryEdge i j with
    | none => 0
    | some e => MonoidAlgebra.single (gamma e) (coupling e (slot i) (slot j))

/-- The 3-cover voltage of an edge. -/
noncomputable def voltE (e : Fin 110) : ZMod 3 :=
  match edgeGen e with
  | none => 0
  | some g => volt g

/-- Coefficients of `1`, `u`, `u²` of the image of `opA` in `𝔽₃[C₃] = 𝔽₃[u]/(u³)`. -/
noncomputable def B0 : Matrix (Fin 110) (Fin 110) (ZMod 3) :=
  Matrix.of fun i j =>
    match entryEdge i j with
    | none => 0
    | some e => coupling e (slot i) (slot j)

noncomputable def B1 : Matrix (Fin 110) (Fin 110) (ZMod 3) :=
  Matrix.of fun i j =>
    match entryEdge i j with
    | none => 0
    | some e => voltE e * coupling e (slot i) (slot j)

noncomputable def B2 : Matrix (Fin 110) (Fin 110) (ZMod 3) :=
  Matrix.of fun i j =>
    match entryEdge i j with
    | none => 0
    | some e => (if voltE e = 2 then 1 else 0) * coupling e (slot i) (slot j)

end Luck.Op

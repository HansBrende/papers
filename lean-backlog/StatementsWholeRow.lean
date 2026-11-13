import LeanMachine.WholeRow.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Basic.Real.Basic

/-!
# Open targets D1 and D8: whole-row and covariant linear codes

These declarations are definitions of propositions, not asserted theorems or axioms.
Nothing in this file proves a half-rate bound. Check from `lean-machine/` with
`lake env lean ../lean-backlog/StatementsWholeRow.lean`.

The field is fixed before the asymptotic quantifiers: the threshold may depend
on the field, the window bound, and the error. No finiteness, characteristic,
splitting-field, coefficient-norm, or decoder-invertibility hypothesis is imposed.
For a finite field, dimension bounds give the corresponding code-cardinality bounds.
-/

open scoped BigOperators Matrix

namespace LeanBacklog.WholeRow

universe u v

/-- **Open front D1, linear form of Paper 17, Problem 9.4(c).**
For every fixed helper-row bound and positive error, every sufficiently large
whole-row recovery code has rate at most one half plus that error.

`ρ r` consists of the helper ROWS for output COLUMN `r`; the shared definition says
`X i r = ∑ s ∈ ρ r, ∑ j, M r s i j * X s j`. All blocks are arbitrary, and one
fixed family `M` must work for every matrix in the code. The threshold is uniform
over the relation and the blocks. This asks only about linear codes/decoders.
-/
def LinearWholeRowHalfRate (F : Type u) [Field F] : Prop :=
  ∀ (w : ℕ) (η : ℝ), 0 < η → ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ∀ (ρ : Fin d → Finset (Fin d))
      (M : Fin d → Fin d → Matrix (Fin d) (Fin d) F),
      (∀ r, (ρ r).card ≤ w) →
      (Module.finrank F (LeanMachine.WholeRow.rowCode ρ M) : ℝ) ≤
        (1 / 2 + η) * (d : ℝ) ^ 2

section FiniteGroup

variable {F : Type u} [Field F] {G : Type v} [Group G] [Fintype G]

/-- The Cayley helper-row relation: output column `r` reads rows `r * s`, `s ∈ Σ`.
No symmetry, identity-membership, or generation assumption on `Σ` is imposed. -/
noncomputable def cayleyRows (S : Finset G) (r : G) : Finset G := by
  classical
  exact S.image (fun s => r * s)

omit [Fintype G] in
/-- Left translation does not change the helper-window cardinality. -/
theorem card_cayleyRows (S : Finset G) (r : G) : (cayleyRows S r).card = S.card := by
  classical
  exact Finset.card_image_of_injective _ (fun _ _ h => mul_left_cancel h)

/-- Original-coordinate blocks for one covariant family `κ`.

If the helper row is `r * s`, this equals `κ s (r⁻¹ * i) ((r * s)⁻¹ * j)`.
Writing `X̃(r,g)=X(r,r*g)`, its decoder is
`(K X)̃(r,g)=∑ s∈Σ, ∑ h, κ s g h * X̃(r*s,h)`.
Thus `κ` varies with generator and displacement indices, but NOT independently
with base point `r`. The SAME `κ` also serves every representation sector.
-/
def covariantBlocks (κ : G → Matrix G G F) (r a : G) : Matrix G G F :=
  fun i j => κ (r⁻¹ * a) (r⁻¹ * i) (a⁻¹ * j)

omit [Field F] [Fintype G] in
/-- Literal simultaneous-left-translation covariance of the original blocks. -/
theorem covariantBlocks_left_translate (κ : G → Matrix G G F) (t r a i j : G) :
    covariantBlocks κ (t * r) (t * a) (t * i) (t * j) =
      covariantBlocks κ r a i j := by
  simp [covariantBlocks, mul_assoc]

/-- The covariant slice expressed using the existing whole-row code definition. -/
noncomputable def covariantRowCode (S : Finset G) (κ : G → Matrix G G F) :
    Submodule F (Matrix G G F) :=
  LeanMachine.WholeRow.rowCode (cayleyRows S) (covariantBlocks κ)

/-- The residual matrix over the group algebra, indexed by displacements.

Its entry `(g,h)` is `1_{h=g⁻¹} [g] - ∑ s∈Σ, κ s g h [s]`, where `[s]` is
the group-algebra basis element. Inversion fixed points are included literally;
no fixed-point-free replacement or separate-sector maximization is made.
-/
noncomputable def covariantResidual (S : Finset G) (κ : G → Matrix G G F) :
    Matrix G G (MonoidAlgebra F G) := by
  classical
  exact fun g h =>
    (if h = g⁻¹ then MonoidAlgebra.single g 1 else 0) -
      ∑ s ∈ S, MonoidAlgebra.single s (κ s g h)

/-- The group-algebra matrix acts by left multiplication, regarded as an
`F`-linear map. No vector-space rank over the generally nondivision ring `F[G]`
is used. Identifying `v_h` by `v_h.coeff(r⁻¹)=X(r,r*h)` turns multiplication
by `[s]` into the required right translation of the base point `r -> r*s`.
-/
noncomputable def covariantResidualAction (S : Finset G) (κ : G → Matrix G G F) :
    (G → MonoidAlgebra F G) →ₗ[F] (G → MonoidAlgebra F G) :=
  Matrix.mulVecBilin F F (covariantResidual S κ)

/-- Explicit action formula, using ordinary group-algebra multiplication. -/
theorem covariantResidualAction_apply (S : Finset G) (κ : G → Matrix G G F)
    (x : G → MonoidAlgebra F G) (g : G) :
    covariantResidualAction S κ x g = ∑ h, covariantResidual S κ g h * x h := rfl

omit [Fintype G] in
/-- The inverse coefficient convention realizes right translation, including
in noncommutative groups. This checks the orientation in the definition above. -/
theorem single_mul_coeff_inv (s r : G) (a : F) (x : MonoidAlgebra F G) :
    (MonoidAlgebra.single s a * x).coeff r⁻¹ = a * x.coeff (r * s)⁻¹ := by
  simp [mul_inv_rev]

/-- Ordinary rank OVER THE FIELD `F` of the group-algebra matrix action.
The ambient `F`-space has dimension `|G|²`, using the group basis in every
displacement coordinate. This is an unnormalized integer rank.
-/
noncomputable def covariantResidualRank (S : Finset G) (κ : G → Matrix G G F) : ℕ :=
  Module.finrank F (LinearMap.range (covariantResidualAction S κ))

omit [Group G] in
/-- The finite group basis computes the actual dimension over the field. -/
theorem finrank_groupAlgebra :
    Module.finrank F (MonoidAlgebra F G) = Fintype.card G := by
  rw [Module.finrank_eq_nat_card_basis (MonoidAlgebra.basis G F)]
  simp

omit [Group G] in
/-- The group-algebra action acts on exactly `|G|²` field coordinates. -/
theorem finrank_covariantAmbient :
    Module.finrank F (G → MonoidAlgebra F G) = Fintype.card G ^ 2 := by
  let : Module.Finite F (MonoidAlgebra F G) :=
    Module.Finite.of_basis (MonoidAlgebra.basis G F)
  rw [Module.finrank_pi_fintype]
  simp [finrank_groupAlgebra, pow_two]

/-- Rank-nullity for the literal finite group-algebra action, over `F`.
This proves only the rank/nullity conversion, not the conjectured bound. -/
theorem covariant_nullity_add_rank (S : Finset G) (κ : G → Matrix G G F) :
    Module.finrank F (LinearMap.ker (covariantResidualAction S κ)) +
      covariantResidualRank S κ = Fintype.card G ^ 2 := by
  let : Module.Finite F (MonoidAlgebra F G) :=
    Module.Finite.of_basis (MonoidAlgebra.basis G F)
  rw [covariantResidualRank, Nat.add_comm, LinearMap.finrank_range_add_finrank_ker,
    finrank_covariantAmbient]

end FiniteGroup

/-- **Open front D8, the finite-group covariant slice of D1.**
Every bounded-support covariant residual eventually has field rank at least
`(1/2 - η)|G|²`. Equivalently, its field-linear kernel has dimension at most
`(1/2 + η)|G|²` by rank-nullity. The threshold is uniform over finite groups,
generator sets, and the single globally shared family `κ`.

All finite groups are included, not only quasirandom ones. The group-algebra
action makes sense in every characteristic, including characteristics dividing
the group order; semisimple representation decomposition is not assumed.
-/
def CovariantGroupHalfRate (F : Type u) [Field F] : Prop :=
  ∀ (w : ℕ) (η : ℝ), 0 < η → ∃ d₀ : ℕ,
    ∀ (G : Type v) [Group G] [Fintype G], d₀ ≤ Fintype.card G →
      ∀ (S : Finset G) (κ : G → Matrix G G F), S.card ≤ w →
        (1 / 2 - η) * (Fintype.card G : ℝ) ^ 2 ≤
          (covariantResidualRank S κ : ℝ)

/-- A stronger version of D1 whose threshold is uniform also in the field.
The field quantifier is AFTER `∃ d₀`; this is not asserted equivalent to
`LinearWholeRowHalfRate` for each fixed field. -/
def UniformInFieldLinearWholeRowHalfRate : Prop :=
  ∀ (w : ℕ) (η : ℝ), 0 < η → ∃ d₀ : ℕ,
    ∀ (F : Type u) [Field F], ∀ d : ℕ, d₀ ≤ d →
      ∀ (ρ : Fin d → Finset (Fin d))
        (M : Fin d → Fin d → Matrix (Fin d) (Fin d) F),
        (∀ r, (ρ r).card ≤ w) →
        (Module.finrank F (LeanMachine.WholeRow.rowCode ρ M) : ℝ) ≤
          (1 / 2 + η) * (d : ℝ) ^ 2

/-- A stronger version of D8 whose threshold is uniform also in the field.
The original fixed-field targets suffice to express a fixed alphabet's linear
problem; this separate proposition records the stronger quantifier order. -/
def UniformInFieldCovariantGroupHalfRate : Prop :=
  ∀ (w : ℕ) (η : ℝ), 0 < η → ∃ d₀ : ℕ,
    ∀ (F : Type u) [Field F],
      ∀ (G : Type v) [Group G] [Fintype G], d₀ ≤ Fintype.card G →
        ∀ (S : Finset G) (κ : G → Matrix G G F), S.card ≤ w →
          (1 / 2 - η) * (Fintype.card G : ℝ) ^ 2 ≤
            (covariantResidualRank S κ : ℝ)

/-- Only a quantifier-specialization lemma; it proves neither conjecture. -/
theorem UniformInFieldLinearWholeRowHalfRate.to_fixed
    (h : UniformInFieldLinearWholeRowHalfRate.{u}) (F : Type u) [Field F] :
    LinearWholeRowHalfRate F := by
  intro w η hη
  obtain ⟨d₀, hd₀⟩ := h w η hη
  exact ⟨d₀, hd₀ F⟩

/-- Only a quantifier-specialization lemma; it proves neither conjecture. -/
theorem UniformInFieldCovariantGroupHalfRate.to_fixed
    (h : UniformInFieldCovariantGroupHalfRate.{u, v}) (F : Type u) [Field F] :
    CovariantGroupHalfRate.{u, v} F := by
  intro w η hη
  obtain ⟨d₀, hd₀⟩ := h w η hη
  exact ⟨d₀, hd₀ F⟩

end LeanBacklog.WholeRow

import FanoFull
import LeanMachine.WholeRow.AcyclicOrder

/-!
# Whole-row helper containment and macro projection

This is the deterministic upper-bound step of sparse amplification. It
reuses Paper 4's push-forward theorem. No mixing, random construction,
girth, code linearity, or attainment on the fine host is assumed.
-/

namespace LeanBacklog.MacroProjection

open Finset MotionDepthCodes
open scoped BigOperators
noncomputable section

variable {R J B K : Type*} [Fintype R] [Fintype J] [Fintype B] [Fintype K]
variable [DecidableEq R] [DecidableEq J] [DecidableEq B] [DecidableEq K]

/-- All cells in the helper rows of the target's column. -/
abbrev rowHelpers (ρ : J → Finset R) (x : R × J) : Finset (R × J) :=
  LeanMachine.WholeRow.AcyclicOrder.rowHelpers ρ x

omit [Fintype R] [DecidableEq R] [DecidableEq J] in
@[simp] theorem mem_rowHelpers (ρ : J → Finset R) (x y : R × J) :
    y ∈ rowHelpers ρ x ↔ y.1 ∈ ρ x.2 := by
  classical
  exact LeanMachine.WholeRow.AcyclicOrder.mem_rowHelpers ρ x y

/-- Independent row and column maps give the cell projection. -/
def cellMap (πR : R → B) (πJ : J → K) (x : R × J) : B × K :=
  (πR x.1, πJ x.2)

omit [Fintype B] in
/-- Helper containment supplies precisely Paper 4's validity-transfer premise. -/
theorem projected_valid (ρ : J → Finset R) (ρ₀ : K → Finset B)
    (πR : R → B) (πJ : J → K)
    (hρ : ∀ j r, r ∈ ρ j → πR r ∈ ρ₀ (πJ j))
    {h : Finset (R × J) → ℝ} (hh : IsPolymatroid h)
    (hv : IsValid h (rowHelpers ρ)) :
    IsValid (pushRank (cellMap πR πJ) h) (rowHelpers ρ₀) := by
  classical
  apply hv.pushRank hh (cellMap πR πJ)
  intro x y hy
  exact (mem_rowHelpers ρ₀ _ _).mpr (hρ x.2 y.1 ((mem_rowHelpers ρ x y).mp hy))

omit [Fintype B] [Fintype K] in
/-- Unit fine caps give a macro cap equal to the size of its fibre. -/
theorem projected_singleton_le_card (πR : R → B) (πJ : J → K)
    {h : Finset (R × J) → ℝ} (hh : IsPolymatroid h) (hc : ∀ x, h {x} ≤ 1)
    (p : B × K) :
    pushRank (cellMap πR πJ) h {p} ≤
      ((univ.filter (fun x => cellMap πR πJ x = p)).card : ℝ) := by
  classical
  simp only [pushRank, mem_singleton]
  calc
    _ ≤ ∑ x ∈ univ.filter (fun x => cellMap πR πJ x = p), h {x} := hh.le_sum_singleton _
    _ ≤ ∑ _x ∈ univ.filter (fun x => cellMap πR πJ x = p), (1 : ℝ) :=
      sum_le_sum (fun x _ => hc x)
    _ = _ := by simp

/-- Each macro cell of a product of clone groups contains exactly `n*m` cells. -/
theorem clone_fiber_card (n m : ℕ) (p : B × K) :
    (univ.filter (fun x : (B × Fin n) × (K × Fin m) =>
      cellMap Prod.fst Prod.fst x = p)).card = n * m := by
  classical
  have he : univ.filter (fun x : (B × Fin n) × (K × Fin m) =>
      cellMap Prod.fst Prod.fst x = p) =
      (({p.1} : Finset B).product univ).product (({p.2} : Finset K).product univ) := by
    ext x
    simp [cellMap, Prod.ext_iff, eq_comm]
  rw [he]
  simp

private theorem divide_polymatroid {V : Type*} [DecidableEq V]
    {h : Finset V → ℝ} (hh : IsPolymatroid h) (a : ℝ) (ha : 0 ≤ a) :
    IsPolymatroid (fun S => h S / a) where
  empty := by simp [hh.empty]
  mono := fun _ _ h => div_le_div_of_nonneg_right (hh.mono h) ha
  submod := by
    intro S T
    simpa only [← add_div] using div_le_div_of_nonneg_right (hh.submod S T) ha

/-- Any unit-cap base upper bound transfers under a positive fibre-size cap.
Neither surjectivity of the maps nor equality of fibre sizes is needed. -/
theorem upper_of_projection (ρ : J → Finset R) (ρ₀ : K → Finset B)
    (πR : R → B) (πJ : J → K)
    (hρ : ∀ j r, r ∈ ρ j → πR r ∈ ρ₀ (πJ j))
    (a U : ℝ) (ha : 0 < a)
    (hsize : ∀ p, ((univ.filter (fun x => cellMap πR πJ x = p)).card : ℝ) ≤ a)
    (hbase : ∀ g : Finset (B × K) → ℝ, IsPolymatroid g →
      IsValid g (rowHelpers ρ₀) → (∀ p, g {p} ≤ 1) → g univ ≤ U)
    {h : Finset (R × J) → ℝ} (hh : IsPolymatroid h)
    (hv : IsValid h (rowHelpers ρ)) (hc : ∀ x, h {x} ≤ 1) : h univ ≤ a * U := by
  classical
  let g := pushRank (cellMap πR πJ) h
  have hg : IsPolymatroid g := hh.pushRank _
  have hgv : IsValid g (rowHelpers ρ₀) := projected_valid ρ ρ₀ πR πJ hρ hh hv
  have hb := hbase (fun S => g S / a) (divide_polymatroid hg a ha.le)
    (fun p => congrArg (fun t : ℝ => t / a) (hgv p)) (fun p =>
      (div_le_one ha).mpr ((projected_singleton_le_card πR πJ hh hc p).trans (hsize p)))
  rw [div_le_iff₀ ha] at hb
  simpa only [g, pushRank_univ, mul_comm] using hb

/-- Fano accepts arbitrary maps with a common macro-cell cap, including cap zero. -/
theorem fano_upper_of_projection (ρ : J → Finset R)
    (πR : R → Fin 7) (πJ : J → Fin 7)
    (hρ : ∀ j r, r ∈ ρ j → FanoCertificate.incident (πR r) (πJ j))
    (a : ℝ) (hsize : ∀ p,
      ((univ.filter (fun x => cellMap πR πJ x = p)).card : ℝ) ≤ a)
    {h : Finset (R × J) → ℝ} (hh : IsPolymatroid h)
    (hv : IsValid h (rowHelpers ρ)) (hc : ∀ x, h {x} ≤ 1) :
    3 * h univ ≤ 119 * a := by
  classical
  have hmap : IsValid (pushRank (cellMap πR πJ) h) FanoFull.helpers := by
    apply hv.pushRank hh (cellMap πR πJ)
    intro x y hy
    exact mem_filter.mpr ⟨mem_univ _, hρ x.2 y.1 ((mem_rowHelpers ρ x y).mp hy)⟩
  have hb := FanoFull.full_upper_of_cap (hh.pushRank _) hmap a
    (fun p => (projected_singleton_le_card πR πJ hh hc p).trans (hsize p))
  simpa only [pushRank_univ] using hb

/-- The fine Fano bound is rectangular in the clone counts and includes empty clones. -/
theorem fano_clone_upper (n m : ℕ)
    (ρ : (Fin 7 × Fin m) → Finset (Fin 7 × Fin n))
    (hρ : ∀ j r, r ∈ ρ j → FanoCertificate.incident r.1 j.1)
    {h : Finset ((Fin 7 × Fin n) × (Fin 7 × Fin m)) → ℝ}
    (hh : IsPolymatroid h) (hv : IsValid h (rowHelpers ρ)) (hc : ∀ x, h {x} ≤ 1) :
    3 * h univ ≤ 119 * ((n * m : ℕ) : ℝ) := by
  apply fano_upper_of_projection ρ Prod.fst Prod.fst hρ _ ?_ hh hv hc
  intro p
  rw [clone_fiber_card]

#print axioms rowHelpers
#print axioms mem_rowHelpers
#print axioms cellMap
#print axioms projected_valid
#print axioms projected_singleton_le_card
#print axioms clone_fiber_card
#print axioms upper_of_projection
#print axioms fano_upper_of_projection
#print axioms fano_clone_upper

end
end LeanBacklog.MacroProjection

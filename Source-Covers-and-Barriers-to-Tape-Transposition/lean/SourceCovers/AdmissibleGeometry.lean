import SourceCovers.OrbitCountDeficit

set_option autoImplicit false

/-!
# The actual geometry and local computation interface

This packages the original finite theorem's hypotheses. Its fields specify
complete work walks, the clamped raw path, ordered output times, the actual
correctness set, finite step records and local determination by all parents.
No source-cover bound, global recovery, or final deficit inequality is a field.
-/

namespace SourceCovers

open Classical Finset LeanMachine Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators
noncomputable section

/-- An admissible fixed-geometry instance, allowing arbitrary positive entry
width. The record alphabet and geometry may vary between instances. -/
structure AdmissibleGeometry (c β : ℝ) (N q : ℕ) where
  d : ℕ
  b : ℕ
  hd : 0 < d
  hb : 0 < b
  T : ℕ
  k : ℕ
  xs : Fin k → ℕ → ℤ
  work_walk : ∀ h, BoundedNesting.IsWalk (xs h)
  x : ℕ → ℕ
  raw_range : ∀ s ≤ T - 1, x s < d * d * b
  raw_step : ∀ e < T - 1, dist (x e : ℝ) (x (e + 1) : ℝ) ≤ 1
  t : ℕ → ℕ
  append_strict : StrictMonoOn t (Set.Iio (d * d * b))
  append_lt : ∀ z < d * d * b, t z < T
  C : Finset (Fin (d * d * b) → Bool)
  correct_nonempty : C.Nonempty
  Record : Type
  recordFintype : Fintype Record
  record : (Fin (d * d * b) → Bool) → ℕ → Record
  output : ℕ → Record → Bool
  capacity : Real.log (@Fintype.card Record recordFintype : ℝ) / Real.log 2 ≤ β
  locally_determined : CausalRecovery.LocallyDetermined (actualParents xs T) (fun s => {x s})
    (T - 1) (C : Set (Fin (d * d * b) → Bool)) zbit record
  correct : ∀ z ∈ C, ∀ u : Fin (d * d * b),
    output (tpos d b u.val) (record z (t (tpos d b u.val))) = z u
  core : Finset (ActualFamily xs T)
  core_coloring : HasSpanColoring core 2
  full_coloring : HasSpanColoring (univ : Finset (ActualFamily xs T)) N
  exceptions : Finset (ActualFamily xs T)
  exceptions_card : exceptions.card ≤ q
  exceptions_disjoint : Disjoint core exceptions
  a0 : ℕ
  outside_small : ∀ G : ActualFamily xs T, G ∉ core ∪ exceptions → G.hops.card ≤ a0
  runtime : (T : ℝ) ≤ c * (d * d * b)

attribute [instance] AdmissibleGeometry.recordFintype

namespace AdmissibleGeometry

variable {c β : ℝ} {N q : ℕ} (G : AdmissibleGeometry c β N q)

def inputLength : ℕ := G.d * G.d * G.b

def deficit : ℝ := G.inputLength - Real.log (G.C.card : ℝ) / Real.log 2

def relativeDeficit : ℝ := G.deficit / G.inputLength

theorem inputLength_pos : 0 < G.inputLength := Nat.mul_pos (Nat.mul_pos G.hd G.hd) G.hb

theorem dimension_le_inputLength : G.d ≤ G.inputLength :=
  (Nat.le_mul_of_pos_right G.d G.hd).trans (Nat.le_mul_of_pos_right _ G.hb)

theorem horizon_pos : 0 < G.T := lt_of_le_of_lt (Nat.zero_le _) (G.append_lt 0 G.inputLength_pos)

/-- Packaging preserves the complete paid theorem, rather than assuming its
conclusion as a field of a purported admissible geometry. -/
theorem orbit_count_deficit
    (K : Finset (ActualFamily G.xs G.T)) (hKsub : K ⊆ G.core)
    (P D : Finset (CoreFamily K)) {M w J R r a : ℕ}
    (hM : 2 ≤ M) (hK : K.card ≤ J) (hP : P.card ≤ R) (hR : R < M)
    (hD : D.card ≤ r) (hw : 0 < w)
    (hsize : ∀ F : ActualFamily G.xs G.T, F ∉ K ∪ G.exceptions → F.hops.card ≤ a)
    {α τ : ℝ}
    (hV : (∑ F ∈ univ \ D, ∑ e ∈ F.val.edges,
      dist (G.x e : ℝ) (G.x (e + 1) : ℝ)) ≤ α * (G.d * G.d * G.b))
    (hτ : ((∑ F ∈ coreNonleaves K \ P, F.val.hops.card : ℕ) : ℝ) ≤ τ) :
    G.relativeDeficit ≥
      max (1 - α) 0 ^ 2 / (2 * (2 * (r : ℝ) + 1) * (2 * (M : ℝ) + 4) ^ q) -
        (2 * bankCost M q * ((G.T - 1 : ℕ) : ℝ) / (G.d * (G.d * G.d * G.b)) +
          2 * ((w : ℝ) - 1) / (G.d * G.d * G.b) +
          ((G.d : ℝ) * G.b - G.b + 1) / (2 * (G.d * G.d * G.b)) +
          β / (G.d * G.d * G.b) * (J + q + τ / ((M - R : ℕ) : ℝ) +
            (1 + (N : ℝ) * a) * bankCost M q * ((G.T - 1 : ℕ) : ℝ) / w)) := by
  simpa only [relativeDeficit, deficit, inputLength, Nat.cast_mul] using
    orbit_count_paid_deficit (G.core_coloring.mono hKsub) hM G.exceptions P D
      hK G.exceptions_card hP hR hD G.work_walk G.full_coloring hsize
      G.x G.t G.hd G.hb hw G.append_strict G.append_lt G.raw_range G.raw_step
      G.C G.correct_nonempty G.record G.output G.capacity G.locally_determined G.correct hV hτ

end AdmissibleGeometry
end
end SourceCovers

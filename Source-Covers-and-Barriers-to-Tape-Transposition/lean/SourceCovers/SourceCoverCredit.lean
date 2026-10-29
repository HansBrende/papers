import SourceCovers.FractionalGap
import SourceCovers.AnchoredErosion
import LeanMachine.CircularRefinement

set_option autoImplicit false

/-!
# Admissible source-cover witnesses and supremum credit

Witnesses contain actual anchored arcs in a common real subdivision, together
with their complete-core fractional cover. The area bound is derived from the
geometry and is not a witness hypothesis. Arbitrary chosen witness families,
including empty families and families with an unattained supremum, are allowed.
-/

namespace SourceCovers

open Finset LeanMachine CyclicSelection WeightedCircularGap CircularSubdivision
open CircularRefinement AnchoredCircularCover AnchoredGapErosion
open scoped BigOperators ENNReal
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K : Finset (ActualFamily xs T)}

/-- Raw anchors and target points retain their coordinates in the finer real
subdivision. Added vertices may be fractional arc endpoints. -/
structure SourceCoverWitness (I : Finset (CoreFamily K)) (x : ℕ → ℕ)
    (L : ℕ) (S : Finset ℕ) where
  base : Finset ℕ
  base_nonempty : base.Nonempty
  base_subset : base ⊆ range L
  finite_cover : fractionalCoreCover I x base ≠ ⊤
  N : ℕ
  p : ℕ → ℝ
  embed : ℕ ↪o ℕ
  embed_lt : ∀ a < L, embed a < N
  coordinate : ∀ a < L, p (embed a) = (a : ℝ)
  period : ∀ i, p (i + N) = p i + L
  monotone : ∀ i < N, p i ≤ p (i + 1)
  m : ℕ
  start : Fin m → ℕ
  len : Fin m → ℕ
  start_lt : ∀ i, start i < N
  len_le : ∀ i, len i ≤ N
  anchored : ∀ i, ∃ a ∈ base, embed a ∈ arc N (start i) (len i + 1)
  cover : S.image embed ⊆ base.image embed ∪ coveredVertices N univ start len
  budget : ℝ
  length_le : coveredLength N (edgeLength p) univ start len ≤ budget

/-- Every finitely covered complete target admits the exact, zero-cost witness.
No auxiliary arc or extra subdivision vertex is required. -/
def exactSourceCoverWitness (I : Finset (CoreFamily K)) (x : ℕ → ℕ)
    {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty) (hSL : S ⊆ range L)
    (hfinite : fractionalCoreCover I x S ≠ ⊤) : SourceCoverWitness I x L S where
  base := S
  base_nonempty := hS
  base_subset := hSL
  finite_cover := hfinite
  N := L
  p := fun i => i
  embed := (OrderIso.refl ℕ).toOrderEmbedding
  embed_lt := fun _ ha => ha
  coordinate := fun _ _ => rfl
  period := by intro i; exact Nat.cast_add i L
  monotone := by intro i _; exact_mod_cast Nat.le_succ i
  m := 0
  start := Fin.elim0
  len := Fin.elim0
  start_lt := fun i => Fin.elim0 i
  len_le := fun i => Fin.elim0 i
  anchored := fun i => Fin.elim0 i
  cover := by simp [coveredVertices]
  budget := 0
  length_le := by simp [coveredLength, coveredEdges]

def SourceCoverWitness.score {I : Finset (CoreFamily K)} {x : ℕ → ℕ}
    {L : ℕ} {S : Finset ℕ} (W : SourceCoverWitness I x L S) (α : ℝ) (r : ℕ) : ℝ :=
  max (1 - α) 0 ^ 2 /
    (2 * (2 * (r : ℝ) + 1) * (fractionalCoreCover I x W.base).toReal) -
      penalty (min (W.budget / L) 1)

@[simp]
theorem exactSourceCoverWitness_score (I : Finset (CoreFamily K)) (x : ℕ → ℕ)
    {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty) (hSL : S ⊆ range L)
    (hfinite : fractionalCoreCover I x S ≠ ⊤) (α : ℝ) (r : ℕ) :
    (exactSourceCoverWitness I x hS hSL hfinite).score α r =
      max (1 - α) 0 ^ 2 /
        (2 * (2 * (r : ℝ) + 1) * (fractionalCoreCover I x S).toReal) := by
  simp [SourceCoverWitness.score, exactSourceCoverWitness, penalty]

/-- Every individual witness earns no more credit than the actual target
gap area. The underlying recovery set is the complete target `S`. -/
theorem SourceCoverWitness.score_le (hc : HasSpanColoring K 2)
    (I J D : Finset (CoreFamily K)) (hIJ : I ⊆ J) (x : ℕ → ℕ)
    {L r : ℕ} (hL : 0 < L) (hD : D.card ≤ r) {S : Finset ℕ}
    (hS : S.Nonempty) (hSL : S ⊆ range L) {α : ℝ}
    (hV : (∑ q ∈ J \ D, ∑ e ∈ q.val.edges,
      dist (x e : ℝ) (x (e + 1) : ℝ)) ≤ α * L)
    (W : SourceCoverWitness I x L S) :
    W.score α r ≤ GapErosion.pointArea (range S.card) (gap L S hS) L := by
  have hbase := fractional_core_gap hc I J D hIJ x hL hD W.base_nonempty
    W.base_subset W.finite_cover hV
  have htotal : circumference W.N (edgeLength W.p) = L := total_length W.period
  have hgeom := AnchoredGapErosion.area_lower_bound (w := edgeLength W.p)
    (W.base_nonempty.image W.embed) (image_subset_range W.embed W.embed_lt W.base_subset)
    (hS.image W.embed) (image_subset_range W.embed W.embed_lt hSL)
    univ W.start W.len (fun i _ => W.start_lt i) (fun i _ => W.len_le i)
    (fun i _ => by
      obtain ⟨a, ha, harc⟩ := W.anchored i
      exact ⟨W.embed a, mem_image_of_mem W.embed ha, harc⟩)
    W.cover (fun i hi => sub_nonneg.mpr (W.monotone i hi))
    (by rw [htotal]; exact_mod_cast hL) W.length_le
  rw [area_image_eq_pointArea W.base_nonempty W.base_subset W.embed W.embed_lt W.period
      W.coordinate,
    area_image_eq_pointArea hS hSL W.embed W.embed_lt W.period W.coordinate, htotal] at hgeom
  exact (sub_le_sub_right hbase _).trans hgeom

/-- The chosen family is a set, so no finiteness or attainment is imposed. -/
def sourceCoverCredit {I : Finset (CoreFamily K)} {x : ℕ → ℕ} {L : ℕ} {S : Finset ℕ}
    (F : Set (SourceCoverWitness I x L S)) (α : ℝ) (r : ℕ) : ℝ :=
  sSup (insert 0 ((fun W => W.score α r) '' F))

@[simp]
theorem sourceCoverCredit_empty {I : Finset (CoreFamily K)} {x : ℕ → ℕ}
    {L : ℕ} {S : Finset ℕ} (α : ℝ) (r : ℕ) :
    sourceCoverCredit (∅ : Set (SourceCoverWitness I x L S)) α r = 0 := by
  simp [sourceCoverCredit]

/-- The supremum bounds hold for every chosen family, even when no witness
attains the supremum. -/
theorem sourceCoverCredit_bounds (hc : HasSpanColoring K 2)
    (I J D : Finset (CoreFamily K)) (hIJ : I ⊆ J) (x : ℕ → ℕ)
    {L r : ℕ} (hL : 0 < L) (hD : D.card ≤ r) {S : Finset ℕ}
    (hS : S.Nonempty) (hSL : S ⊆ range L) {α : ℝ}
    (hV : (∑ q ∈ J \ D, ∑ e ∈ q.val.edges,
      dist (x e : ℝ) (x (e + 1) : ℝ)) ≤ α * L)
    (F : Set (SourceCoverWitness I x L S)) :
    0 ≤ sourceCoverCredit F α r ∧
      sourceCoverCredit F α r ≤ GapErosion.pointArea (range S.card) (gap L S hS) L ∧
      GapErosion.pointArea (range S.card) (gap L S hS) L ≤ 1 / 2 := by
  let A := GapErosion.pointArea (range S.card) (gap L S hS) L
  have hA : 0 ≤ A := by unfold A GapErosion.pointArea; positivity
  have hub : ∀ z ∈ insert 0 ((fun W => W.score α r) '' F), z ≤ A := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hA
    · obtain ⟨W, _, rfl⟩ := hz
      exact W.score_le hc I J D hIJ x hL hD hS hSL hV
  have hnonempty : (insert 0 ((fun W => W.score α r) '' F)).Nonempty :=
    ⟨0, Set.mem_insert _ _⟩
  refine ⟨le_csSup ⟨A, hub⟩ (Set.mem_insert _ _), csSup_le hnonempty hub, ?_⟩
  rw [← area_one hS hSL]
  exact area_le_half hS hSL (fun _ _ => zero_le_one)

end
end SourceCovers

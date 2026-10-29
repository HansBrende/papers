import SourceCovers.SubsetHelper
import SourceCovers.IntervalQueryMovement

/-! The actual repeated columns of the subset interface. Arbitrary query
times and interval order are permitted. Singleton intervals include all
representative-time schedules as a special case. -/

namespace SourceCovers.SubsetMovement

open Finset LeanMachine
open scoped BigOperators Classical
noncomputable section

abbrev Column (N k h : ℕ) := SubsetPlacement.Subset (Fin N) k × Fin (N * h)

def query {N k h : ℕ} (c : Column N k h) : Finset (Fin N) := c.1.val

theorem query_card {N k h : ℕ} (c : Column N k h) : (query c).card = k := c.1.property

theorem card_columns (N k h : ℕ) : Fintype.card (Column N k h) = SubsetHelper.side N k h := by
  simp [Column, SubsetPlacement.Subset, SubsetHelper.side]
  ring

theorem query_types {N k h : ℕ} (hN : 0 < N) (hh : 0 < h) :
    (univ : Finset (Column N k h)).image query = (univ : Finset (Fin N)).powersetCard k := by
  ext S
  constructor
  · intro hS
    obtain ⟨c, _, rfl⟩ := mem_image.mp hS
    exact mem_powersetCard.mpr ⟨subset_univ _, query_card c⟩
  · intro hS
    have hz : 0 < N * h := Nat.mul_pos hN hh
    exact mem_image.mpr ⟨(⟨S, (mem_powersetCard.mp hS).2⟩, ⟨0, hz⟩), mem_univ _, rfl⟩

theorem card_query_types {N k h : ℕ} (hN : 0 < N) (hh : 0 < h) :
    ((univ : Finset (Column N k h)).image query).card = N.choose k := by
  rw [query_types hN hh, card_powersetCard, card_univ, Fintype.card_fin]

theorem query_repetitions {N k h : ℕ} (S : SubsetPlacement.Subset (Fin N) k) :
    ((univ : Finset (Column N k h)).filter fun c => query c = S.val).card = N * h := by
  have he : (univ : Finset (Column N k h)).filter (fun c => query c = S.val) =
      {S} ×ˢ (univ : Finset (Fin (N * h))) := by
    ext c
    rcases c with ⟨c, z⟩
    simp [query, Subtype.val_inj, eq_comm]
  rw [he, card_product, card_singleton, one_mul, card_univ, Fintype.card_fin]

/-- A full timeline serving every actual column. The trajectories include
all movement between intervals. Only internal edge disjointness is needed. -/
structure ColumnQueries (N k m h b : ℕ) (lam : ℝ) where
  horizon : ℕ
  path : Fin m → ℕ → AddCircle (SubsetHelper.inputBits N k h b : ℝ)
  first : Column N k h → ℕ
  last : Column N k h → ℕ
  ordered : ∀ c, first c ≤ last c
  bounded : ∀ c, last c ≤ horizon
  disjoint : (Set.univ : Set (Column N k h)).PairwiseDisjoint fun c => Ico (first c) (last c)
  cover : ∀ c, ∀ a ∈ query c, ∃ t ∈ Icc (first c) (last c), ∃ i, ∃ z,
    dist z (QueryMovement.centre (SubsetHelper.inputBits N k h b) N a) ≤
      SubsetHelper.side N k h * b ∧
    dist z (path i t) ≤ lam * SubsetHelper.inputBits N k h b

namespace ColumnQueries

variable {N k m h b : ℕ} {lam : ℝ}
variable [NeZero m]

def maxCost (Q : ColumnQueries N k m h b lam) : ℝ :=
  LeanMachine.QueryMovement.elapsed (LeanMachine.QueryMovement.maxStep Q.path) Q.horizon

def totalCost (Q : ColumnQueries N k m h b lam) : ℝ :=
  LeanMachine.QueryMovement.variation Q.path Q.horizon

theorem maxCost_nonneg (Q : ColumnQueries N k m h b lam) : 0 ≤ Q.maxCost :=
  LeanMachine.QueryMovement.elapsed_nonneg
    (fun e _ => LeanMachine.QueryMovement.maxStep_nonneg Q.path e) le_rfl

theorem maxCost_le_total (Q : ColumnQueries N k m h b lam) : Q.maxCost ≤ Q.totalCost :=
  LeanMachine.QueryMovement.elapsed_maxStep_le_variation Q.path Q.horizon

/-- Every representative-time interface is a zero-length interval
interface, with exactly the same trajectories and movement bill. -/
def ofRepresentatives (n : ℕ)
    (Y : Fin m → ℕ → AddCircle (SubsetHelper.inputBits N k h b : ℝ))
    (time : Column N k h → ℕ) (ht : ∀ c, time c ≤ n)
    (hc : ∀ c, ∀ a ∈ query c, ∃ i,
      dist (QueryMovement.centre (SubsetHelper.inputBits N k h b) N a) (Y i (time c)) ≤
        lam * SubsetHelper.inputBits N k h b) : ColumnQueries N k m h b lam where
  horizon := n
  path := Y
  first := time
  last := time
  ordered := fun _ => le_rfl
  bounded := ht
  disjoint := by intro c hc c' hc' hne; simp
  cover := by
    intro c a ha
    obtain ⟨i, hi⟩ := hc c a ha
    exact ⟨time c, by simp, i, QueryMovement.centre (SubsetHelper.inputBits N k h b) N a,
      by simp; positivity, hi⟩

end ColumnQueries
end
end SourceCovers.SubsetMovement

import LeanMachine.CosetRecords
import LeanMachine.DisjointSumsExtension

/-! # Separating parity cosets by recoverable coordinate views

Kernel shifts align a helper view. Recovery then supplies one more coordinate,
so any parity block covered by that view and coordinate has a determined sum.
The resulting record criterion is abstract: compatibility with a recovery
relation is an explicit hypothesis, not a consequence proved in this module.
-/

namespace LeanMachine.DisjointSums

open Finset

variable {ι κ A : Type*} [Finite κ] [AddCommGroup A]
variable (D : DisjointSums ι κ) (C : Set (ι → A))
variable (hstable : ∀ x ∈ C, ∀ z : ι → A, D.encode z = 0 → x + z ∈ C)

include hstable in
/-- One recovered coordinate completes a block whose other coordinates are in
the view. Neither membership of `i` in the block nor its exclusion from `S`
is required. -/
theorem encode_eq_of_recovery_view (S : Set ι) (i : ι) (k : κ)
    (hrecover : ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v S → u i = v i)
    (hcover : (↑(D.support k) : Set ι) ⊆ insert i S)
    {x y : ι → A} (hx : x ∈ C) (hy : y ∈ C)
    (hsums : ∀ l, (↑(D.support l) : Set ι) ⊆ S → D.encode x l = D.encode y l) :
    D.encode x k = D.encode y k := by
  obtain ⟨z, hz, hview⟩ := D.exists_kernel_shift S x y hsums
  have hi := hrecover (x + z) (hstable x hx z hz) y hy hview
  have hblock : Set.EqOn (x + z) y (↑(D.support k) : Set ι) := by
    intro j hj
    rcases Set.mem_insert_iff.mp (hcover hj) with rfl | hjS
    · exact hi
    · exact hview hjS
  calc
    D.encode x k = D.encode (x + z) k := by
      have he : D.encode (x + z) = D.encode x := by rw [map_add, hz, add_zero]
      exact (congrFun he k).symm
    _ = D.encode y k := by
      apply sum_congr rfl
      intro j hj
      exact hblock hj

include hstable in
/-- It suffices that each unrecorded block has one recovery view covering all
but its recovered coordinate, and every block fully inside that view is
recorded. The view may be chosen separately for each unrecorded block. -/
theorem encode_eq_of_record_cover (H : ι → Set ι) (T : Set κ)
    (hrecover : ∀ i, ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v (H i) → u i = v i)
    (hcover : ∀ k, k ∉ T → ∃ i,
      (↑(D.support k) : Set ι) ⊆ insert i (H i) ∧
      ∀ l, (↑(D.support l) : Set ι) ⊆ H i → l ∈ T)
    {x y : ι → A} (hx : x ∈ C) (hy : y ∈ C)
    (hrecord : Set.EqOn (D.encode x) (D.encode y) T) :
    D.encode x = D.encode y := by
  classical
  funext k
  by_cases hk : k ∈ T
  · exact hrecord hk
  · obtain ⟨i, hblock, hview⟩ := hcover k hk
    exact D.encode_eq_of_recovery_view C hstable (H i) i k (hrecover i)
      hblock hx hy (fun l hl => hrecord (hview l hl))

include hstable in
/-- The standard template hypotheses imply record separation: compatibility
at nonincident coordinates, all fully viewed blocks recorded, and all
all-incident blocks recorded. Compatibility remains an explicit premise. -/
theorem encode_eq_of_compatibility (H : ι → Set ι) (T : Set κ)
    (hrecover : ∀ i, ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v (H i) → u i = v i)
    (hcompat : ∀ k i, i ∈ D.support k → i ∉ H i →
      (↑(D.support k) : Set ι) ⊆ insert i (H i))
    (hinternal : ∀ i k, (↑(D.support k) : Set ι) ⊆ H i → k ∈ T)
    (hincident : ∀ k, (∀ i ∈ D.support k, i ∈ H i) → k ∈ T)
    {x y : ι → A} (hx : x ∈ C) (hy : y ∈ C)
    (hrecord : Set.EqOn (D.encode x) (D.encode y) T) :
    D.encode x = D.encode y := by
  classical
  apply D.encode_eq_of_record_cover C hstable H T hrecover ?_ hx hy hrecord
  intro k hk
  have hn : ¬ ∀ i ∈ D.support k, i ∈ H i := fun h => hk (hincident k h)
  push Not at hn
  obtain ⟨i, hik, hi⟩ := hn
  exact ⟨i, hcompat k i hik hi, hinternal i⟩

/-- The selected parity sums, with the record indexed only by selected blocks. -/
def syndromeRecord (T : Set κ) (x : ι → A) : T → A := fun k => D.encode x k

include hstable in
/-- Exact attained-record count for an invariant code satisfying the cover
criterion. The record need not separate cosets outside `C`. This `Nat.card`
identity is general; quantitative code-size applications use finite sets. -/
theorem card_eq_kernel_mul_record_image (H : ι → Set ι) (T : Set κ)
    (hrecover : ∀ i, ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v (H i) → u i = v i)
    (hcover : ∀ k, k ∉ T → ∃ i,
      (↑(D.support k) : Set ι) ⊆ insert i (H i) ∧
      ∀ l, (↑(D.support l) : Set ι) ⊆ H i → l ∈ T) :
    Nat.card C = Nat.card (D.encode (A := A)).ker *
      Nat.card (D.syndromeRecord T '' C) := by
  apply CosetRecords.card_eq_subgroup_mul_image D.encode.ker C (D.syndromeRecord T)
  · intro x hx z hz
    exact hstable x hx z hz
  · intro x hx z hz
    have hz' : D.encode z = 0 := hz
    funext k
    change D.encode (x + z) k = D.encode x k
    rw [map_add, hz', add_zero]
  · intro x hx y hy hrecord
    change D.encode (y - x) = 0
    have heq := D.encode_eq_of_record_cover C hstable H T hrecover hcover hx hy
      (fun k hk => congrFun hrecord ⟨k, hk⟩)
    rw [map_sub, heq, sub_self]

end LeanMachine.DisjointSums

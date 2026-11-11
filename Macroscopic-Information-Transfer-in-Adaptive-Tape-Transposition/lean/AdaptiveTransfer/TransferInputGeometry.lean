import AdaptiveTransfer.InputErosion
import AdaptiveTransfer.TransferClockShadow

/-! Valid-coordinate dilation, physical input boundaries and eroded reads.
The geometric bounds include every input head of the actual compiler. -/

namespace AdaptiveTransfer
open Finset Transpose Transpose.Tape MergeDepth
open TapeStorageRates TapeStorageRates.Native TransferClock
attribute [local instance] Classical.propDecidable

def inputDilation {L : ℕ} (S : Finset (Fin L)) (R : ℕ) : Finset (Fin L) :=
  univ.filter fun p => ∃ j ∈ S, |(p.val : ℤ) - (j.val : ℤ)| ≤ R

def inputBoundary (L R : ℕ) : Finset (Fin L) :=
  univ.filter fun p => p.val < R ∨ L ≤ p.val + R

theorem outside_shadow_in_boundary {L R : ℕ} {p : Fin L} {z : ℤ}
    (hz : ¬ (0 ≤ z ∧ z < L)) (hnear : |(p.val : ℤ) - z| ≤ R) :
    p ∈ inputBoundary L R := by
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  have hh := abs_le.mp hnear
  have hp := p.isLt
  by_cases hz0 : 0 ≤ z
  · right
    have hzL : (L : ℤ) ≤ z := by omega
    omega
  · left
    omega

/-- A nearby valid raw address lies in the dilation when its source address
is valid, and otherwise lies in the physical input boundary. -/
theorem shadow_in_dilation_or_boundary {L R : ℕ} {S : Finset (Fin L)} {p : Fin L} {z : ℤ}
    (hnear : |(p.val : ℤ) - z| ≤ R)
    (hsource : ∀ j : Fin L, z = (j.val : ℤ) → j ∈ S) :
    p ∈ inputDilation S R ∪ inputBoundary L R := by
  by_cases hz : 0 ≤ z ∧ z < L
  · let j : Fin L := ⟨z.toNat, by omega⟩
    have he : z = (j.val : ℤ) := by dsimp [j]; omega
    exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, j, hsource j he, by simpa only [← he] using hnear⟩)
  · exact mem_union_right _ (outside_shadow_in_boundary hz hnear)

noncomputable def inputReadSteps {k : ℕ} (τ : Trace k) (T : ℕ) (U : Finset ℤ) : Finset ℕ :=
  (range T).filter fun u => τ.input u ∈ U

/-- An actual simulator read of the radius-3s erosion projects to an actual
live source read of U. No source correctness or shared trace is required. -/
theorem actual_eroded_read_projects {M : TM} {s t u : ℕ} {w : List Bool}
    (hs : 0 < s) (ht : 1 ≤ t) (H : HaltsAt M w t) {U : Finset ℤ}
    (hu : u ∈ inputReadSteps (trace (machine M hs) w) (alignedTime s t) (inputErosion U (3 * s))) :
    sourceClock s t u ∈ inputReadSteps (trace M w) t U := by
  obtain ⟨huT, hread⟩ := mem_filter.mp hu
  have hshadow := actual_head_shadow hs ht H (mem_range.mp huT) none
  change |(trace (machine M hs) w).input u - (trace M w).input (sourceClock s t u)| ≤ 3 * (s : ℤ) at hshadow
  refine mem_filter.mpr ⟨mem_range.mpr (sourceClock_lt ht u), ?_⟩
  exact inputErosion_shadow_mem hread (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hshadow)

end AdaptiveTransfer

import SourceCovers.CoreProfiles
import SourceCovers.AdmissibleGeometry

set_option autoImplicit false

/-!
# Common bounds on actual sorted families

A hop envelope needs one supplied sorted order, with arbitrary ties.
The limit proof retains that order for both hops and variation.
-/

namespace SourceCovers

open Classical Finset
noncomputable section

namespace AdmissibleGeometry

variable {c β : ℝ} {N q : ℕ} (G : AdmissibleGeometry c β N q)

/-- A common normalized envelope in one arbitrary hop-sorted order. -/
def HasHopEnvelope (g : ℕ → ℝ) : Prop :=
  ∃ O : SortedCore G.core, ∀ i, O.hopProfile G.inputLength i ≤ g i

/-- For a nonnegative envelope, the normalized statement is exactly the
finite family-size bound; zero padding adds no further hypothesis. -/
theorem hasHopEnvelope_iff_hops_le {g : ℕ → ℝ} (hg : ∀ i, 0 ≤ g i) :
    G.HasHopEnvelope g ↔ ∃ O : SortedCore G.core,
      ∀ i (hi : i < O.families.length),
        (O.families[i].hops.card : ℝ) ≤ g i * G.inputLength := by
  have hL : (0 : ℝ) < G.inputLength := by exact_mod_cast G.inputLength_pos
  constructor
  · rintro ⟨O, h⟩
    refine ⟨O, fun i hi => ?_⟩
    simpa only [SortedCore.hopProfile, SortedCore.profile, dite_eq_left hi,
      div_le_iff₀ hL] using h i
  · rintro ⟨O, h⟩
    refine ⟨O, fun i => ?_⟩
    by_cases hi : i < O.families.length
    · simpa only [SortedCore.hopProfile, SortedCore.profile, dite_eq_left hi,
        div_le_iff₀ hL] using h i hi
    · simpa only [SortedCore.hopProfile, SortedCore.profile, dite_eq_right hi] using hg i

end AdmissibleGeometry
end
end SourceCovers

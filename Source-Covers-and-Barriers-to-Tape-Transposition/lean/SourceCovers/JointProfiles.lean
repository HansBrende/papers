import SourceCovers.AdmissibleGeometry
import SourceCovers.CoreProfiles
import LeanMachine.ProfileCompactness

set_option autoImplicit false

/-!
# Actual near-full sequences and joint numerical profiles

The hop and variation profiles use the same ordered complete families.
Natural index zero denotes the manuscript's first family. Summability is
proved from finite-sum bounds, not assumed in the definition of a profile.
No limiting geometry or convergence of the finite geometries' tails is used.
-/

namespace SourceCovers

open Classical Finset Filter LeanMachine
open scoped BigOperators Topology
noncomputable section

/-- The geometry and record alphabet may change with dimension. The order
is chosen once per geometry, with any fixed tie-breaking among equal sizes. -/
structure NearFullSequence (c β : ℝ) (N q : ℕ) where
  geometry : ℕ → AdmissibleGeometry c β N q
  order : ∀ ν, SortedCore (geometry ν).core
  dimension_tendsto : Tendsto (fun ν => (geometry ν).d) atTop atTop
  outside_tendsto : Tendsto
    (fun ν => ((geometry ν).a0 : ℝ) / (geometry ν).inputLength) atTop (𝓝 0)
  deficit_tendsto : Tendsto (fun ν => (geometry ν).relativeDeficit) atTop (𝓝 0)

namespace NearFullSequence

variable {c β : ℝ} {N q : ℕ} (S : NearFullSequence c β N q)

/-- Choosing a hop order imposes no additional condition on a sequence
of admissible geometries satisfying the original three limit conditions. -/
def ofGeometry (G : ℕ → AdmissibleGeometry c β N q)
    (hd : Tendsto (fun ν => (G ν).d) atTop atTop)
    (ha : Tendsto (fun ν => ((G ν).a0 : ℝ) / (G ν).inputLength) atTop (𝓝 0))
    (hΔ : Tendsto (fun ν => (G ν).relativeDeficit) atTop (𝓝 0)) :
    NearFullSequence c β N q where
  geometry := G
  order := fun ν => Classical.choice (exists_sortedCore (G ν).core)
  dimension_tendsto := hd
  outside_tendsto := ha
  deficit_tendsto := hΔ

theorem inputLength_tendsto : Tendsto (fun ν => (S.geometry ν).inputLength) atTop atTop :=
  tendsto_atTop_mono (fun ν => (S.geometry ν).dimension_le_inputLength) S.dimension_tendsto

def hops (ν i : ℕ) : ℝ := (S.order ν).hopProfile (S.geometry ν).inputLength i

def variation (ν i : ℕ) : ℝ :=
  (S.order ν).variationProfile (S.geometry ν).x (S.geometry ν).inputLength i

theorem profile_mass_bounds (ν : ℕ) (s : Finset ℕ) :
    (∑ i ∈ s, S.hops ν i) ≤ c ∧ (∑ i ∈ s, S.variation ν i) ≤ 2 * c := by
  apply (S.order ν).profile_mass_bounds (S.geometry ν).work_walk
    (S.geometry ν).core_coloring (S.geometry ν).x (S.geometry ν).inputLength_pos
    (S.geometry ν).raw_step
  simpa only [AdmissibleGeometry.inputLength, Nat.cast_mul] using (S.geometry ν).runtime

/-- Every strictly increasing subsequence preserves all three near-full
conditions and the same geometry-dependent family ordering. -/
def subseq (φ : ℕ → ℕ) (hφ : StrictMono φ) : NearFullSequence c β N q where
  geometry := S.geometry ∘ φ
  order := fun ν => S.order (φ ν)
  dimension_tendsto := S.dimension_tendsto.comp hφ.tendsto_atTop
  outside_tendsto := S.outside_tendsto.comp hφ.tendsto_atTop
  deficit_tendsto := S.deficit_tendsto.comp hφ.tendsto_atTop

/-- A joint profile includes one common strictly increasing subsequence.
Its masses and tails are conclusions below, not certificate assumptions. -/
structure JointProfile where
  h : ℕ → ℝ
  v : ℕ → ℝ
  subsequence : ℕ → ℕ
  strictMono : StrictMono subsequence
  hops_tendsto : ∀ i, Tendsto (fun ν => S.hops (subsequence ν) i) atTop (𝓝 (h i))
  variation_tendsto : ∀ i, Tendsto (fun ν => S.variation (subsequence ν) i) atTop (𝓝 (v i))

/-- Extraction is simultaneous for the two profiles; it does not reorder
variation or extract an unrelated second subsequence. -/
theorem exists_jointProfile : Nonempty S.JointProfile := by
  obtain ⟨h, v, φ, hφ, hh, hv⟩ := ProfileCompactness.exists_joint_subsequence
    S.hops S.variation
    (fun ν i => (S.order ν).hopProfile_nonneg _ i)
    (fun ν i => (S.order ν).variationProfile_nonneg _ _ i)
    (fun ν s => (S.profile_mass_bounds ν s).1)
    (fun ν s => (S.profile_mass_bounds ν s).2)
  exact ⟨⟨h, v, φ, hφ, hh, hv⟩⟩

namespace JointProfile

variable {S} (P : S.JointProfile)

/-- These conclusions hold for every joint profile, not just for the one
chosen by the compactness proof. No convergence of finite tail masses is asserted. -/
theorem hop_mass :
    (∀ i, 0 ≤ P.h i) ∧ (∀ s : Finset ℕ, ∑ i ∈ s, P.h i ≤ c) ∧
      Summable P.h ∧ (∑' i, P.h i) ≤ c :=
  ProfileCompactness.limit_mass_of_finite_sums
    (fun ν i => (S.order (P.subsequence ν)).hopProfile_nonneg _ i)
    (fun ν s => (S.profile_mass_bounds (P.subsequence ν) s).1) P.hops_tendsto

theorem variation_mass :
    (∀ i, 0 ≤ P.v i) ∧ (∀ s : Finset ℕ, ∑ i ∈ s, P.v i ≤ 2 * c) ∧
      Summable P.v ∧ (∑' i, P.v i) ≤ 2 * c :=
  ProfileCompactness.limit_mass_of_finite_sums
    (fun ν i => (S.order (P.subsequence ν)).variationProfile_nonneg _ _ i)
    (fun ν s => (S.profile_mass_bounds (P.subsequence ν) s).2) P.variation_tendsto

theorem hop_antitone : Antitone P.h := by
  intro i j hij
  exact le_of_tendsto_of_tendsto' (P.hops_tendsto j) (P.hops_tendsto i)
    (fun ν => (S.order (P.subsequence ν)).hopProfile_antitone _ hij)

/-- The inherited ordering gives an individual rank bound in addition to
the total mass bound. Index `i` is the manuscript's rank `i+1`. -/
theorem hop_le_rank (i : ℕ) : P.h i ≤ c / (i + 1 : ℕ) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (i + 1 : ℕ))).mpr
  calc
    _ = ∑ _j ∈ range (i + 1), P.h i := by simp [mul_comm]
    _ ≤ ∑ j ∈ range (i + 1), P.h j :=
      sum_le_sum fun j hj => P.hop_antitone (by have := mem_range.mp hj; omega)
    _ ≤ c := P.hop_mass.2.1 _

/-- Finite selections commute with the dimension limit along this one
subsequence. The cutoff remains fixed in this statement. -/
theorem finite_sums_tendsto (s : Finset ℕ) :
    Tendsto (fun ν => ∑ i ∈ s, S.hops (P.subsequence ν) i) atTop
      (𝓝 (∑ i ∈ s, P.h i)) ∧
    Tendsto (fun ν => ∑ i ∈ s, S.variation (P.subsequence ν) i) atTop
      (𝓝 (∑ i ∈ s, P.v i)) :=
  ⟨tendsto_finsetSum s (fun i _ => P.hops_tendsto i),
    tendsto_finsetSum s (fun i _ => P.variation_tendsto i)⟩

/-- After deleting the first `R` entries, the next entry is indexed `R`. -/
def hopTail (R : ℕ) : ℝ := ∑' i, P.h (i + R)

def variationTail (R : ℕ) : ℝ := ∑' i, P.v (i + R)

/-- Exact mass decomposition identifies these shifts with the tails after
the first `R` families in the manuscript's one-based indexing. -/
theorem prefix_add_tail (R : ℕ) :
    (∑ i ∈ range R, P.h i) + P.hopTail R = ∑' i, P.h i ∧
    (∑ i ∈ range R, P.v i) + P.variationTail R = ∑' i, P.v i :=
  ⟨P.hop_mass.2.2.1.sum_add_tsum_nat_add R,
    P.variation_mass.2.2.1.sum_add_tsum_nat_add R⟩

theorem finite_tails_tendsto (R : ℕ) :
    Tendsto (fun J => ∑ i ∈ Ico R J, P.h i) atTop (𝓝 (P.hopTail R)) ∧
    Tendsto (fun J => ∑ i ∈ Ico R J, P.v i) atTop (𝓝 (P.variationTail R)) :=
  ⟨ProfileCompactness.finite_tail_tendsto P.hop_mass.2.2.1 R,
    ProfileCompactness.finite_tail_tendsto P.variation_mass.2.2.1 R⟩

/-- Summability was independently proved in the mass theorems above; these
are genuine nonnegative tails, not the totalized sum of a divergent series. -/
theorem tails_tendsto_zero :
    Tendsto P.hopTail atTop (𝓝 0) ∧ Tendsto P.variationTail atTop (𝓝 0) :=
  ⟨tendsto_sum_nat_add P.h, tendsto_sum_nat_add P.v⟩

theorem tails_nonneg (R : ℕ) : 0 ≤ P.hopTail R ∧ 0 ≤ P.variationTail R :=
  ⟨tsum_nonneg fun i => P.hop_mass.1 (i + R),
    tsum_nonneg fun i => P.variation_mass.1 (i + R)⟩

end JointProfile

end NearFullSequence
end
end SourceCovers

import SourceCovers.UniformDeficit

set_option autoImplicit false

/-!
# A fixed finite skeleton cannot support near-full correctness

An empty core has the explicit zero joint profile. The existing necessary
tail inequality rules it out, including zero exceptional families. Relabeling
the core and exceptions preserves the complete computation and correctness set.
-/

namespace SourceCovers

open Classical Finset Filter
open scoped Topology
noncomputable section

/-- Reclassify the same complete families around a proposed finite skeleton.
Only the labels and their outside-family bound change. -/
def AdmissibleGeometry.withSkeleton {c β : ℝ} {N q₀ q : ℕ}
    (G : AdmissibleGeometry c β N q₀) (E : Finset (ActualFamily G.xs G.T))
    (hE : E.card ≤ q) (a : ℕ)
    (hsize : ∀ F : ActualFamily G.xs G.T, F ∉ E → F.hops.card ≤ a) :
    AdmissibleGeometry c β N q :=
  { G with
    core := ∅
    core_coloring := G.core_coloring.mono (empty_subset _)
    exceptions := E
    exceptions_card := hE
    exceptions_disjoint := disjoint_empty_left _
    a0 := a
    outside_small := by simpa only [empty_union] using hsize }

/-- The zero profile gives a direct contradiction for every natural `q`,
without extracting a compact subsequence or assuming positive capacity. -/
theorem NearFullSequence.empty_core_false {c β : ℝ} {N q : ℕ}
    (S : NearFullSequence c β N q) (hcore : ∀ n, (S.geometry n).core = ∅) : False := by
  have hh (n i : ℕ) : S.hops n i = 0 :=
    (S.order n).hopProfile_eq_zero _ (by simp [hcore n])
  have hv (n i : ℕ) : S.variation n i = 0 :=
    (S.order n).variationProfile_eq_zero _ _ (by simp [hcore n])
  let P : S.JointProfile :=
    { h := fun _ => 0
      v := fun _ => 0
      subsequence := id
      strictMono := strictMono_id
      hops_tendsto := fun i => by simpa only [hh] using (tendsto_const_nhds (x := (0 : ℝ)))
      variation_tendsto := fun i => by simpa only [hv] using (tendsto_const_nhds (x := (0 : ℝ))) }
  have h := P.necessary_hop_tail (K := 0) (R := 0) (M := 2) (by decide) (by decide)
  have hbad : (1 : ℝ) / (2 * 8 ^ q) ≤ 0 := by
    convert h using 1 <;> norm_num [JointProfile.hopTail, JointProfile.variationTail, P]
  exact (not_le_of_gt (by positivity)) hbad

/-- Uniform exclusion for an empty selected core; the full geometry remains. -/
theorem empty_core_uniform_deficit (c β : ℝ) (N q : ℕ) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ G : AdmissibleGeometry c β N q,
      G.core = ∅ → d₀ ≤ G.d → (G.a0 : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) :=
  uniform_deficit_of_no_nearFull (fun G => G.core = ∅)
    (fun S hcore => S.empty_core_false hcore)

/-- A chosen skeleton need not match the original core/exception labels.
The constants are uniform over every positive width and original labeling. -/
theorem finite_skeleton_uniform_deficit (c β : ℝ) (N q : ℕ) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ {q₀ : ℕ} (G : AdmissibleGeometry c β N q₀)
      (E : Finset (ActualFamily G.xs G.T)), E.card ≤ q → ∀ a : ℕ,
      (∀ F : ActualFamily G.xs G.T, F ∉ E → F.hops.card ≤ a) →
      d₀ ≤ G.d → (a : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  obtain ⟨ε, hε, d₀, h⟩ := empty_core_uniform_deficit c β N q
  exact ⟨ε, hε, d₀, fun G E hE a hsize hd ha =>
    h (G.withSkeleton E hE a hsize) rfl hd ha⟩

/-- Every sufficiently correct geometry needs more than `q` actual complete
families of size greater than the same positive fraction of its input length. -/
theorem large_family_count_of_small_deficit (c β : ℝ) (N q : ℕ) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ {q₀ : ℕ} (G : AdmissibleGeometry c β N q₀),
      d₀ ≤ G.d → G.deficit < ε * G.inputLength →
        q < (univ.filter fun F : ActualFamily G.xs G.T =>
          ε * G.inputLength < (F.hops.card : ℝ)).card := by
  obtain ⟨ε, hε, d₀, h⟩ := finite_skeleton_uniform_deficit c β N q
  refine ⟨ε, hε, d₀, fun G hd hΔ => ?_⟩
  by_contra hcount
  have hsize : ∀ F : ActualFamily G.xs G.T,
      F ∉ univ.filter (fun F => ε * G.inputLength < (F.hops.card : ℝ)) →
        F.hops.card ≤ ⌊ε * G.inputLength⌋₊ := by
    intro F hF
    apply Nat.le_floor
    simpa only [mem_filter, mem_univ, true_and, not_lt] using hF
  exact (not_le_of_gt hΔ)
    (h G _ (Nat.le_of_not_gt hcount) _ hsize hd (Nat.floor_le (by positivity))).1

end
end SourceCovers

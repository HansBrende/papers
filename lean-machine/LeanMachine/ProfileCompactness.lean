import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Coordinatewise compactness and profile mass

Countable products of compact intervals supply one common subsequence.
Finite-sum budgets pass to every coordinatewise limit, independently of
how that limit was obtained. This does not exchange an infinite sum with
the sequence limit or assert uniform control of the original tails.
-/

namespace LeanMachine.ProfileCompactness

open Filter Finset
open scoped BigOperators Topology

/-- A coordinate-dependent box suffices for a common subsequence. -/
theorem exists_bounded_subsequence {ι : Type*} [Countable ι]
    (f : ℕ → ι → ℝ) (B : ι → ℝ)
    (hf : ∀ n i, 0 ≤ f n i ∧ f n i ≤ B i) :
    ∃ (g : ι → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ i, 0 ≤ g i ∧ g i ≤ B i) ∧
      ∀ i, Tendsto (fun n => f (φ n) i) atTop (𝓝 (g i)) := by
  have hs : IsCompact (Set.Icc (0 : ι → ℝ) B) := isCompact_Icc
  obtain ⟨g, hg, φ, hφ, hlim⟩ := hs.tendsto_subseq
    (x := f) (fun n => ⟨fun i => (hf n i).1, fun i => (hf n i).2⟩)
  exact ⟨g, φ, hφ, fun i => ⟨hg.1 i, hg.2 i⟩, tendsto_pi_nhds.mp hlim⟩

/-- Every coordinatewise limit retains the mass budget. Neither countability
nor the construction of a particular subsequence is needed here. -/
theorem limit_mass_of_finite_sums {α ι : Type*} {l : Filter α} [l.NeBot]
    {f : α → ι → ℝ} {g : ι → ℝ} {C : ℝ}
    (hnonneg : ∀ n i, 0 ≤ f n i)
    (hbudget : ∀ n (S : Finset ι), ∑ i ∈ S, f n i ≤ C)
    (hlim : ∀ i, Tendsto (fun n => f n i) l (𝓝 (g i))) :
    (∀ i, 0 ≤ g i) ∧ (∀ S : Finset ι, ∑ i ∈ S, g i ≤ C) ∧
      Summable g ∧ (∑' i, g i) ≤ C := by
  have hg : ∀ i, 0 ≤ g i := fun i => ge_of_tendsto' (hlim i) (fun n => hnonneg n i)
  have hsum : ∀ S : Finset ι, ∑ i ∈ S, g i ≤ C := fun S =>
    le_of_tendsto' (tendsto_finsetSum S (fun i _ => hlim i)) (fun n => hbudget n S)
  exact ⟨hg, hsum, summable_of_sum_le hg hsum, Real.tsum_le_of_sum_le hg hsum⟩

/-- Uniform finite-sum budgets give a summable subsequential profile. -/
theorem exists_profile_subsequence {ι : Type*} [Countable ι]
    (f : ℕ → ι → ℝ) {C : ℝ}
    (hnonneg : ∀ n i, 0 ≤ f n i)
    (hbudget : ∀ n (S : Finset ι), ∑ i ∈ S, f n i ≤ C) :
    ∃ (g : ι → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ i, Tendsto (fun n => f (φ n) i) atTop (𝓝 (g i))) ∧
      (∀ i, 0 ≤ g i) ∧ (∀ S : Finset ι, ∑ i ∈ S, g i ≤ C) ∧
      Summable g ∧ (∑' i, g i) ≤ C := by
  classical
  have hb : ∀ n i, 0 ≤ f n i ∧ f n i ≤ C := by
    intro n i
    exact ⟨hnonneg n i, by simpa only [sum_singleton] using hbudget n {i}⟩
  obtain ⟨g, φ, hφ, _, hlim⟩ := exists_bounded_subsequence f (fun _ => C) hb
  exact ⟨g, φ, hφ, hlim,
    limit_mass_of_finite_sums (fun n => hnonneg (φ n)) (fun n => hbudget (φ n)) hlim⟩

/-- Hop and variation coordinates converge along the same subsequence.
Their budgets remain separate; apply `limit_mass_of_finite_sums` to either
channel of any such subsequence to obtain its own mass bound. -/
theorem exists_joint_subsequence (h v : ℕ → ℕ → ℝ) {cH cV : ℝ}
    (hh0 : ∀ n i, 0 ≤ h n i) (hv0 : ∀ n i, 0 ≤ v n i)
    (hhSum : ∀ n (S : Finset ℕ), ∑ i ∈ S, h n i ≤ cH)
    (hvSum : ∀ n (S : Finset ℕ), ∑ i ∈ S, v n i ≤ cV) :
    ∃ (hLim vLim : ℕ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ i, Tendsto (fun n => h (φ n) i) atTop (𝓝 (hLim i))) ∧
      ∀ i, Tendsto (fun n => v (φ n) i) atTop (𝓝 (vLim i)) := by
  let f := fun n (p : Bool × ℕ) => cond p.1 (v n p.2) (h n p.2)
  let B := fun p : Bool × ℕ => cond p.1 cV cH
  have hb : ∀ n p, 0 ≤ f n p ∧ f n p ≤ B p := by
    rintro n ⟨b, i⟩
    cases b with
    | false => exact ⟨hh0 n i, by simpa [f, B] using hhSum n {i}⟩
    | true => exact ⟨hv0 n i, by simpa [f, B] using hvSum n {i}⟩
  obtain ⟨g, φ, hφ, _, hlim⟩ := exists_bounded_subsequence f B hb
  exact ⟨fun i => g (false, i), fun i => g (true, i), φ, hφ,
    fun i => hlim (false, i), fun i => hlim (true, i)⟩

/-- After fixing the lower cutoff, finite tail windows of a summable profile
converge to its actual infinite tail. -/
theorem finite_tail_tendsto {g : ℕ → ℝ} (hg : Summable g) (R : ℕ) :
    Tendsto (fun J => ∑ i ∈ Ico R J, g i) atTop (𝓝 (∑' i, g (i + R))) := by
  have h := ((summable_nat_add_iff R).mpr hg).tendsto_sum_tsum_nat.comp
    (tendsto_sub_atTop_nat R)
  simpa only [Function.comp_def, sum_Ico_eq_sum_range, Nat.add_comm] using h

end LeanMachine.ProfileCompactness

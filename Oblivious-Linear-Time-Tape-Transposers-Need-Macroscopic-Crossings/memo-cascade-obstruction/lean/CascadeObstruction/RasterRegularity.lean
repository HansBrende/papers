import TransposeFollowup.ActualStageRegularity
import TransposeFollowup.FiniteAffineSums
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.HeineCantor

/-! A bounded number of straight interpolants suffices for stage regularity.
All normalized parameters lie in compact intervals; a single finite-product
subsequence replaces separate formulas for every limiting endpoint. -/

namespace CascadeObstruction.Raster

open Set Filter Topology
open scoped BigOperators
open TransposeFollowup.AffineMotion TransposeFollowup.RegularMotion

set_option autoImplicit false

/-- Slope, start, and duration of one normalized straight block. -/
abbrev Parameters (a : ℝ) := Icc (-1 : ℝ) 1 × Icc (0 : ℝ) a × Icc (0 : ℝ) a

noncomputable def ramp {a : ℝ} (p : Parameters a) (s : ℝ) : ℝ :=
  (p.1 : ℝ) * clippedRamp p.2.2 p.2.1 1 s

noncomputable def curve {a : ℝ} {J : ℕ} (p : Fin J → Parameters a) (s : ℝ) : ℝ :=
  ∑ j, ramp (p j) s

theorem cover_mul_const {J : ℕ} {a : ℝ} {f : ℝ → ℝ}
    (hf : HasAffineIntervalCover J f a) (c : ℝ) :
    HasAffineIntervalCover J (fun s => c * f s) a := by
  obtain ⟨l, r, hcover, hpieces⟩ := hf
  refine ⟨l, r, hcover, fun j => ?_⟩
  obtain ⟨u, v, huv⟩ := hpieces j
  refine ⟨c * u, c * v, fun s hs => ?_⟩
  change c * f s = _
  rw [huv s hs]
  ring

theorem curve_cover {a : ℝ} (ha : 0 ≤ a) {J : ℕ}
    (p : Fin J → Parameters a) : HasAffineIntervalCover (3 ^ J) (curve p) a := by
  apply HasAffineIntervalCover.sum_fin ha
  intro j
  exact cover_mul_const
    (clippedRamp_cover ha (p j).2.2.property.1 (p j).2.1.property.1 (by norm_num)) _

theorem curve_continuous {a : ℝ} {J : ℕ} :
    Continuous (fun z : (Fin J → Parameters a) × ℝ => curve z.1 z.2) := by
  unfold curve ramp clippedRamp
  fun_prop

/-- Every sequence of bounded finite ramp sums has a finite-affine uniform
subsequential limit. No convergence of its individual parameters is assumed. -/
theorem curve_subsequence {a : ℝ} (ha : 0 ≤ a) {J : ℕ}
    (p : ℕ → Fin J → Parameters a) :
    ∃ (φ : ℕ → ℕ) (q : ℝ → ℝ), StrictMono φ ∧
      HasAffineIntervalCover (3 ^ J) q a ∧
      TendstoUniformlyOn (fun i => curve (p (φ i))) q atTop (Icc 0 a) := by
  obtain ⟨p₀, φ, hφ, hp⟩ := CompactSpace.tendsto_subseq p
  refine ⟨φ, curve p₀, hφ, curve_cover ha p₀, ?_⟩
  have hc : UniformContinuousOn
      (fun z : (Fin J → Parameters a) × ℝ => curve z.1 z.2)
      (univ ×ˢ Icc 0 a) :=
    ((isCompact_univ : IsCompact (univ : Set (Fin J → Parameters a))).prod
      isCompact_Icc).uniformContinuousOn_of_continuous curve_continuous.continuousOn
  have hu := UniformContinuousOn.tendstoUniformlyOn
    (F := fun p : Fin J → Parameters a => curve p) hc (x := p₀) (mem_univ p₀)
  simp only [nhdsWithin_univ] at hu
  exact fun u hu' => hp.eventually (hu u hu')

/-- An actual frozen integer stage is regular if its normalized path has a
bounded finite-ramp approximation with bounded unscaled error. -/
theorem regular_of_ramp_approximation {a C : ℝ} (ha : 0 ≤ a) {J : ℕ}
    {V : ℕ → ℝ} {A L : ℕ → ℕ} {hs : ℕ → ℕ → ℤ}
    (p : ℕ → Fin J → Parameters a)
    (herr : ∀ i s, s ∈ Icc 0 a →
      dist (curve (p i) s)
        (((hs i (A i + min ⌊V i * s⌋₊ (L i)) - hs i (A i) : ℤ) : ℝ) / V i)
        ≤ C / V i) :
    HasRegularStageSubsequences a V A L hs := by
  intro φ hφ _hL hV
  obtain ⟨ψ, q, hψ, hq, hconv⟩ := curve_subsequence ha (fun i => p (φ i))
  refine ⟨3 ^ J, ψ, q, hψ, hq, ?_⟩
  exact uniform_limit_of_vanishing_error hconv
    (tendsto_const_nhds.div_atTop (hV.comp hψ.tendsto_atTop))
    (Eventually.of_forall fun i s hs' => herr (φ (ψ i)) s hs')

end CascadeObstruction.Raster

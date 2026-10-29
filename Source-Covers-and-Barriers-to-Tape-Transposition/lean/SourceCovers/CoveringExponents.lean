import SourceCovers.MetricSharing
import LeanMachine.PowerEnvelope

set_option autoImplicit false

/-! Power-law raw covers specialize the metric criterion. The same original
hop order and dimension-independent cutoffs serve every geometric bound. -/

namespace SourceCovers

open Classical Filter LeanMachine
open scoped Topology
noncomputable section

namespace AdmissibleGeometry

/-- Power bounds on actual phase-mean raw covering numbers. The cutoff
sets and all constants are supplied independently of the geometry. -/
def HasRawPowerCover {c β : ℝ} {N : ℕ} (G : AdmissibleGeometry c β N 2)
    (O : SortedCore G.core) (radii : Set ℕ) (cutoffs : ℕ → Set ℕ)
    (H u s δ₀ : ℕ → ℝ) : Prop :=
  ∀ R ∈ radii, ∀ J ∈ cutoffs R, R ≤ J → ∀ δ : ℝ, 0 < δ → δ < δ₀ R →
    G.prefixMeanRawCover O J R (2 * R + 2) (by omega) δ ≤
      H R * (J + 1 : ℝ) ^ u R * δ ^ (-s R)

/-- The original unshifted cutoff budget implies the slightly more
permissive shifted budget, including cutoff zero. -/
theorem hasRawPowerCover_of_unshifted {c β : ℝ} {N : ℕ}
    (G : AdmissibleGeometry c β N 2) (O : SortedCore G.core)
    {radii : Set ℕ} {cutoffs : ℕ → Set ℕ} {H u s δ₀ : ℕ → ℝ}
    (hH : ∀ R ∈ radii, 0 ≤ H R) (hu : ∀ R ∈ radii, 0 ≤ u R)
    (hcover : ∀ R ∈ radii, ∀ J ∈ cutoffs R, R ≤ J →
      ∀ δ : ℝ, 0 < δ → δ < δ₀ R →
        G.prefixMeanRawCover O J R (2 * R + 2) (by omega) δ ≤
          H R * (J : ℝ) ^ u R * δ ^ (-s R)) :
    G.HasRawPowerCover O radii cutoffs H u s δ₀ := by
  intro R hR J hJ hRJ δ hδ hδ₀
  exact (hcover R hR J hJ hRJ δ hδ hδ₀).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg J)
        (by linarith) (hu R hR)) (hH R hR)) (Real.rpow_nonneg hδ.le _))

end AdmissibleGeometry

/-- A power envelope with any positive exponent suffices when
`u < p * (1 - s)`. Common unbounded cutoff sets are allowed, and the
cover amplitudes and exponents may vary with the protected scale. -/
theorem power_metric_sharing_uniform_deficit {c β A p : ℝ} {N : ℕ}
    {radii : Set ℕ} {cutoffs : ℕ → Set ℕ} {H u s δ₀ : ℕ → ℝ}
    (hp : 0 < p) (hradii : ∀ R₀ : ℕ, ∃ R ≥ R₀, R ∈ radii)
    (hcutoffs : ∀ R ∈ radii, ∀ J₀ : ℕ, ∃ J ≥ J₀, J ∈ cutoffs R)
    (hδ₀ : ∀ R ∈ radii, 0 < δ₀ R) (hs : ∀ R ∈ radii, s R < 1)
    (hu : ∀ R ∈ radii, u R < p * (1 - s R)) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ G : AdmissibleGeometry c β N 2,
      ∀ O : SortedCore G.core,
      (∀ J, O.hopProfile G.inputLength J ≤ A / (J + 1 : ℝ) ^ p) →
      G.HasRawPowerCover O radii cutoffs H u s δ₀ →
      d₀ ≤ G.d → (G.a0 : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  have hex : ∀ R : ℕ, ∃ v : ℝ,
      R ∈ radii → 0 < v ∧ v < p ∧ u R < v * (1 - s R) := by
    intro R
    by_cases hR : R ∈ radii
    · obtain ⟨v, hv⟩ := PowerEnvelope.exists_balanced_exponent hp (hs R hR) (hu R hR)
      exact ⟨v, fun _ => hv⟩
    · exact ⟨1, fun h => False.elim (hR h)⟩
  choose v hv using hex
  let δ := fun R J : ℕ => (J + 1 : ℝ) ^ (-v R)
  let n := fun R J : ℕ => H R * (J + 1 : ℝ) ^ u R * δ R J ^ (-s R)
  let good := fun R => {J | J ∈ cutoffs R ∧ δ R J < δ₀ R}
  have hsmall : ∀ R ∈ radii, ∀ ε > 0, ∀ J₀ : ℕ, ∃ J ≥ J₀, J ∈ good R ∧
      δ R J < ε ∧ δ R J * n R J < ε ∧ (A / (J + 1 : ℝ) ^ p) / δ R J < ε := by
    intro R hR ε hε J₀
    obtain ⟨hd, hn, hη⟩ := PowerEnvelope.balanced_scale_limits
      (fun J : ℕ => by positivity : ∀ J : ℕ, 0 < (J + 1 : ℝ))
      (show Tendsto (fun J : ℕ => (J + 1 : ℝ)) atTop atTop by
        simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
          (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
      (hv R hR).1 (hv R hR).2.1 (hv R hR).2.2 A (H R)
    have hev := (hd.eventually (Iio_mem_nhds (hδ₀ R hR))).and
      ((hd.eventually (Iio_mem_nhds hε)).and
        ((hn.eventually (Iio_mem_nhds hε)).and (hη.eventually (Iio_mem_nhds hε))))
    obtain ⟨J₁, hJ₁⟩ := eventually_atTop.mp hev
    obtain ⟨J, hJ, hJs⟩ := hcutoffs R hR (max J₀ J₁)
    have hj := hJ₁ J ((le_max_right J₀ J₁).trans hJ)
    exact ⟨J, (le_max_left J₀ J₁).trans hJ, ⟨hJs, hj.1⟩, hj.2⟩
  obtain ⟨ε, hε, d₀, hgap⟩ := metric_sharing_uniform_deficit
    (c := c) (β := β) (N := N) hradii hsmall
  refine ⟨ε, hε, d₀, fun G O henv hcover => hgap G O ?_⟩
  intro R hR J hJ hRJ
  have hδ : 0 < δ R J := Real.rpow_pos_of_pos (by positivity) _
  exact ⟨hδ, henv J, hcover R hR J hJ.1 hRJ (δ R J) hδ hJ.2⟩

/-- No size envelope is needed for growth `u < 1 - s`. In particular,
cutoff-independent covering budgets are the special case `u = 0`. -/
theorem sublinear_metric_sharing_uniform_deficit {c β : ℝ} {N : ℕ}
    {radii : Set ℕ} {cutoffs : ℕ → Set ℕ} {H u s δ₀ : ℕ → ℝ}
    (hradii : ∀ R₀ : ℕ, ∃ R ≥ R₀, R ∈ radii)
    (hcutoffs : ∀ R ∈ radii, ∀ J₀ : ℕ, ∃ J ≥ J₀, J ∈ cutoffs R)
    (hδ₀ : ∀ R ∈ radii, 0 < δ₀ R) (hs : ∀ R ∈ radii, s R < 1)
    (hu : ∀ R ∈ radii, u R < 1 - s R) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ G : AdmissibleGeometry c β N 2,
      ∀ O : SortedCore G.core, G.HasRawPowerCover O radii cutoffs H u s δ₀ →
      d₀ ≤ G.d → (G.a0 : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  obtain ⟨ε, hε, d₀, hgap⟩ := power_metric_sharing_uniform_deficit
    (c := c) (β := β) (N := N) (A := c) (p := 1) (by norm_num) hradii hcutoffs
    hδ₀ hs (by simpa only [one_mul] using hu)
  exact ⟨ε, hε, d₀, fun G O =>
    hgap G O (fun J => by simpa using G.hopProfile_le_rank O J)⟩

end
end SourceCovers

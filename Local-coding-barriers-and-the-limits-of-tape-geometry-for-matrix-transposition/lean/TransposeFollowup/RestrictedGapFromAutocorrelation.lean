import TransposeFollowup.UniformSmoothedBandWitness
import TransposeFollowup.AutocorrelationFlatnessBarrier

/-! A restricted spectral gap from flatness of a fixed dyadic power of
the actual smoothed walk's autocorrelation. The canonical density is
symmetric; no transfer back to one-sided density flatness is needed.
Flatness remains an explicit hypothesis. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_restricted_gap_from_autocorrelation_flatness_above (k Nmin : ℕ) :
    ∃ N J₀ : ℕ, 0 < N ∧ Nmin ≤ N ∧ 0 < J₀ ∧
      ∀ C : ℝ, 0 < C → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ J : ℕ, J₀ ≤ J →
      ∀ {c : ℕ} (G : Fin c → Group), 0 < c → (∀ i, G i ∈ matrixEntryBox 2) →
      ∀ K : ℕ, 0 < K → 16384 * Real.pi ^ 2 * (2 : ℝ) ^ (3 * J) ≤ (K : ℝ) ^ 2 →
      (∀ j : ℕ, J ≤ j → ∀ m : ℕ, 2 * N * 2 ^ m ≤ j →
        C * Real.log (1 / (1 / 4 : ℝ) ^ j) / Real.log (1 / ε) < (2 : ℝ) ^ m →
        ∃ D : ℝ, 0 ≤ D ∧ D ^ 2 ≤ (2 : ℝ) ^ j ∧
          ∀ᵐ g ∂(Measure.haar : Measure Group),
            smoothedAutocorrelationIterate (generatorWalkMeasure G (2 ^ m)) ((1 / 4 : ℝ) ^ j) k g ≤
              ENNReal.ofReal D) →
      ∀ f : RealL2, ‖f‖ = 1 →
        (∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) →
        (∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0) →
        inner ℝ (averageOperator G f) f < 1 / 2 := by
  obtain ⟨r, hr, hselect⟩ := exists_uniform_smoothed_regular_high_band
  obtain ⟨Nbar, Jbar, _, _, _, hbarrier⟩ := exists_autocorrelationIterate_action_barrier 0 k hr
  obtain ⟨N, Jselect, hN, hNmax, hJselect, hscales⟩ := hselect (max Nmin Nbar)
  have hNbar : Nbar ≤ N := (le_max_right _ _).trans hNmax
  refine ⟨N, max Jselect Jbar, hN, (le_max_left _ _).trans hNmax,
    hJselect.trans_le (le_max_left _ _), ?_⟩
  intro C hC
  obtain ⟨ε₀, hε₀, hε₀one, hwitness⟩ := hscales C hC
  refine ⟨ε₀, hε₀, hε₀one, ?_⟩
  intro ε hε hεsmall J hJ c G hc hG K hK hgrid hflat f hf hs hmeans
  by_contra hnot
  have hcorr : 1 / 2 ≤ inner ℝ (averageOperator G f) f := le_of_not_gt hnot
  obtain ⟨j, F, m, hj, hF, _, _, hfreq, hm, hthreshold, hlower⟩ :=
    hwitness ε hε hεsmall J ((le_max_left _ _).trans hJ) G hc
      (fun i => ⟨hG i 0 0, hG i 1 0, hG i 1 1⟩) hK f hf hs hmeans hgrid hcorr
  have : IsProbabilityMeasure (generatorWalkMeasure G (2 ^ m)) := generatorWalkMeasure_probability G hc _
  rw [← groupActionAverage_mobiusHaarKernel_eq_integral _
    (by positivity : (0 : ℝ) < (1 / 4 : ℝ) ^ j)] at hlower
  obtain ⟨D, hD, hDsq, hbound⟩ := hflat j hj m hm hthreshold
  have hupper := hbarrier N j (2 ^ m) hNbar (((le_max_right _ _).trans hJ).trans hj) hm
    G hc hG ((1 / 4 : ℝ) ^ j) (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num)) F hF
    (fun ξ hξ => hfreq ξ (Or.inl hξ.le)) D hD hDsq hbound
  exact (not_lt_of_ge hlower) hupper

theorem exists_restricted_gap_from_autocorrelation_flatness (k : ℕ) :
    ∃ N J₀ : ℕ, 0 < N ∧ 0 < J₀ ∧
      ∀ C : ℝ, 0 < C → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ J : ℕ, J₀ ≤ J →
      ∀ {c : ℕ} (G : Fin c → Group), 0 < c → (∀ i, G i ∈ matrixEntryBox 2) →
      ∀ K : ℕ, 0 < K → 16384 * Real.pi ^ 2 * (2 : ℝ) ^ (3 * J) ≤ (K : ℝ) ^ 2 →
      (∀ j : ℕ, J ≤ j → ∀ m : ℕ, 2 * N * 2 ^ m ≤ j →
        C * Real.log (1 / (1 / 4 : ℝ) ^ j) / Real.log (1 / ε) < (2 : ℝ) ^ m →
        ∃ D : ℝ, 0 ≤ D ∧ D ^ 2 ≤ (2 : ℝ) ^ j ∧
          ∀ᵐ g ∂(Measure.haar : Measure Group),
            smoothedAutocorrelationIterate (generatorWalkMeasure G (2 ^ m)) ((1 / 4 : ℝ) ^ j) k g ≤
              ENNReal.ofReal D) →
      ∀ f : RealL2, ‖f‖ = 1 →
        (∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) →
        (∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0) →
        inner ℝ (averageOperator G f) f < 1 / 2 := by
  obtain ⟨N, J₀, hN, _, hJ₀, hgap⟩ :=
    exists_restricted_gap_from_autocorrelation_flatness_above k 0
  exact ⟨N, J₀, hN, hJ₀, hgap⟩

end TransposeFollowup.RealMobius

import Transpose.Tape.MStarRobust
import Transpose.Tape.Witnesses

/-!
# Theorem M* for adaptive machines (popular trace)

* `theoremMStar_level_adaptive`: every machine that transposes in time `≤ c L` has popular trace
  classes with `D / L → 0`; their representatives' rescaled trajectories have convergent
  subsequences; and every subsequential limit is 1-Lipschitz and satisfies (★). This is the case
  `W_i` = all matrix inputs, `m_i = 0` of `theoremMStar_level_robust` (`MStarRobust.lean`). The trace
  cost `traceBits_le` (`D ≤ C n b`) is in `MStarClass.lean`.
* `no_stationary_limits_class`: the representatives of trace classes with `D = o(L)` cannot all
  be macroscopically stationary.
* `adaptive_hyps_of_linearTime` and `linearTimeTransposable_popular_limits`: the link to the frozen
  statement (T).
-/

namespace Transpose.Tape.Impl

open Transpose MeasureTheory Filter Topology

open scoped ENNReal

/-! ### Theorem M* for adaptive machines -/

/-- **Theorem M\* for adaptive machines (popular trace)**: the case `W_i` = all matrix inputs,
`m_i = 0` of `theoremMStar_level_robust`. -/
theorem theoremMStar_level_adaptive {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    (hcorr : ∀ᶠ i in atTop, Transposes M (ns i) (entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, ∀ w ∈ matrixInputs (ns i) (entryBits (ns i)),
      ∃ T : ℕ, (T : ℝ) ≤ c * inputLength (ns i) ∧ HaltsAt M w T) :
    ∃ (Ts Ds : ℕ → ℕ) (Fs : ℕ → Set (List Bool)) (ws : ℕ → List Bool),
      (∀ᶠ i in atTop,
        TraceClass M (ns i) (entryBits (ns i)) (slotLen M (ns i)) (Ts i) (Fs i) (ws i) ∧
          (Ts i : ℝ) ≤ c * inputLength (ns i) ∧ 2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard) ∧
      (∀ᶠ i in atTop, Ds i ≤ traceConst M c * ns i * entryBits (ns i)) ∧
      Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin M.k → ℝ → ℝ, ∀ t,
        TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
          (Set.Icc 0 (horizon M c))) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin M.k → ℝ → ℝ,
        (∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
          (Set.Icc 0 (horizon M c))) →
        (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (horizon M c))) ∧
        ∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S → PiecewiseConstOn β S (horizon M c) →
          (∀ ℓ, volume {u | u ∈ Set.Icc 0 (horizon M c) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
          1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (horizon M c) p) + 2 * θ +
            2 * M.k * volume (S ∩ Set.Icc 0 (horizon M c)) := by
  obtain ⟨Ts, Ds, Fs, ws, hall, hDs, hDL, hex, hlim⟩ :=
    theoremMStar_level_robust (Ws := fun i => matrixInputs (ns i) (entryBits (ns i)))
      (ms := fun _ => 0) hns
      (Eventually.of_forall fun i => by rw [ncard_matrixInputs]; simp [inputLength])
      (by simp)
      ((hcorr.and htime).mono fun i h w hw => by
        obtain ⟨T, hT, hh⟩ := h.2 w hw
        exact ⟨T, hT, hh, correct_of_transposes h.1 hw hh⟩)
  exact ⟨Ts, Ds, Fs, ws, hall.mono fun i h => ⟨h.1, h.2.2⟩,
    hDs.mono fun i h => by simpa using h, hDL, hex, hlim⟩

/-! ### The frozen statement -/

/-- **The frozen (T) supplies the hypotheses of `theoremMStar_level_adaptive`** (with `2c`), along
any `n_i → ∞`. -/
theorem adaptive_hyps_of_linearTime {M : TM} {c : ℕ} (h : TransposesWithin M (fun L => c * (L + 1)))
    {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) :
    (∀ᶠ i in atTop, Transposes M (ns i) (entryBits (ns i))) ∧
    (∀ᶠ i in atTop, ∀ w ∈ matrixInputs (ns i) (entryBits (ns i)),
      ∃ T : ℕ, (T : ℝ) ≤ ((2 * c : ℕ) : ℝ) * inputLength (ns i) ∧ HaltsAt M w T) := by
  refine ⟨(hns.eventually_ge_atTop 1).mono fun i hi => transposes_of_transposesWithin h _ hi,
    (hns.eventually_ge_atTop 1).mono fun i hi => ?_⟩
  rintro w ⟨A, rfl⟩
  obtain ⟨T, hT, hh, -⟩ := (computesWithin_iff _ _).1 (h (ns i) hi A)
  refine ⟨T, ?_, hh⟩
  have hL : 1 ≤ inputLength (ns i) := by
    unfold inputLength entryBits
    have : 1 ≤ ns i * ns i := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have : T ≤ 2 * c * inputLength (ns i) := by nlinarith
  exact_mod_cast this

/-- **Under (T), the popular-trace limits satisfy (★).** If `LinearTimeTransposable` holds, then some
machine `M` and constant `c` have, along every `n_i → ∞`, popular trace classes with `D = o(L)`; a
subsequence of their representatives' rescaled trajectories converges uniformly; and every
subsequential limit is 1-Lipschitz and satisfies (★) with horizon `c₀ = horizon M (2c)`. So
exhibiting, for every machine, a sequence along which some popular-trace limit violates (★) would
refute (T). -/
theorem linearTimeTransposable_popular_limits (hT : LinearTimeTransposable) :
    ∃ (M : TM) (c : ℕ), ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ (Ts Ds : ℕ → ℕ) (Fs : ℕ → Set (List Bool)) (ws : ℕ → List Bool),
        (∀ᶠ i in atTop,
          TraceClass M (ns i) (entryBits (ns i)) (slotLen M (ns i)) (Ts i) (Fs i) (ws i) ∧
            2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard) ∧
        Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0) ∧
        (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin M.k → ℝ → ℝ, ∀ t,
          TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
            (Set.Icc 0 (horizon M ((2 * c : ℕ) : ℝ)))) ∧
        ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin M.k → ℝ → ℝ,
          (∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
            (Set.Icc 0 (horizon M ((2 * c : ℕ) : ℝ)))) →
          (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (horizon M ((2 * c : ℕ) : ℝ)))) ∧
          ∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S →
            PiecewiseConstOn β S (horizon M ((2 * c : ℕ) : ℝ)) →
            (∀ ℓ, volume {u | u ∈ Set.Icc 0 (horizon M ((2 * c : ℕ) : ℝ)) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
            1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (horizon M ((2 * c : ℕ) : ℝ)) p) + 2 * θ +
              2 * M.k * volume (S ∩ Set.Icc 0 (horizon M ((2 * c : ℕ) : ℝ))) := by
  obtain ⟨M, c, h⟩ := hT
  refine ⟨M, c, fun ns hns => ?_⟩
  obtain ⟨h1, h2⟩ := adaptive_hyps_of_linearTime h hns
  obtain ⟨Ts, Ds, Fs, ws, hall, -, hDL, hex, hlim⟩ := theoremMStar_level_adaptive hns h1 h2
  exact ⟨Ts, Ds, Fs, ws, hall.mono (fun i h => ⟨h.1, h.2.2⟩), hDL, hex, hlim⟩

/-- **No stationary limits for trace classes.** Along trace classes with `D = o(L)`, the
representatives' rescaled work-head trajectories cannot all converge uniformly to `0`. -/
theorem no_stationary_limits_class {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts Ds : ℕ → ℕ} {Fs : ℕ → Set (List Bool)} {ws : ℕ → List Bool}
    (hF : ∀ᶠ i in atTop,
      TraceClass M (ns i) (entryBits (ns i)) (slotLen M (ns i)) (Ts i) (Fs i) (ws i))
    (hD : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard)
    (hDL : Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hcorr : ∀ᶠ i in atTop, ClassCorrect M (ns i) (entryBits (ns i)) (Ts i) (Fs i))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i)) :
    ¬ ∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf M (ns i) (ws i) t) (fun _ => 0) atTop
      (Set.Icc 0 (horizon M c)) := by
  intro hconv
  obtain ⟨hS, hβ, hcl, hfail⟩ := theoremMStar_conclusion_can_fail M.k (horizon M c)
  exact hfail (theoremMStar_level_class (P := fun _ _ => 0) hns hF hD hDL hcorr htime hconv hS hβ
    hcl)

end Transpose.Tape.Impl

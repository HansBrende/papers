import Transpose.Tape.MStarDiagram

/-!
# Theorem M* and the Tape Coding Conjecture

Theorem M\* for code-carrying diagrams (`MStarDiagram.lean`) at the profile capacities, and what it
says about the Tape Coding Conjecture `RobustNoCode_TM` (`DefsCE.lean`).

* `theoremMStar_diagram_profile`: let valid `k`-walk diagrams of length `≤ c L_i` carry causal codes
  solving complete exchange at the profile capacities (`profileCap`) on sets of co-entropy
  `m_i = o(L_i)`. Then the rescaled walks have a uniformly convergent subsequence on `[0, c₀]`,
  `c₀ = c G + 1`, and every subsequential limit `P` is 1-Lipschitz, satisfies (★), has total excess
  level multiplicity `Σ_t ∫⁻ (#Λ_t(p) − 1) dp ≥ 1` and total range `1 + Σ_t |P_t([0, c₀])| ≤ k c₀`, and
  is not monotone on every tape.
* `mstar_of_robustNoCode_counterexamples`: **every family of counterexamples to the Tape Coding
  Conjecture satisfies (★)**: for fixed constants `k, G, c, C` and sizes `n_i → ∞`, any choice of
  diagrams and codes violating `RobustNoCode_TM` at the large `n_i` has limits as above.
* `mstar_of_not_robustNoCode`: if `RobustNoCode_TM` fails, such counterexample families exist (at
  sizes `n_i ≥ i`, co-entropy `C n_i w_i`), so their limits satisfy all of the above.
  (Counterexamples to the weaker infinitely-often form give codes at all large sizes, hence such
  families too; `theoremMStar_diagram_profile` covers every co-entropy `o(L)`.)
-/

namespace Transpose.Tape.Impl

open Transpose MeasureTheory Filter Topology TSDiagram

open scoped ENNReal

/-- **Theorem M\* for code-carrying diagrams at the profile capacities**, with the labelling-free
consequences (`excess_of_star`). -/
theorem theoremMStar_diagram_profile {k G : ℕ} (hG : 1 ≤ G) {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ds : ℕ → TSDiagram k}
    {Fs : ∀ i, Set (Fin (ns i * ns i * entryBits (ns i)) → Bool)} {codes : ℕ → NetCode}
    {ms : ℕ → ℕ}
    (hvalid : ∀ᶠ i in atTop, (Ds i).Valid (ns i * ns i * entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, ((Ds i).T : ℝ) ≤ c * inputLength (ns i))
    (hco : ∀ᶠ i in atTop, 2 ^ (ns i * ns i * entryBits (ns i)) ≤ 2 ^ ms i * (Fs i).ncard)
    (hsol : ∀ᶠ i in atTop, (Ds i).Solves (ns i) G ((Ds i).profileCap (ns i) G) (Fs i) (codes i))
    (hmL : Tendsto (fun i => (ms i : ℝ) / inputLength (ns i)) atTop (𝓝 0)) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
      TendstoUniformlyOn (fun i => (Ds (φ i)).rescaled (ns (φ i)) G t) (P t) atTop
        (Set.Icc 0 (c * G + 1))) ∧
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin k → ℝ → ℝ,
      (∀ t, TendstoUniformlyOn (fun i => (Ds (φ i)).rescaled (ns (φ i)) G t) (P t) atTop
        (Set.Icc 0 (c * G + 1))) →
      (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (c * G + 1))) ∧
      (∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S → PiecewiseConstOn β S (c * G + 1) →
        (∀ ℓ, volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
        1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (c * G + 1) p) + 2 * θ +
          2 * k * volume (S ∩ Set.Icc 0 (c * G + 1))) ∧
      1 ≤ ∑ t, ∫⁻ p, levelExcess (P t) (c * G + 1) p ∧
      1 + ∑ t, volume (P t '' Set.Icc 0 (c * G + 1)) ≤ k * ENNReal.ofReal (c * G + 1) ∧
      ¬ ∀ t, MonotoneOn (P t) (Set.Icc 0 (c * G + 1)) ∨ AntitoneOn (P t) (Set.Icc 0 (c * G + 1)) := by
  obtain ⟨hsub, hlim⟩ := theoremMStar_diagram hG hns (ss := fun _ => 0) hvalid htime hco hsol
    (by simpa using hmL)
  exact ⟨hsub, fun φ hφ P hP => ⟨(hlim φ hφ P hP).1, (hlim φ hφ P hP).2,
    excess_of_star (hlim φ hφ P hP).1 (hlim φ hφ P hP).2⟩⟩

/-- **Every family of counterexamples to the Tape Coding Conjecture satisfies (★).** Fix `k`,
`G ≥ 1`, `c`, `C` and sizes `n_i → ∞`, and at every large `n_i` a counterexample to
`RobustNoCode_TM` at these constants: a valid `k`-walk diagram of length `≤ c L_i` whose block
network carries a causal code solving complete exchange at the profile capacities on a set of
co-entropy `≤ C n_i w_i`. Then the rescaled walks have a uniformly convergent subsequence on
`[0, c₀]`, `c₀ = c G + 1`, and every subsequential limit is 1-Lipschitz, satisfies (★), has total
excess level multiplicity `≥ 1` and total range `≤ k c₀ − 1`, and is not monotone on every
tape. -/
theorem mstar_of_robustNoCode_counterexamples {k G c C : ℕ} (hG : 1 ≤ G) {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ds : ℕ → TSDiagram k}
    {Fs : ∀ i, Set (Fin (ns i * ns i * entryBits (ns i)) → Bool)} {codes : ℕ → NetCode}
    (hcex : ∀ᶠ i in atTop, (Ds i).Valid (ns i * ns i * entryBits (ns i)) ∧
      (Ds i).T ≤ c * (ns i * ns i * entryBits (ns i)) ∧
      2 ^ (ns i * ns i * entryBits (ns i)) ≤ 2 ^ (C * ns i * entryBits (ns i)) * (Fs i).ncard ∧
      (Ds i).Solves (ns i) G ((Ds i).profileCap (ns i) G) (Fs i) (codes i)) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
      TendstoUniformlyOn (fun i => (Ds (φ i)).rescaled (ns (φ i)) G t) (P t) atTop
        (Set.Icc 0 ((c : ℝ) * G + 1))) ∧
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin k → ℝ → ℝ,
      (∀ t, TendstoUniformlyOn (fun i => (Ds (φ i)).rescaled (ns (φ i)) G t) (P t) atTop
        (Set.Icc 0 ((c : ℝ) * G + 1))) →
      (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 ((c : ℝ) * G + 1))) ∧
      (∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S →
        PiecewiseConstOn β S ((c : ℝ) * G + 1) →
        (∀ ℓ, volume {u | u ∈ Set.Icc 0 ((c : ℝ) * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
        1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β ((c : ℝ) * G + 1) p) + 2 * θ +
          2 * k * volume (S ∩ Set.Icc 0 ((c : ℝ) * G + 1))) ∧
      1 ≤ ∑ t, ∫⁻ p, levelExcess (P t) ((c : ℝ) * G + 1) p ∧
      1 + ∑ t, volume (P t '' Set.Icc 0 ((c : ℝ) * G + 1)) ≤
        k * ENNReal.ofReal ((c : ℝ) * G + 1) ∧
      ¬ ∀ t, MonotoneOn (P t) (Set.Icc 0 ((c : ℝ) * G + 1)) ∨
        AntitoneOn (P t) (Set.Icc 0 ((c : ℝ) * G + 1)) := by
  exact theoremMStar_diagram_profile hG hns (ms := fun i => C * ns i * entryBits (ns i))
    (hcex.mono fun i h => h.1)
    (hcex.mono fun i h => by
      have h2 := h.2.1
      rw [inputLength]
      exact_mod_cast h2)
    (hcex.mono fun i h => h.2.2.1) (hcex.mono fun i h => h.2.2.2)
    (div_inputLength_tendsto hns (Eventually.of_forall fun _ => le_rfl))

/-- **Counterexamples to the Tape Coding Conjecture, and their limits.** If `RobustNoCode_TM`
fails, there are `k`, `G ≥ 1`, `c`, `C` and, at sizes `n_i ≥ i`, counterexamples at these
constants: valid `k`-walk diagrams of length `≤ c L_i` whose block networks carry causal codes
solving complete exchange at the profile capacities on sets of co-entropy `≤ C n_i w_i`. Their
rescaled walks have a uniformly convergent subsequence on `[0, c₀]`, `c₀ = c G + 1`, and every
subsequential limit is 1-Lipschitz, satisfies (★), has total excess level multiplicity `≥ 1` and
total range `≤ k c₀ − 1`, and is not monotone on every tape. (Every family of counterexamples has
these limits: `mstar_of_robustNoCode_counterexamples`.) -/
theorem mstar_of_not_robustNoCode (h : ¬ RobustNoCode_TM) :
    ∃ (k G c C : ℕ) (ns : ℕ → ℕ) (Ds : ℕ → TSDiagram k)
      (Fs : ∀ i, Set (Fin (ns i * ns i * entryBits (ns i)) → Bool)) (codes : ℕ → NetCode),
      1 ≤ G ∧ (∀ i, i ≤ ns i) ∧
      (∀ i, (Ds i).Valid (ns i * ns i * entryBits (ns i)) ∧
        (Ds i).T ≤ c * (ns i * ns i * entryBits (ns i)) ∧
        2 ^ (ns i * ns i * entryBits (ns i)) ≤ 2 ^ (C * ns i * entryBits (ns i)) * (Fs i).ncard ∧
        (Ds i).Solves (ns i) G ((Ds i).profileCap (ns i) G) (Fs i) (codes i)) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
        TendstoUniformlyOn (fun i => (Ds (φ i)).rescaled (ns (φ i)) G t) (P t) atTop
          (Set.Icc 0 ((c : ℝ) * G + 1))) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin k → ℝ → ℝ,
        (∀ t, TendstoUniformlyOn (fun i => (Ds (φ i)).rescaled (ns (φ i)) G t) (P t) atTop
          (Set.Icc 0 ((c : ℝ) * G + 1))) →
        (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 ((c : ℝ) * G + 1))) ∧
        (∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S →
          PiecewiseConstOn β S ((c : ℝ) * G + 1) →
          (∀ ℓ, volume {u | u ∈ Set.Icc 0 ((c : ℝ) * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
          1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β ((c : ℝ) * G + 1) p) + 2 * θ +
            2 * k * volume (S ∩ Set.Icc 0 ((c : ℝ) * G + 1))) ∧
        1 ≤ ∑ t, ∫⁻ p, levelExcess (P t) ((c : ℝ) * G + 1) p ∧
        1 + ∑ t, volume (P t '' Set.Icc 0 ((c : ℝ) * G + 1)) ≤
          k * ENNReal.ofReal ((c : ℝ) * G + 1) ∧
        ¬ ∀ t, MonotoneOn (P t) (Set.Icc 0 ((c : ℝ) * G + 1)) ∨
          AntitoneOn (P t) (Set.Icc 0 ((c : ℝ) * G + 1)) := by
  unfold RobustNoCode_TM at h
  push Not at h
  obtain ⟨k, G, c, C, hG, hall⟩ := h
  choose ns hns Ds hv hT Fs hco codes hsol using hall
  have hnsT : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  exact ⟨k, G, c, C, ns, Ds, Fs, codes, hG, hns, fun i => ⟨hv i, hT i, hco i, hsol i⟩,
    mstar_of_robustNoCode_counterexamples hG hnsT
      (Eventually.of_forall fun i => ⟨hv i, hT i, hco i, hsol i⟩)⟩

end Transpose.Tape.Impl

import Transpose.Tape.MStarClass

/-!
# Theorem M*, level form for interval labellings (oblivious machines)

An oblivious machine correct on all inputs is the case of `theoremMStar_level_class` with a single
trace class: all matrix inputs (co-entropy `0`, `traceClass_of_obliviousOn`), represented by the
all-zero input `zeroInput`. So Theorem M\* for oblivious machines is a corollary of Theorem M\* for
code-carrying diagrams (`MStarDiagram.lean`), hence of Theorem M\* for walks (`theoremMStar_walk`).

* `theoremMStar_level` (every `θ : ℝ≥0∞`) and `theoremMStar_level_sub` (from the TM-free
  arithmetic `level_sub_of_add`);
* compactness (Arzelà–Ascoli): `exists_subseq_tendstoUniformlyOn` (the case of the reference
  input `zeroInput` of `exists_subseq_blockTraj`) and `theoremMStar_level_subseq` (every sequence
  has a subsequential limit, and it satisfies Theorem M\* in level form);
* the labelling-free form `theoremMStar_excess` (`excess_of_star`), and its corollary
  `no_stationary_limits`: the work-head trajectories cannot all converge to `0`.
-/

namespace Transpose.Tape.Impl

open Transpose MeasureTheory Filter Topology

open scoped ENNReal

/-- **Theorem M\*, level form (additive, any `θ`).** -/
theorem theoremMStar_level {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts : ℕ → ℕ}
    (hobl : ∀ᶠ i in atTop, ObliviousOn M (matrixInputs (ns i) (entryBits (ns i))) (Ts i))
    (hcorr : ∀ᶠ i in atTop, Transposes M (ns i) (entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i))
    {P : Fin M.k → ℝ → ℝ}
    (hconv : ∀ t, TendstoUniformlyOn (fun i => rescaledTraj M (ns i) t) (P t) atTop
      (Set.Icc 0 (horizon M c)))
    {θ : ℝ≥0∞} {S : Set ℝ} (hS : FinUnionIcc S) {β : ℝ → ℕ}
    (hβ : PiecewiseConstOn β S (horizon M c))
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 (horizon M c) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) :
    1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (horizon M c) p) + 2 * θ +
      2 * M.k * volume (S ∩ Set.Icc 0 (horizon M c)) := by
  have hF : ∀ᶠ i in atTop, TraceClass M (ns i) (entryBits (ns i)) (slotLen M (ns i)) (Ts i)
      (matrixInputs (ns i) (entryBits (ns i))) (zeroInput (ns i)) :=
    hobl.mono fun i h => traceClass_of_obliviousOn subset_rfl h (zeroInput_mem _)
  exact theoremMStar_level_class hns (Ds := fun _ => 0) hF
    (Eventually.of_forall fun i => by rw [ncard_matrixInputs, pow_zero, one_mul]; exact le_rfl)
    (by simp)
    (by
      filter_upwards [hF, hcorr] with i hFi hci
      exact classCorrect_of_transposes hci hFi)
    htime hconv hS hβ hclass

/-- The arithmetic of the subtractive form: `1 ≤ X + 2θ + 2kV` gives `ofReal (1 − 2θ − 2kV) ≤ X`
(`V < ⊤`). -/
theorem level_sub_of_add {X V : ℝ≥0∞} {θ : ℝ} {k : ℕ} (hθ : 0 ≤ θ) (hV : V ≠ ⊤)
    (h : 1 ≤ X + 2 * ENNReal.ofReal θ + 2 * k * V) :
    ENNReal.ofReal (1 - 2 * θ - 2 * k * V.toReal) ≤ X := by
  rw [sub_sub, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, tsub_le_iff_right,
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hV, ENNReal.ofReal_ofNat,
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast, ← add_assoc]
  exact h

/-- **Theorem M\*, level form, subtractive notation.** -/
theorem theoremMStar_level_sub {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts : ℕ → ℕ}
    (hobl : ∀ᶠ i in atTop, ObliviousOn M (matrixInputs (ns i) (entryBits (ns i))) (Ts i))
    (hcorr : ∀ᶠ i in atTop, Transposes M (ns i) (entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i))
    {P : Fin M.k → ℝ → ℝ}
    (hconv : ∀ t, TendstoUniformlyOn (fun i => rescaledTraj M (ns i) t) (P t) atTop
      (Set.Icc 0 (horizon M c)))
    {θ : ℝ} (hθ : 0 ≤ θ) {S : Set ℝ} (hS : FinUnionIcc S) {β : ℝ → ℕ}
    (hβ : PiecewiseConstOn β S (horizon M c))
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 (horizon M c) ∧ u ∉ S ∧ β u = ℓ} ≤
      ENNReal.ofReal θ) :
    ENNReal.ofReal (1 - 2 * θ - 2 * M.k * (volume (S ∩ Set.Icc 0 (horizon M c))).toReal) ≤
      ∑ t, ∫⁻ p, levelCross (P t) S β (horizon M c) p :=
  level_sub_of_add hθ (ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    (measure_mono Set.inter_subset_right))
    (theoremMStar_level hns hobl hcorr htime hconv hS hβ hclass)

/-! ### Compactness: convergent subsequences -/

theorem exists_subseq_tendstoUniformlyOn (M : TM) (c : ℝ) {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin M.k → ℝ → ℝ, ∀ t,
      TendstoUniformlyOn (fun i => rescaledTraj M (ns (φ i)) t) (P t) atTop
        (Set.Icc 0 (horizon M c)) :=
  exists_subseq_blockTraj (horizon M c) hns (rs := fun i => slotLen M (ns i))
    (hs := fun i t τ => workTraj M (zeroInput (ns i)) τ t)
    ((hns.eventually_ge_atTop 1).mono fun _i hi =>
      ⟨one_le_slotLen M hi, fun t => ⟨unitSteps_workTraj M _ t, workTraj_zero M _ t⟩⟩)

/-- **Every machine has a subsequential limit, and it satisfies Theorem M\*.** -/
theorem theoremMStar_level_subseq {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts : ℕ → ℕ}
    (hobl : ∀ᶠ i in atTop, ObliviousOn M (matrixInputs (ns i) (entryBits (ns i))) (Ts i))
    (hcorr : ∀ᶠ i in atTop, Transposes M (ns i) (entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin M.k → ℝ → ℝ,
      (∀ t, TendstoUniformlyOn (fun i => rescaledTraj M (ns (φ i)) t) (P t) atTop
        (Set.Icc 0 (horizon M c))) ∧
      (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (horizon M c))) ∧
      ∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S → PiecewiseConstOn β S (horizon M c) →
        (∀ ℓ, volume {u | u ∈ Set.Icc 0 (horizon M c) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
        1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (horizon M c) p) + 2 * θ +
          2 * M.k * volume (S ∩ Set.Icc 0 (horizon M c)) := by
  obtain ⟨φ, hφ, P, hP⟩ := exists_subseq_tendstoUniformlyOn M c hns
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hnsφ : Tendsto (fun i => ns (φ i)) atTop atTop := hns.comp hφt
  refine ⟨φ, hφ, P, hP, fun t => rescaledTraj_limit_lipschitz hnsφ (hP t), ?_⟩
  intro θ S β hS hβ hclass
  exact theoremMStar_level hnsφ (hφt.eventually hobl) (hφt.eventually hcorr)
    (hφt.eventually htime) hP hS hβ hclass

/-! ### The labelling-free form -/

/-- **Labelling-free M\* for oblivious machines** (`excess_of_star`). -/
theorem theoremMStar_excess {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts : ℕ → ℕ}
    (hobl : ∀ᶠ i in atTop, ObliviousOn M (matrixInputs (ns i) (entryBits (ns i))) (Ts i))
    (hcorr : ∀ᶠ i in atTop, Transposes M (ns i) (entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i))
    {P : Fin M.k → ℝ → ℝ}
    (hconv : ∀ t, TendstoUniformlyOn (fun i => rescaledTraj M (ns i) t) (P t) atTop
      (Set.Icc 0 (horizon M c))) :
    1 ≤ ∑ t, ∫⁻ p, levelExcess (P t) (horizon M c) p ∧
      1 + ∑ t, volume (P t '' Set.Icc 0 (horizon M c)) ≤ M.k * ENNReal.ofReal (horizon M c) ∧
      ¬ ∀ t, MonotoneOn (P t) (Set.Icc 0 (horizon M c)) ∨
        AntitoneOn (P t) (Set.Icc 0 (horizon M c)) :=
  excess_of_star (fun t => rescaledTraj_limit_lipschitz hns (hconv t))
    fun _ _ _ hS hβ hcl => theoremMStar_level hns hobl hcorr htime hconv hS hβ hcl

/-- **No stationary limits**: an oblivious linear-time transposer cannot have all rescaled work-head
trajectories converging uniformly to `0` (the path `0` is monotone; `theoremMStar_excess`). -/
theorem no_stationary_limits {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts : ℕ → ℕ}
    (hobl : ∀ᶠ i in atTop, ObliviousOn M (matrixInputs (ns i) (entryBits (ns i))) (Ts i))
    (hcorr : ∀ᶠ i in atTop, Transposes M (ns i) (entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i)) :
    ¬ ∀ t, TendstoUniformlyOn (fun i => rescaledTraj M (ns i) t) (fun _ => 0) atTop
      (Set.Icc 0 (horizon M c)) := fun hconv =>
  (theoremMStar_excess hns hobl hcorr htime hconv).2.2 fun _ => Or.inl monotoneOn_const

end Transpose.Tape.Impl

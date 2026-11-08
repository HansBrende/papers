# Oblivious Linear-Time Tape Transposers Need Macroscopic Crossings

Hans Brende, Claude Opus 5.5 (Anthropic) and Gemini 4 Argon (Google DeepMind), November 2026.

- [`paper/`](paper/): the paper ([`main.pdf`](paper/main.pdf)) and its LaTeX sources. License: CC BY 4.0
  ([`paper/LICENSE`](paper/LICENSE)).
- [`lean/`](lean/): the Lean 4 formalization (`NativeRelations`, Lean and Mathlib v4.34.1). License: Apache 2.0
  ([`lean/LICENSE`](lean/LICENSE)). It requires the libraries of the fourteenth and fifteenth papers by relative path, and through
  them the earlier libraries of the series and [`lean-machine/`](../lean-machine/), so the sibling directories of this repository
  must be in place. [`lean/README.md`](lean/README.md) is a guide to its modules.
- [`tools/lean_index.py`](tools/lean_index.py) generates the index of Lean declarations and `lean/PaperAxioms.lean` from the paper's
  LaTeX sources; [`tools/print_constants.py`](tools/print_constants.py) prints the explicit constants of Sections 4, 5.1 and 6.3.

## The question

Can a multitape Turing machine transpose a d×d matrix of b(d) = max(1, ⌈log₂ d⌉)-bit entries, written row by row, in time linear in its
length L = d²b(d)? This is statement (T) of the [first paper](../Matrix-Transposition-and-the-Tape-Coding-Conjecture/). For oblivious
machines the series has reduced (T) to a coding question on the machine's own time–space network: the
[fourteenth paper](../Bounded-Stack-DAGs-Reduce-to-Constant-Depth/) showed that the crux alone would exclude oblivious linear-time
transposers. This paper asks which schedules make the crux provable, and shows that it holds for every schedule in which a small enough set
of steps separates a large set of outputs from the macroscopic crossings of the tapes.

## What is proved

Proved in Lean, with no axioms beyond `propext`, `Classical.choice` and `Quot.sound` (the paper states each result with its Lean
declarations and file; declarations below are in the namespace `NativeRelations`):

- **Theorem X (macroscopic crossings; `TightConstants.lean`):** `obliviousLinTime_macroscopicCrossingLowers_menger_lb_tight` and
  `obliviousLinTime_crossingLowerGT2H_menger_lb_tight` (with `obliviousLinTime_macroscopicCrossingLowers_card_and_menger_tight` for
  Corollary 5.6, and `obliviousLinTime_macroscopicCrossingLowers_menger_lb_genie` in `MacroscopicThreshold.lean` for the first,
  genie-based form). For every oblivious machine that transposes in time C(L + 1) and every set V₀ of at least αL input positions, every
  set of steps separating the output steps of V₀ from the earlier ends of crossing revisits of excursion more than θL has at least c|V₀|
  elements at all large d, with explicit θ, c > 0 (`thetaMacro_tight`, `cE_menger_tight`) polynomial in C, 1/α and the value width and
  singly exponential in the number of work tapes.
- **Theorem D, bridge and time pullback (`TightConstants.lean`, `CrossingBridge.lean`, `MacroscopicThreshold.lean`):**
  `linearTimeTrace_crossingLowerGT2H_cone_menger_dichotomy_tight` (first forms `linearTimeTrace_crossingLowerGT2H_menger_dichotomy` and
  `linearTimeTrace_crossingLowerGT2H_ballSep_dichotomy`), built on the common-refinement time pullback
  `timePullback_commonRefinement_mais_tight` (first form `timePullback_blockCut_mais`) and the single-cell guarded bridge
  `exists_singleCell_guard_coneSystem_isIndependent_crossingLowerGT2H` (first form `bridge_exists_isAcyclicIn_crossingLowerH`): on every
  linear-time trace, either macroscopic crossings are reached with linear expansion, or a cheap separator plus an O(H)-step guard leaves a
  linear-size independent set in the cone relation, which no transposer can afford (`obliviousLinTime_coneSystem_isAcyclicIn_card_le`).
- **Theorem S (skeletons and single-leg localization; `MacroscopicSkeleton.lean`, `TightConstants.lean`):**
  `obliviousLinTime_reduces_to_crossingCapableSkeleton_and_singleLeg_tight`,
  `obliviousLinTime_crossingCapableSkeleton_and_singleLeg_of_le_one_tight` and `obliviousLinTime_infinite_pinned_skeleton_and_leg_tight`.
  At scale ⌊θL/4⌋ the run's coarse skeleton lies in an explicit finite family independent of d, some tape's word is crossing-capable, and
  the expansion of Theorem X is carried by a single coarsely monotone leg of a single tape.
- **Theorem H (two long-range heads; `OneFreeHeadSmallExcursion.lean`):** `oneFreeHead_smallExcursion_excludes`,
  `twoMacroscopicHeads_of_linearTimeTransposer`, `twoMacroscopicHeads_of_oblivious_linearTimeTransposer`,
  `offCarrier_vertexExpansion_of_linearTimeTransposer` and `offCarrier_vertexExpansion_of_obliviousLinTime` (with Corollary 4.2 in the
  same file). Every oblivious or low-adaptivity linear-time transposer has at least two work heads that make revisits of linear excursion,
  with polynomial constants.
- **Theorem E (adaptive heavy traces and simulators; `SimulatorBridge.lean`, `TightConstants.lean`):**
  `frozenTrace_macroscopicCrossingLowers_menger_lb_tight`, `frozenTrace_reduces_to_crossingCapableSkeleton_and_singleLeg_tight` and
  `simulator_heavyTrace_expansion_and_skeleton_tight` (alongside `adaptive_simulator_heavyTrace_macroscopicExpansion_tight` and
  `simulator_heavyTrace_reduces_to_crossingCapableSkeleton_and_singleLeg_tight`). The conclusions of Theorems X and S hold on every
  η-heavy trace (η ≤ (α/8)ρ₀) of an arbitrary linear-time transposer, and simultaneously on every 2η*-heavy trace of the fifteenth
  paper's bit simulator of any linear-time transposer.
- **Lemma R and the colouring criterion (`TranspositionCut.lean`):** `frozenTrace_bichromatic_tposOf_cut_ge`,
  `oblivious_bichromatic_tposOf_cut_ge` and `frozenTrace_bichromaticColoring_wave_cut_ge`. Every cut between the reads of input rows A₀
  and the outputs they feed into output rows A₁ carries at least (|A₀||A₁|b − ηL)/(w_val + 1) steps.
- **Class exclusions:** bounded macroscopic phases (`boundedMacroBank_has_crux`, `boundedMacroBank_excludes` in `MacroBankCrux.lean`;
  suffix forms `suffixMacroBank_has_crux`, `suffixMacroBank_excludes` in `SuffixMassCrux.lean`); adaptive jittered phases
  (`native_machine_preserves_jitterBM`, `nativeGapBound_of_adaptiveJitterBM`, `adaptiveJitterBM_excludes_transposesAt`,
  `adaptiveJitterBM_not_linearTimeTransposer`, `adaptiveSuffixJitterBM_excludes_transposesAt`,
  `adaptiveSuffixJitterBM_not_linearTimeTransposer` in `JitterMacroBank.lean` and `AdaptiveSuffixJitterBM.lean`); the native gap
  criterion and its low-adaptivity corollary (`nativeGapBound_half_iff`, `native_gap_tests_exclude_linear`,
  `native_gap_exists_exclude_linear`, `fSecond_native_gap`, `native_gap_exclusion_of_trace_support` in `NativeGapCriterion.lean`); and the
  scale-gap pigeonhole for machines without a free work head (`zeroFreeHead_qWindow_excludes`,
  `zeroFreeHead_entries_qWindow_excludes`, `zeroFreeHead_qWindow_oblivious_excludes` in `ZeroFreeHeadQWindow.lean`).
- **Pass counting with coarse passes (`CoarseGroupedPass.lean`):** `theoremP_coarseWorkspace_grouped_on_bits`,
  `theoremPprime_coarseWorkspace_grouped_on_bits`, `oblivious_singleScale_coarseWorkspace_closed_lb` and
  `adaptive_singleScale_coarseWorkspace_closed_lb` (Theorem 10.3), and `subcriticalPhaseProfile_oblivious_excludes`,
  `subcriticalDimPhaseProfile_oblivious_excludes` and `subcriticalPhaseProfile_adaptive_polyTime_excludes` (Corollary 10.4), together with
  the θ = 2 grouped-inequality non-exclusion (`groupedBound_thetaTwo_not_excluded_above_half`,
  `perfectUnshuffleSlopeProduct_tendsto_half`, `unshuffleStep_iter_transpose`).

Proved in the paper but not formalized: Proposition 10.2 (one cut serves every pair of row sets) and Corollary 7.3 (scale-separated
traces). Remark 8.2, the perfect-unshuffle transposer realizing the θ = 2 parameters after Corollary 10.4, and the exclusions of the
individual schedule families of Appendix A are given as proof sketches. Exploratory measurement scripts behind the labelled numerical
remarks (d ≤ 128) are not shipped, and no proof depends on them.

## What is open

The paper ends with four problems: a pass bound that counts phases across all scales; transferring the simulator results back to the
machine's own dependency DAG; constants polynomial in the number of tapes; and the five explicit linear-time cascade schedules that met
every necessary condition proved here in our numerical tests (d ≤ 128).

## Building and verifying

Clone the whole `papers` repository so that the sibling libraries and [`lean-machine/`](../lean-machine/) stay in place, and fetch the
second paper's pinned external dependency as described in its
[README](../Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/). Install
[elan](https://github.com/leanprover/elan), then in `lean/`:

```bash
lake exe cache get
lake build
lake env lean PaperAxioms.lean
```

From this directory, verify the Lean index and `PaperAxioms.lean` against the LaTeX sources and print the numerical constants:

```bash
python3 tools/lean_index.py --check
python3 tools/print_constants.py
```

To build the PDF, run `latexmk -pdf main.tex` in `paper/`.

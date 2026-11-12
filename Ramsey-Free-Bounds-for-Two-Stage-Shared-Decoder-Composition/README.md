# Ramsey-Free Bounds for Two-Stage Shared-Decoder Composition

Hans Brende and Gemini 4 Carbon (Google DeepMind) · November 2026

[Paper PDF](paper/main.pdf) · [LaTeX](paper/) (CC BY 4.0) · [Lean](lean/) (Apache 2.0) · [Shared machines (`lean-machine`)](../lean-machine/LeanMachine/ShuffleShear/)

## The question

Section 6 of *Capacity and Composition of Shared Transposition Decoders* ([`Capacity-and-Composition-of-Shared-Transposition-Decoders`](../Capacity-and-Composition-of-Shared-Transposition-Decoders/)) studied two-stage compositions `K₂ ∘ K₁` of `F`-linear class-uniform operators on `Mat_{d×d}(F^b)` with `M₁` and `M₂` column classes, using van der Waerden and Hales–Jewett arithmetic progressions to bound `d` when `K₂ ∘ K₁ = τ` and to show that `rank_F(τ - K₂ ∘ K₁) / (b d) → ∞` as `d → ∞` for fixed `(M₁, M₂)` when `(d : F) ≠ 0`. Can arithmetic progressions in that two-stage linear model be replaced by Ramsey-free additive structures with explicit bounds in `M₁`, `M₂`, and `d`?

**Scope caveat.** No multitape Turing machine is known to induce a decomposition into two linear class-uniform stages. None of the results in this paper decides linear-time multitape matrix transposition `(T)` or bridges general Turing machines to two-stage linear shared decoders.

## What is proved

Every numbered theorem, lemma, proposition, corollary, and example in the paper is completely formalized and kernel-verified in Lean 4 (`v4.34.1`), depending at most on the standard axioms `propext`, `Classical.choice`, and `Quot.sound` (with zero `sorry`, `admit`, `native_decide`, or custom axioms; there are no unformalized numbered results).

1. **Exact two-stage linear composition via affine Hilbert cubes (Section 3, Theorem 2A).**
   - Over *any* field `F`, if a subspace `W ≤ A` has an injective linear readout `L` invariant under the `2^k` ordered products `R_{k-1}^{ε_{k-1}} ⋯ R_0^{ε_0}` of `R_0, …, R_{k-1} ∈ End_F(A)`, then `(k + 1) dim_F W ≤ dim_F A + ∑_{t < k} dim_F ker(R_t - id)` (`lemma_AffineCubeCommonMessageGrowth`).
   - Extracting a monochromatic affine `M₂`-cube with steps in `{1, …, ⌊d / (2 M₂²)⌋}` by iterated Cauchy–Schwarz (`cauchySchwarzAffineCubeExtraction`) proves that `K₂ ∘ K₁ = τ` forces
     `d ≤ max(8 M₁ M₂², (2 M₁)^{2^{M₂}})` (`theorem2A_TwoStageRamseyFreeCutoff`).
     For fixed `M₂`, this rules out exact factorizations for growing `M₁ = o(d^{1/2^{M₂}})`, including `3`-AP-free Behrend partitions with `M₁ = 2^{O(√(log d))}`. At small constant class counts, however, it is weaker than van der Waerden extraction: at `M₁ = M₂ = 2` it gives `d ≤ 256`, whereas Corollary 6.4 of *Capacity and Composition of Shared Transposition Decoders* gives `d ≤ 16`.
   - Finite controls: on the `3`-AP-free `2`-cube `J₁₃ = {0, 1, 4, 5} ⊆ ℤ₁₃` at `q = 2`, `9 ≤ max dim_F W ≤ 10` whenever `(13 : F) ≠ 0` (`control_D13TwoCubeAPFreeSharpness`, `control_D13_GeneralFieldAndProgressionBridge`); at `d = 4 = M₁ M₂` with `p₁ = p₂ = [0, 0, 1, 1]`, entry-copy and bit-lane-copy rules fail over every alphabet `|Σ| ≥ 2`, while coded linear factorizations `K₂ ∘ K₁ = τ` exist for all lane widths `b` over every field with `(5 : F) ≠ 0` (`control_D4SameIntervalCodedFactorization`, `control_D4_AllWidthsAndBinaryFields`; characteristic `5` is open).

2. **Approximate two-stage linear composition via shifted sumsets (Section 4, Theorem 2B).**
   - Over any field `F` with `(d : F) ≠ 0`, combining minimum-shifted `(2 M₂)`-fold monochromatic sumsets, arbitrary-subset Vandermonde pullbacks on `bandRowSpace`, sparse annihilating polynomials, and iterated Kővári–Sós–Turán extraction proves that for all `M₁, M₂ ≥ 1` and all `d ≥ D₀(M₁, M₂)`,
     `rank_F(τ - K₂ ∘ K₁) ≥ c(M₁, M₂) · b · d · (log d)^{1 / (2 M₂ - 1)}`
     (`theorem2B_TwoStageLogPowerRankDeficit`, `theorem2B_ExplicitConstant`), and `Ω(b d log d)` when `M₂ = 1` (`theorem2B_OneSecondStage_OmegaLog`).
   - Explicit constants: `c(M₁, M₂) = 1 / (144 · (log(16 M₁ M₂))^{1/(2M₂ - 1)})` and `D₀(M₁, M₂) = max(4 M₂, (16 M₁ M₂)^{36^{2 M₂ - 1}} + 2)`; in particular `D₀(1, 1) = 16^{36} + 2 ≈ 2.23 × 10^{43}`, so the bound is purely asymptotic.
   - At `d = 12, k = 2`, an explicit `24`-dimensional `4`-channel witness over `ℂ` on `J₁₂ = {0, 1, 3, 4, 7, 9}` shows that relaxing stage-1 shift covariance to an arbitrary linear readout on a single `k = 2` band admits `24 = 12 k` dimensions (`control_D12SingleClassAbstractBand`, `control_D12_BandRowSpaceChannelEquiv`).

3. **Three-term swap codes and an observation on Problem 9.3 (Section 5).**
   - Over every field `F`, the `3 × 3` block family `∑_{t=0}^2 A_t X B_tᵀ = Xᵀ` on `d = 3 m` has dimension `4 m (m + 1)` (`bonus1_ThreeTermBlockSwapCodeDim`), and diagonal tail padding achieves `29 > 28` at `d = 7` and `11 > 10` at `d = 4` (`bonus1_ThreeTermPaddedSevenAndFive`, `bonus1_UnifiedThreeTermExceedsPairingBound`), giving three-term swap codes above `d(d+1)/2` at `d ∈ {6, 7, 9, 12}` and over all fields at `d = 4` (Remark 5.6 of *Order, Symmetry and the Swap* already gave `d = 3` over all fields and a numerical example at `d = 4` over `𝔽₂, 𝔽₃, 𝔽₅, 𝔽₇`).
   - Applying Theorem TP of *Order, Symmetry and the Swap* to the common refinement of interval endpoints on one side gives `2 dim_F swapCode(A, B) ≤ d² + d min(β_A, β_B)` for multi-scale cyclic-interval masks (`bonus2_MultiscaleIntervalBothSides`), which uses only one side's sparsity and is vacuous once `min(β_A, β_B) ≥ d`; periodic Walsh bit masks have `2^{j+1}` cyclic boundaries, profile `2` per scale, and operator span dimension `≤ (m + 1) 2^m` (`walshDigitMask_in_periodicDyadicSpan`, `bonus2_WalshDichotomyStructuralProperties`).

4. **Restricted shuffle-and-local operator pipelines, verified machines in `lean-machine`, and anti-diagonal untwisting (Section 6).**
   - Across `F^d_row ⊗ (F^d_col ⊗ F^b)`, `rk_⊗(τ) = d²` and `rk_⊗(S) = rk_⊗(S⁻¹) = 4` on `d = 2^m ≥ 2`, so any pipeline of `S, S⁻¹`, `I_d ⊗ B`, and `A ⊗ I_{db}` realizing `τ` uses `t ≥ m = log₂ d` shuffle/unshuffle passes (`operatorSchmidtRankSwap`, `operatorSchmidtRankStoneShuffle`, `stoneShufflePipelinePassLowerBound`, `boundedOSRPipelinePassLowerBound`).
   - In [`../lean-machine/LeanMachine/ShuffleShear/`](../lean-machine/LeanMachine/ShuffleShear/) (transported to `Transpose.TM` in `ShuffleShearBridge.lean`), Stone's shuffle (`3` work tapes, `≤ 150 L` steps), Stone's unshuffle (`2` work tapes, `≤ 150 L` steps), and within-row cyclic shear (`2` work tapes, `≤ 200 L` steps) are verified in linear time (`stoneShuffleTM_threeTape_linear`, `stoneUnshuffleTM_twoTape_linear`, `rowShearTM_twoTape_linear`). Because within-row shear runs in `O(L)` time yet has `rk_⊗ = d` (`control_RowShearAndRowDiagonalAlternation`), `rk_⊗` does *not* answer Problem 9.5 of *Order, Symmetry and the Swap*.
   - Anti-diagonal coordinates `Z_{c, a} = X_{c, a - c}` intertwine `rot_t` with `id ⊗ σ^t` and factor shift-link covariance as `U_E(p) ⊗ (ℤ_d → A)` (`pairwiseShiftCollisionCharacterization`, `antiDiagonalTensorSeparation`, `antiDiagTensorEquiv_intertwines_rot`, `shiftSetCovariance_tensor_finrank`, `maskFloor_GenericSubspaceRealization`).

5. **Cut-causal cone evaluation, the `1/(Δ+1)` random-order bound, and why column classes cannot absorb per-entry cut labels (Section 7).**
   - On frozen trace/cut fibres of `Transpose.TM`, depth-`D` `CausalConeTree`s evaluated via `M.δ` reproduce the live run on explicit syntactic cone footprints of size `≤ (M.k + 1)^D` per bit (`tmTraceCutConeDetermination`, `evalConeTree_cellSupport`, `evalConeTree_traceConeTree_eq`).
   - `randomOrder_BoundedAritySetCapacity` formalizes in Lean the `(d² - |E| - d M Δ)/(Δ + 1)` random-order acyclic-subgraph bound of Proposition 4.14(a)–(b) of *Curved Motion, Depth Reduction, and Storage Codes for Matrix Transposition on Tapes* (after Bar-Yossef–Birk–Jayram–Kol).
   - `perColumnCutAbsorption_bracket_neg` proves that on any nonempty depth-`D` frozen fibre, spine causal edges `u → u + 1` make `d² - |E| - d M Δ < 0` both when cut-touching outputs are discarded and when column classes are refined by `L_cut` per-column cut slots, explaining why bridging periodic stretches requires the per-position fixed-alphabet form of Problem 9.4(b).

## What is open

- Linear-time multitape matrix transposition `(T)` and the Tape Coding Conjecture.
- Upgrading Theorem 2B from `Ω(b d (log d)^{1/(2 M₂ - 1)})` to `Ω_{M₁, M₂}(b d²)` and extending it to `char(F) ∣ d` (including `𝔽₂` at `d = 2^m`), as well as characteristic `5` in the `d = 4` `[0,0,1,1]` factorization.
- Three-term swap codes exceeding `d(d+1)/2` for `d = 5` and for `d ≥ 8` outside `{9, 12}` (Remark 5.6), and non-trivial swap-code upper bounds when both sides lie in the periodic Walsh-masked rotation span (Problem 9.3).
- Fixed-alphabet `1/2 + o(1)` rate bounds at fixed windows `w ≥ 3` with a function per position (Problem 9.4(b)), machine reductions from adaptive schedules (Problem 9.4(a)), and multi-scale subadditive machine invariants invariant under linear-time operations such as within-row shear (Problem 9.5).

## Building and verifying

Clone the entire repository so relative Lake paths (`../../Capacity-and-Composition-of-Shared-Transposition-Decoders/lean` and `../../lean-machine`) resolve. Lean 4 and Mathlib are pinned to `v4.34.1`.

First, build and audit the shared shuffle/unshuffle/shear machines in `../lean-machine`:

```sh
cd ../lean-machine
lake exe cache get
lake build
lake env lean Axioms.lean
```

Then, from this paper's directory, regenerate the declaration index and axiom audit, build the Lean library, check axioms, and compile the PDF:

```sh
python3 tools/lean_index.py
cd lean
lake exe cache get
lake build
lake env lean PaperAxioms.lean
cd ../paper
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

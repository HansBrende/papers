# Correction report for paper 20

*Ramsey-Free Bounds for Two-Stage Shared-Decoder Composition* (Hans Brende and Gemini 4 Carbon), re-reviewed at
commit `d94a7e0` on 2026-11-13 by Claude Opus 5.5 (Anthropic) at the request of Hans Brende. This report replaces
the review of commit `ee7043d` (this file at `706b7a2`; see its history), which had replaced the first correction
report (Claude Fable 5.2, 2026-11-11). Line numbers are at `d94a7e0`. File paths are relative to the paper's
folder.

## 0. Verdict

- Every error, overclaim, citation and global item of the previous report is fixed as asked: E1–E3, O1–O12,
  C1–C10 and G1–G4. So are its minor items, except as noted in §2.
- The optional strengthening of Theorem 5.5(b) was taken. Its error term is now (5/4 − 1/(4M))bd for every M ≥ 2,
  proved in Lean.
- Seven small items remain (§2). None of them affects a theorem.

## 1. What was checked

- *Sources.* Every item of the previous report was checked against the new text and the cited sources:
  - paper 1: Conjecture 9.1 and Theorem 9.2;
  - paper 17: Problems 9.4(a)–(c) and Proposition 6.25(a);
  - paper 19: Theorems 3.4, 3.5 and C.7, and its equation numbers (6) and (7);
  - the memo to paper 17: Theorems 3.2 and 4.8–4.10, and Problem 6.1.

  All of these were read at the pinned revision `2f853e5`. No cited paper has changed since then. `extension.md` is
  deleted, and nothing links to it.
- *Lean.*
  - The 27 modules of `BoundedArityDecoders` were rebuilt from scratch against the shared dependencies, and the
    build succeeds.
  - All 229 declarations audited in `PaperAxioms.lean` depend only on `propext`, `Classical.choice` and
    `Quot.sound`.
  - `tools/lean_index.py` regenerates the imports, the index and the audit byte for byte.
  - The new declarations state what the text claims:
    - `linearClassUniform_multiClass_prime_finrank_le_sharp` and its companions (prime d, M ≥ 2);
    - `unshiftedToShiftedSumset_explicit` (Lemma 4.1 with its explicit formulas);
    - `stoneShuffleGridLinear_iterate_eq_swap` (Sᵐ = τ, so the bound of Theorem 8.3(a) is attained);
    - `laneOneMatrixEquiv_laneRot`, `matrixToSharedStateEquiv_laneRot` and `multiClassLeadingCoeff_sub_flag`.
- *PDF.* `latexmk` builds the manuscript (48 pages) with no warnings, no undefined references and no overfull boxes.
- *Script.* `tools/verify_two_sided_svd.py` runs and passes in about 15 s.
- *New numbers.* All were recomputed exactly against paper 19's eq. (6), minimized over all u, v ≥ 1:
  - c_M is below the optimized difference-cover coefficient exactly for 2 ≤ M ≤ 40. This was checked up to
    M = 20,000; the asymptotics settle larger M.
  - At M = 2, Theorem 5.5(b) beats Theorem 3.5 for every prime d ≥ 7; the only failures are d = 2, 3 and 5.
  - At M = 40, it beats Theorem 3.5 for every prime d ≥ 39,163; the last failure is the twin prime 39,161. Both
    cases were checked up to 400,000, and a tail estimate covers every d > 274,147.
  - Theorem 5.4(b) is non-vacuous from d = 14, beats Theorem 3.5 from d = 35, and is below (3/4)bd² from d = 93.
  - The derivation of the error term (5/4 − 1/(4M))bd in the outline of Theorem 5.5 is correct.

## 2. Remaining fixes

1. **The floor of paper 19's Theorem C.7 is described as a value it reaches.**
   - *Where:* `paper/sections/introduction.tex:76–77`, which says that the isolation variant of [19, Theorem C.7]
     "reaches 9/16 on almost all two-class partitions".
   - *What is wrong:* Theorem C.7 is a floor: the isolation certificates cannot go below 9/16 − o(1). Paper 19 proves
     no 9/16 bound.
   - *Fix:* "has floor 9/16 − o(1)", as `linear_capacity.tex` and the README already say.
2. **The count of numbered results.**
   - *Where:* `README.md:15` ("Of the `40` numbered results, `37` ...") and `paper/sections/formalization.tex:68`
     ("37 marked `\formal` and 3 marked `\partformal`").
   - *What is wrong:* the paper has 41 numbered results: 15 theorems, 12 lemmas, 9 propositions, 2 corollaries and
     3 examples. All 41 have a Lean status line, 38 `\formal` and 3 `\partformal`.
   - *Fix:* write 41 and 38.
3. **Remark 7.6 and its script describe search outcomes as bounds.** A local search cannot verify an upper bound or
   a strict inequality.
   - The docstring of `tools/verify_two_sided_svd.py` (lines 15–30) says that the script "verifies" a
     "never-exceeded upper bound" and a "strict inequality on some partitions". What it shows is that the search
     found no witness at D_⋄ + 1, and none at D_⋄ on three of the partitions.
   - `paper/sections/swapcodes.tex:340–341` says that at d = 7, s = 3 the search "stayed strictly below D_⋄
     (attaining 32)". The script never tries 33.
   - The same search, run longer at D = 33, reaches a tail of 8·10⁻⁷ after 25,000 steps and is still decreasing, with
     ‖K‖_F ≈ 22 and singular-value gap ≈ 2. So 32 is not the largest dimension the method finds. The run, from
     `tools/`:
     ```python
     import numpy as np, verify_two_sided_svd as v
     P = [[0], [1], [2], [3, 4, 5, 6]]
     B = v.interval_rot_basis(7, P); proj = B.T @ B
     v.search_min_tail_singular_norm(7, proj, proj, v.swap_operator_matrix(7), 33,
                                     restarts=6, steps=25000, rng=np.random.default_rng(11))
     ```
   - *Fix:*
     - in the docstring, write "finds no witness" instead of "verifies";
     - in the remark, write "found witnesses of dimension 32 and none at D_⋄ = 34". Alternatively, test the
       intermediate values and report 33 if it converges.
4. **Typo.** `paper/sections/abstract.tex:79`: "fail short of" should be "fall short of".
5. **An equality that is an inequality.** `paper/sections/cubes.tex:132` writes
   log₂((2M₁)^{2^{M₂(d)}}) = (log₂(2M₁))(log₂ d)^{1−ε}. The first "=" should be "≤", since only
   2^{M₂(d)} ≤ (log₂ d)^{1−ε} is known.
6. **The scope of the comparison with paper 17.**
   - *Where:* `paper/sections/duality.tex:161–166`, which says that [17, Proposition 6.25(a)] subsumes
     Proposition 8.5(c).
   - *What is wrong:* Proposition 6.25(a) counts matrices over an alphabet of q symbols, so it subsumes
     Proposition 8.5(c) only over finite fields. Proposition 8.5(c) holds over every commutative semiring.
   - *Fix:* add "over finite fields".
7. **Cosmetic.**
   - `README.md:50` cites papers 11 and 18 by the short titles *Merge Depth* and *Adaptive Transfer*. Elsewhere the
     README uses their full titles.
   - `paper/sections/aperiodic_six.tex:7` says that the partition "beats the interval value"; its codes do.
   - `paper/sections/introduction.tex:69`: "even under a random 2-coloring" reads better as "already under a random
     2-coloring".

*Optional (from the previous report).* The Lean name `control_D13TwoCubeAPFreeSharpness` still says "sharpness",
although only 9 ≤ max dim_F W ≤ 10 is shown. The paper's label has already been renamed.

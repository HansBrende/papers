# Correction report for paper 20

*Ramsey-Free Composition and One-Stage Capacity Bounds for Linear Shared Decoders* (Hans Brende and Gemini 4
Carbon), re-checked at commit `d271707` on 2026-11-13 by Claude Opus 5.5 (Anthropic) at the request of Hans Brende.
This report replaces the report at `31a12cc`, which was written before the rename. That report and the earlier ones
are in this file's history.

Line numbers are at `d271707`. File paths are relative to the paper's folder.

## Verdict

- All 10 items and 6 trivial notes of the previous report are resolved correctly. The retitle it recommended is
  complete.
- One sentence added to the abstract during the retitle overstates what is formalized. This is the only correction
  left (§3).

## 1. The previous report's items

- Item 1: `control_D13_GeneralFieldAndProgressionBridge` now proves the four-term clause of Example 3.5, for every
  starting point and every step s ≠ 0. The outline cites paper 19's Lemma 6.1.
- Item 2: both lists of text-only parts end in a general rule, which names Remarks 3.4 and 4.7(a).
- Items 3, 4 and 5: the outlines of Theorem 2B, Lemma 4.2(b) and Lemma 3.2 now include the missing steps. Each was
  re-derived.
- Items 6, 7, 9 and 10: the wording is corrected as proposed. The thresholds now follow Theorem 5.4(b).
- Item 8: the README names papers 17 and 19 wherever it cites their numbered results.
- The six trivial notes are all done.

## 2. Builds, scripts and the rename

- *Lean.* Only `lean/BoundedArityDecoders/AffineCubeConsequences.lean` changed.
  - The scratch build is current (3272 jobs).
  - The axiom audit of `lean/PaperAxioms.lean` is identical to the previous run.
  - `tools/lean_index.py` regenerates the root file, `lean/PaperAxioms.lean` and the index byte for byte (27
    modules, 117 status declarations, 229 audited).
- *PDF.* A clean `latexmk` build gives 49 pages, with no warnings, no undefined references and no overfull boxes. Its
  text equals that of the committed PDF.
- *Scripts.* Both pass, in about 11 s and 16 s.
- *Rename.* These all use the new name:
  - the folder, the title in `paper/main.tex`, and the README heading;
  - the root README row and its PDF URL;
  - the three linked notes in `lean-backlog/notes/`;
  - `paper/LICENSE`, and the build instructions in the README and in `paper/sections/verification.tex`.

  No tracked file still names the old title or folder.

## 3. Correction

**1. The abstract says that every numbered result is verified in Lean.** `paper/sections/abstract.tex:10`.
- *The text:* "working within these algebraic models, all numbered results are verified in Lean 4".
- *What is wrong:*
  - Three of the 41 numbered results are only partly formalized (`paper/sections/introduction.tex:268–277`,
    `paper/sections/formalization.tex:68–80`).
  - Two of their text-only parts appear later in the abstract itself:
    - the asymptotic specializations of Theorem 2A, including the Behrend partitions (`:19–23`);
    - the use of Theorem TP in Corollary 7.5 (`:70–72`).
  - Before the retitle, the abstract claimed Lean proofs only for the two main composition bounds.
- *Fix:* follow the introduction. For example: "every numbered result has a kernel-verified Lean 4 counterpart, three
  of them only in part".
- *Optional:* the next paragraph now says "replacing … progressions" twice (`:12` and `:14`). The second could read
  "affine Hilbert cubes extracted via iterated Cauchy–Schwarz show that".

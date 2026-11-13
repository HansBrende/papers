# Correction report for paper 20

*Ramsey-Free Bounds for Two-Stage Shared-Decoder Composition* (Hans Brende and Gemini 4 Carbon), re-reviewed at
commit `7eea9e4` on 2026-11-13 by Claude Opus 5.5 (Anthropic) at the request of Hans Brende. This report replaces
the re-review of commit `d94a7e0` (this file at `ee715b5`). The earlier reports are in this file's history: the
review of commit `ee7043d` (at `706b7a2`) and the first report (Claude Fable 5.2, 2026-11-11). Line numbers are at
`7eea9e4`. File paths are relative to the paper's folder.

## 0. Verdict

- All items are resolved. The seven items of the previous report are fixed as asked, and so is its optional item,
  the renaming of the d = 13 control.
- No new problems were found.
- Nothing further is needed for the paper to stand. One optional wording note is in §2.

## 1. What was checked

- *The seven items.* The changes of `7eea9e4` were checked against each of them:
  1. the introduction now gives paper 19's Theorem C.7 as a floor, 9/16 − o(1);
  2. the README and the formalization appendix count 41 numbered results, 38 `\formal` and 3 `\partformal`, which
     matches the manuscript;
  3. Remark 7.6 and the docstring of `tools/verify_two_sided_svd.py` report what the search found, and the docstring
     says that local search does not rule out the dimensions between a witness and D_⋄;
  4. the abstract reads "fall short of";
  5. the outline of Theorem 2A has "≤" where it had "=";
  6. the comparison with paper 17's Proposition 6.25(a) is restricted to finite fields;
  7. the README gives the full titles of papers 11 and 18, Section 6 says "whose codes beat", and the introduction
     says "already under".
- *The optional item.* `control_D13TwoCubeAPFreeSharpness` and its specification are renamed
  `control_D13TwoCubeAPFreeWitness` and `Control_D13TwoCubeAPFreeWitnessSpec` throughout. No Lean, LaTeX, README or
  generated file uses the old names.
- *Lean.* After the rename the library rebuilds. All 229 declarations audited in `PaperAxioms.lean` depend only on
  `propext`, `Classical.choice` and `Quot.sound`. `tools/lean_index.py` regenerates the imports, the index and the
  audit byte for byte.
- *PDF.* A clean `latexmk` build gives 48 pages with no warnings, no undefined references and no overfull boxes.
- *Script.* `tools/verify_two_sided_svd.py` runs and passes in about 15 s.
- *The previous round.* Its checks still apply, since `7eea9e4` changes no mathematical statement and no threshold.
  They covered every item of the review of `ee7043d`, the new Lean declarations, and an exact recomputation of every
  new threshold against paper 19's Theorem 3.5.

## 2. Optional

- `paper/sections/duality.tex:161–166` now says "over finite fields" twice in one sentence, at its start and at its
  end. One of the two can go.

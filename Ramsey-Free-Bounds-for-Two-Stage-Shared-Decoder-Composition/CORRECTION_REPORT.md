# Correction report for paper 20

*Ramsey-Free Bounds for Two-Stage Shared-Decoder Composition* (Hans Brende and Gemini 4 Carbon), re-reviewed at
commit `02eb05f` on 2026-11-13 by Claude Opus 5.5 (Anthropic) at the request of Hans Brende. A second independent
audit of the whole paper followed on the same day, at the same commit (§3). This report replaces the final full review
of commit `7eea9e4` (this file at `95cf7ba`), whose 22 items are now resolved. The earlier reports are in this file's
history. Line numbers are at `02eb05f`. File paths are relative to the paper's folder.

## 0. Verdict

- All 22 items of the final full review are resolved correctly, and so are all items of the earlier reports (§1).
- A second independent audit found 16 more items, plus one optional note (§3).
  - Three new referees each read about a third of the paper and its Lean in full, and the reviewer checked each of
    their findings against the paper, the Lean and the cited sources before listing it.
  - One item is an overclaim (Remark 3.4). The rest are minor: citation details, the wording of one statement and two
    outlines, the lists of text-only parts, the README, and the new crossover script.
  - None affects a theorem or a Lean statement.
- Three items, marked †, come from wording that earlier versions of this report suggested.

## 1. What was checked at `02eb05f` (the 22 items of the previous report)

- *The 22 items.* Each was checked against the new text and the cited sources.
  - N1: the outline of Lemma 6.1 now works with the maximal code of the extended decoders, and step 2 cites its
    maximality.
  - N2: the outline of Lemma 4.2(b) now pulls back id − K₁τK₂ along the band states. Its rank equals
    rank(τ − K₂K₁), because τ² = id and rank(id − AB) = rank(id − BA) on spaces of equal dimension. It concludes
    through K₁X = 0.
  - N3: "for all d" is now "for d ≥ 4M₂ + 1" in all four places.
  - N4–N22: each is corrected as worded in the previous report.
- *The new script.* `tools/verify_linear_capacity_crossovers.py` runs in about 11 s.
  - It minimizes paper 19's eq. (6) exactly over u, v ≥ 1, and its tail estimates are valid.
  - It reproduces the reviewer's independent computations: c_M is below the optimized coefficient of Theorem 3.5
    exactly for 2 ≤ M ≤ 40; the prime crossovers are d ≥ 7 at M = 2 and d ≥ 39,163 at M = 40; and the general-d
    thresholds are 14, 35 and 93.
- *Lean.* No Lean file changed, and `tools/lean_index.py` regenerates the imports, the index and the audit byte for
  byte.
- *PDF.* A clean `latexmk` build gives 49 pages, with no LaTeX or BibTeX warnings, no undefined references and no
  overfull boxes.
- *Script.* `tools/verify_two_sided_svd.py` passes.

## 2. What the second audit checked and found correct

- *Lean against LaTeX.* Every `\formal` and `\partformal` declaration was compared with its statement, and all match.
  None is vacuous.
- *Counts.* They are as stated: 27 modules; 41 numbered results, of which 38 are `\formal` and 3 `\partformal`; 117
  status declarations; 229 audited declarations.
- *Outlines.* Every outline of Sections 2, 3, 5, 6, 7 and 9 was re-derived, with no false step.
- *Recomputations.* Among them:
  - the d = 13 integer certificate;
  - the ℤ₆ determinant;
  - the three-term swap-code dimensions, by exact ranks over several fields;
  - B_cf;
  - the OSR values;
  - S^m = τ;
  - the zero mutual information;
  - dim H_E;
  - the constants of Theorem 2B;
  - every threshold of Section 5, including an independent brute-force check of the script's Theorem 3.5 evaluator
    for d ≤ 129.
- *Sources.* Every claim about papers 1, 4, 11, 17, 18 and 19 and the memo was checked at the pinned revision; all are
  accurate except as listed below.
- *Scripts.* Both scripts pass.

## 3. Items from the second audit

### 3.1 Overclaims and formalization status

**1. Remark 3.4 claims more than it proves.** `paper/sections/cubes.tex:145–146` and `:157–161`.
- *The claim:* Theorem 2A "improves on [19, Theorem 6.3] only when M₁, M₂ ≥ 2 and M₁ is large relative to M₂".
- *Why "only when" is unproved:* for fixed M₁ ≥ 2 and growing M₂, the comparison depends on the unknown growth of
  W(M₁, M₂ + 1).
  - Its known lower bounds are only exponential in M₂ (for example Berlekamp's W(2, p+1) > p·2^p).
  - Theorem 2A's cutoff is doubly exponential in M₂.
- *The parenthetical:* "(and five-fold exponential in M₂ under explicit van der Waerden upper bounds [Gowers])"
  attaches an upper bound to an "is at least" chain. The expression it qualifies, M₂(W(M₁, 3) − 1), is linear in M₂.
- *What is proved:*
  - Theorem 2A never wins at M₁ = 1 or M₂ = 1.
  - It loses at M₁ = M₂ = 2 (256 against 16).
  - For each fixed M₂ ≥ 2 it wins once M₁ is large.
- *Fix:*
  - Say exactly that, and that the case of fixed M₁ ≥ 2 and growing M₂ depends on the growth of W.
  - Move Gowers' bound out of the "at least" chain. It shows only that Theorem 6.3's cutoff is at most five-fold
    exponential in M₂.

**2. The d = 12 control is called general-field.** `paper/sections/formalization.tex:60`.
- *The text:* "the general-field finite controls at d = 13, d = 4, and d = 12".
- *What is wrong:* every d = 12 declaration is over ℂ (`Control_D12SingleClassAbstractBandSpec`, `d12AddChar`,
  `control_D12_UnconditionalExists`, `control_D12_BandRowSpaceChannelEquiv`), as Example 4.9 itself says.
- *Fix:* "the general-field controls at d = 13 and d = 4, and the complex witness and bridge at d = 12".

**3. The lists of text-only parts are incomplete.** `paper/sections/formalization.tex:69–85` and `README.md:15`.
- *What is missing:* the comparisons with paper 19's Theorem 6.6 in Remark 4.7(a) (`paper/sections/sumsets.tex:243–250`;
  also `:12–15` and `README.md:28`):
  - Ω(bd²/M₂) for d ≥ 4M₂ + 1 at M₁ = 1;
  - b(d − 177) from W(2, 5) = 178;
  - the crossover near 10^216.
- *Why they are text-only:* the cited `SharedDecoders.twoHop_rank_interval_any_field` states only
  bk(d − N + 1) ≤ 2r. The choice of k and these consequences appear in no Lean statement. The analogous Section 5
  comparisons are listed.
- *The claims are true.* Taking k = ⌊(d+2)/(2(2M₂+1))⌋ gives r ≥ bd²/(48M₂).
- *Fix:* add them to both lists.

### 3.2 Citations

**4. `MergeDepth.FunDag.cone` is paper 11's Lemma 3.3(b), not Lemma 4.7(a).**
- *Where:* `paper/sections/sweep.tex:20–22` and `README.md:50` list it under "[11, Lemma 4.7(a)]".
- *What paper 11 says:* `FunDag.cone` is the formal counterpart of its Lemma 3.3(b), the cone lemma for function DAGs
  (paper 11, `hopcharging.tex`; also the header of `FieldDag.lean`). Lemma 4.7(a) is the size bound,
  `card_coneV_le`, with its block-machine instance.
- *Fix:* cite Lemma 3.3(b) for `FunDag.cone`, and Lemma 4.7(a) for the size bounds.

**5.† Proposition 8.8 is called a restatement of paper 19.** `paper/sections/duality.tex:208–209`.
- *The text:* "Theorem 8.7(a),(c) and Proposition 8.8 below restate those properties".
- *What is wrong:* the converse construction in Proposition 8.8(a), which realizes
  d² dim A + dim H ≤ 2 dim C₀ + d dim A once the shift coupling is dropped, is this paper's own. It is not among the
  properties of paper 19's Lemma 3.1.
- *Fix:* "Theorem 8.7(a),(c) and the upper bound of Proposition 8.8(a) restate those properties; new here are Ψ, the
  converse construction of 8.8(a) and part (b)".

**6.† Proposition 6.25(a) of paper 17 is said to subsume all of Proposition 8.5(c).**
`paper/sections/duality.tex:164–169`.
- *What is wrong:* paper 17's statement bounds the number of transposed matrices. That gives the conclusion
  2^m ≤ 2^t of Proposition 8.5(c). The output-row source-arity bound ≤ 2^t appears only in the proof of 6.25(a).
- *Fix:* "subsumes the conclusion 2^m ≤ 2^t of Proposition 8.5(c)".

**7. Paper 19's Corollary 6.4 is credited with W(2, 3) = 9.** `paper/sections/cubes.tex:155`.
- *What is wrong:* the corollary uses only W(2, 3) ≤ 9 ("no minimality assertion is needed").
- *Fix:* "uses W(2, 3) ≤ 9".

**8. The headings of the open problems are unattributed.** `paper/sections/sweep.tex:296`.
- *The text:* "Remaining dimensions in Remark 5.6, two-sided multi-scale bounds in Problem 9.3, …".
- *What is wrong:* in this paper Remark 5.6 is its own remark on characteristic dividing d, so a reader lands on the
  wrong remark. The body of the item cites paper 17 correctly.
- *Fix:* "Remark 5.6 and Problem 9.3 of [17]". The heading of item 2, "Problem 9.1(a)–(b)", should name paper 17 too.

### 3.3 Minor

**9. The statement of Proposition 8.8(a) describes an impossible split.** `paper/sections/duality.tex:271–272`.
- *The text:* "splitting a complement of U_{0,s}(p) … into two equal-sized subspaces".
- *What is wrong:* that is impossible when the codimension d − dim U is odd. The construction (outline and Lean) uses
  two independent subspaces of dimension ⌊(d − dim U)/2⌋ inside a complement, which is why the inequality carries the
  extra d·dim A.
- *Fix:* say that.

**10.† The gain over Theorem TP is stated for densities that include 1.** `paper/sections/swapcodes.tex:127–131`.
- *The text:* "when s_A, s_B are proportional to d".
- *What is wrong:* this includes density 1. With S_A = Fin d (so c_A = m_A = 0), B_cf equals the baseline
  (d² + (s_B + c_B)d)/2 exactly.
- *Fix:* "when s_A/d and s_B/d are bounded inside (0, 1)", as Corollary 7.5(a) already assumes.

**11. The Walsh span is given an exact dimension that is not proved.**
- *Where:* `paper/sections/swapcodes.tex:388`, `paper/sections/sweep.tex:304–305` and `README.md:59` say
  "(m+1)2^m-dimensional".
- *What is proved:* Proposition 7.7(c) proves only "at most". Equality holds for m ≥ 1: the functions 1,
  1_{W₀}, …, 1_{W_{m−1}} are linearly independent on each diagonal. At m = 0 the span is {0}.
- *Fix:* "at most (m+1)2^m-dimensional", or state and prove equality for m ≥ 1.

**12. The outline of Lemma 4.5 reverses floor and ceiling.** `paper/sections/sumsets.tex:205–206`.
- *The text:* "lower ⌊m/2⌋ and upper ⌈m/2⌉".
- *What the Lean does* (`single_step_sumset_extract`): it takes the lower ⌈a/2⌉ and the upper ⌊a/2⌋ elements.
- *Fix:* swap them.

**13. The README uses a Lean-only name.** `README.md:38`.
- *The text:* "while Theorem 1A alone gives `≤ 26`".
- *What is wrong:* "Theorem 1A" exists only in Lean names. The paper calls this result Theorem 5.2(b).
- *Fix:* "Theorem 5.2(b)".

**14. The index generator is described inaccurately.** `paper/sections/verification.tex:33–36`.
- *The text:* it says `lean_index.py` regenerates `BoundedArityDecoders.lean` "directly from the \formal, \partformal,
  and \lean commands".
- *What the tool does:* it writes the root file from the list of modules under `lean/BoundedArityDecoders/`. Only
  `PaperAxioms.lean` and the index come from the commands.
- *Fix:* say so.

**15. The crossover script has small slips.** `tools/verify_linear_capacity_crossovers.py`.
- *Coverage of the flag-bound comparisons* (line 145). These say that the optimized Theorem 3.5 bound beats
  1 − 1/(2M) exactly from M ≥ 7, and its square-root form from M ≥ 11. The script asserts them only for M ≤ 29.
  - For M ≥ 41 the first follows from γ*_M < c_M < 1 − 1/(2M), but M = 30–40 is unchecked.
  - The square-root comparison is unchecked from M = 30.
  - The claims are true.
  - *Fix:* extend the loop to M = 40, and add the one-line arguments: γ*_M < c_M < 1 − 1/(2M) for M ≥ 41, and
    2(√(2M) + 1) < M for M ≥ 12.
- *A comment* (lines 209–211). The expansion of ((41/160)d − 1)² − (9/4)d is (1681d² − 70720d + 25600)/25600, not
  …70880…. The polynomial checked is the more conservative one, so the tail bound stands.
- *The docstring* (line 44) says D_tail(M) ≤ 40,200, while the code asserts ≤ 41,000 (line 276). The actual maximum is
  39,322, at M = 40.
- *An assertion* (lines 152–155) is tautological: its second disjunct compares constants, so it never checks that
  (4, 5) is the minimizer at M = 7. The paper does not need that.

**16. A README sentence repeats itself.** `README.md:35`.
- *The text:* "this bound is `< b d²` (and strictly below Theorem 3.4) for `d ≥ 14` (beating Theorem 3.4 for all
  `d ≥ 1`)".
- *Fix:* drop "(and strictly below Theorem 3.4)".

### 3.4 Optional

- The outline of Lemma 4.3 (`paper/sections/sumsets.tex:146–148`) splits into the cases deg P ≤ d and deg P > d.
  The argument is valid, but the Lean proof (`cyclicChannelShift_aeval_ker_finrank_le`) argues uniformly, by
  induction on the leading coefficient. Describe the Lean argument if the outlines are meant to follow it.

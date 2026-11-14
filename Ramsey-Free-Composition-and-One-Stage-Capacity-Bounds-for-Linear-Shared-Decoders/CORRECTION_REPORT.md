# Correction report for paper 20

*Ramsey-Free Bounds for Two-Stage Shared-Decoder Composition* (Hans Brende and Gemini 4 Carbon), re-reviewed at
commit `793c670` on 2026-11-13 by Claude Opus 5.5 (Anthropic) at the request of Hans Brende.
- A third independent review of the whole paper followed on the same day, at the same commit (§2 and §3).
- The title was then assessed (§4).
- This report replaces the report on `02eb05f` (this file at `60cd193`), whose 16 items and optional note are now
  resolved. The earlier reports are in this file's history.

Line numbers are at `793c670`. File paths are relative to the paper's folder.

## 0. Verdict

- All 16 items and the optional note of the previous report are resolved correctly (§1).
- A third independent review found no false theorem and no wrong number. It found 10 items and 6 trivial notes (§3).
  - *How it was done.* Three new referees each read the whole paper through one lens: the statements against the
    Lean, the mathematics, and the claims about other work together with the summaries. The earlier passes split the
    paper by sections instead. The reviewer checked each finding against the paper, the Lean and the sources before
    listing it.
  - *The two items that matter most:*
    - Example 3.5 is marked fully formalized, but one of its clauses has no Lean statement (item 1).
    - The outline of Theorem 2B does not derive the explicit constants in its statement; only the Lean does (item 3).
  - The rest are minor: incomplete lists of text-only parts, two outline steps, README attributions and wording.
- The title no longer describes the paper well. §4 recommends a broader one; the choice is the authors'.

## 1. What was checked at `793c670` (the items of the previous report)

- *The 16 items and the optional note.* Each was checked against the new text and, where it cites one, the source.
  - Item 1: Remark 3.4 now states what is proved.
    - Theorem 2A never wins at M₁ = 1 or M₂ = 1, and it loses at M₁ = M₂ = 2.
    - It wins for each fixed M₂ ≥ 2 once M₁ is large.
    - For fixed M₁ ≥ 2 and growing M₂, the comparison depends on the growth of W(M₁, M₂ + 1).
    - Gowers' bound is now an upper bound on paper 19's cutoff, outside the "at least" chain.
  - Items 2 and 3: the d = 12 control is described as the complex witness and bridge, and both lists of text-only
    parts include Remark 4.7(a)'s comparisons with paper 19's Theorem 6.6.
  - Item 4: `FunDag.cone` is credited to paper 11's Lemma 3.3(b) in Section 9, the introduction and the README.
  - Item 5: "the upper bound of Proposition 8.8(a)" restates paper 19's Lemma 3.1. Its consequence
    |E|D ≤ (|E| − 1)N + bdχ(E) at E = {0, s} is that bound. The converse construction and part (b) are listed as new.
  - Items 6, 7 and 8:
    - paper 17's Proposition 6.25(a) is said to subsume only the conclusion 2^m ≤ 2^t;
    - Corollary 6.4 uses W(2, 3) ≤ 9;
    - the open-problem headings name paper 17.
  - Item 9: Proposition 8.8(a) now chooses two independent subspaces of dimension ⌊(d − dim U)/2⌋ inside a
    complement of U. This gives C₀ ∩ C_s = H and the stated inequality, whether the codimension is odd or even.
  - Items 10–14 are corrected:
    - the density condition;
    - "at most" for the dimension of the Walsh span, in all three places;
    - the outline of Lemma 4.5;
    - "Theorem 5.2(b)" in the README;
    - the description of `lean_index.py`.
  - Item 15: the script now
    - checks the flag comparisons for M ≤ 40 and states the one-line arguments beyond;
    - asserts the quadratic (1681d² − 70720d + 25600)/25600 exactly;
    - asserts the tail cap 39,322 at M = 40;
    - checks the minimizer (4, 5) and γ*₇ = 25/27 at M = 7.
  - Item 16: the redundant README phrase is gone.
  - The optional note: the outline of Lemma 4.3 now argues uniformly in deg P.
    - With (T₁w)_c = w_{c+1}, evaluating P(T₁)w at (n − m) mod d isolates P_m w_{n mod d}.
    - Strong induction on n then shows that restriction to m residues is injective.
    - This is valid and matches the Lean.
- *Lean.* No Lean file has changed since `7eea9e4`.
  - The scratch build is current (3272 jobs).
  - The axiom audit of `lean/PaperAxioms.lean` is identical to the earlier verified run.
  - `tools/lean_index.py` regenerates the root file, `lean/PaperAxioms.lean` and the index byte for byte (27
    modules, 117 status declarations, 229 audited).
- *PDF.* A clean `latexmk` build gives 50 pages, with no LaTeX or BibTeX warnings, no undefined references and no
  overfull boxes. Its text equals that of the committed PDF.
- *Scripts.* Both pass: the crossover script in about 12 s, the SVD script in about 16 s.

## 2. What the third review checked and found correct

- *Statements against the Lean.*
  - All 41 numbered results were compared, clause by clause, with their 117 status declarations and with every
    definition they use.
  - Apart from items 1 and 9 and the first trivial note, hypotheses, quantifiers, constants and directions of
    inequalities agree, and no statement is vacuous.
  - All 118 `\lean` names in the body exist.
  - The counts hold: 27 modules; 41 numbered results, of which 38 are `\formal` and 3 `\partformal`; 117 status
    declarations; 229 audited declarations.
  - The audited declarations use only `propext`, `Classical.choice` and `Quot.sound`.
- *Mathematics.* Every outline of Sections 2–9 was re-derived. Apart from items 3, 4 and 5, every step holds. The
  recomputations include:
  - the d = 13 identity L₁₃T_cE = 13I₉, exactly on J₁₃;
  - the d = 4 factorization, and all 18 band identities at d = 12;
  - D₀(1, 1) = 2^144 + 2, D₀(2, 1) = 2^180 + 2, c(2, 1) = 1/(144 log 32), and the crossover with b(d − 177) near
    5.5 × 10^216;
  - B_run = m² + 3m, with the codes of dimension 2m(m + 1) for m ≤ 5 over ℚ, 𝔽₂, 𝔽₃ and 𝔽₅;
  - c₂ = 19/32, c₃ = 37/54 and c₄ = 191/256;
  - γ*₂ = 17/20, γ*₇ = 25/27, γ*₄₀ = 1301/1342 and γ*₄₁ = 2603/2684, with c_M < γ*_M exactly for 2 ≤ M ≤ 40
    (checked to M = 300);
  - the thresholds d ≥ 14, 35 and 93, and the prime crossovers 7 and 39,163;
  - the mode decoupling of Section 6 (|det|² = 144 in all 24 cases), and the tightness of Lemma 6.1 on both
    25-dimensional codes of the memo;
  - the swap-code dimensions over ℚ, 𝔽₂, 𝔽₃, 𝔽₅ and 𝔽₇, B_cf, and the D_⋄ values;
  - OSR(S) = 4, OSR(τ) = d² and S^m = τ for m ≤ 4;
  - the zero mutual information.
- *Sources.*
  - The numbering of each cited series paper and the memo was rebuilt from its TeX.
  - Every numbered citation of papers 1, 4, 11, 13, 15, 17, 18 and 19 and of the memo exists and says what this
    paper claims, apart from item 8.
  - The Lean names attributed to those papers exist with the stated meaning.
  - The external citations agree with the referees' knowledge.
- *Cross-references and summaries.*
  - Every `\Cref` sub-part exists.
  - Every hard-coded number in the TeX and the tools resolves correctly.
  - The constants in the abstract, the introduction, the README and the root README agree with the body.
  - The open problems ask nothing the paper proves.
- *Scripts.* Both pass, and their assertions establish what the paper says they do.

## 3. Items from the third review

### 3.1 Formalization status

**1. Example 3.5 is marked fully formalized, but one clause has no Lean statement.**
`paper/sections/cubes.tex:190–193`, with the status lines at `:177–178`.
- *The clause:* "on every non-constant 4-term arithmetic progression in ℤ₁₃ the progression bound forces
  4 dim_F W ≤ 26 + 3·2 = 32 (dim_F W ≤ 8 < 9)".
- *What the Lean has:*
  - `control_D13_GeneralFieldAndProgressionBridge` (`lean/BoundedArityDecoders/AffineCubeConsequences.lean:690`)
    proves the progression bound only for two-term progressions (2 dim_F W ≤ 28), for each s ≠ 0.
  - The specification (`lean/BoundedArityDecoders/AffineCubeComposition.lean:102–104`) covers progressions inside
    J₁₃, which have length at most 2.
  - The value 32 appears only in a docstring (`AffineCubeComposition.lean:98`).
  - The kernel dimension 2 for every s ≠ 0 is the private `d13ShiftKer_finrank_eq_two` (`AffineCubeConsequences.lean:658`).
- *Why it matters:*
  - The clause is true: it is paper 19's Lemma 6.1 at four steps, with dim ker(T_s − id) = 2.
  - But by the paper's own convention (`paper/sections/introduction.tex:273–276`), an external-theorem
    specialization proved only in the text makes the result partially formalized.
  - `README.md:22` repeats the clause next to the Lean names.
- *Fix (preferred):* add the four-step clause to `control_D13_GeneralFieldAndProgressionBridge`. Its proof would be
  the two-step proof, using `SharedDecoders.commonMessage_finrank_le` at 4 and `d13ShiftKer_finrank_eq_two`.
- *Fix (alternative):* mark Example 3.5 `\partformal` and update the counts (37 and 4) and both lists.

**2. The lists of text-only parts are still incomplete.** `paper/sections/formalization.tex:70–91` and `README.md:15`.
- *What is still missing.* None of the following appears in a Lean statement.
  - Remark 3.4's comparisons with paper 19's Theorem 6.3 and Corollary 6.4:
    - d ≤ M₁ at M₂ = 1, and d ≤ M₂² at M₁ = 1;
    - 16 against 256 at M₁ = M₂ = 2;
    - the superpolynomial growth in M₁, and the bound from Gowers.

    They are repeated in `paper/sections/abstract.tex:20–22`, `paper/sections/introduction.tex:109–112` and
    `README.md:21`. The Lean has only a docstring note (`AffineCubeConsequences.lean:590–594`).
  - The bound 26 from Theorem 5.2(b) at d = 6, at the start of Section 6 (`paper/sections/aperiodic_six.tex:19–23`;
    also `paper/sections/introduction.tex:81–82` and `README.md:38`).
  - In Section 7.2 (`paper/sections/swapcodes.tex:273–277`):
    - the identity ½(d² + (s+1)d) − B_cf(d; s,1,1; s,1,1) = ¼(s(d − s) − 2s − d);
    - the claim that B_cf can exceed d² for scattered S.
  - Other comparisons in the prose with papers 17 and 19:
    - Section 8.1's claim that paper 17's Proposition 6.25(a) subsumes the conclusion of Proposition 8.5(c)
      (`paper/sections/duality.tex:164–170`);
    - Remark 6.3;
    - Remark 9.4's comparisons with paper 17's Propositions 6.21(b) and 6.22(b).
- *These claims are correct;* all were checked.
- *The previous report's share.* It named only Remark 4.7(a). The parallel Remark 3.4 should have been named with it.
- *Fix:* add Remark 3.4's comparisons. Then replace the itemized "outside theorem environments" clause with a rule,
  for example: "Remarks, and comparisons with other papers in the prose, are proved in the text only unless a Lean
  declaration is named."

### 3.2 Proof outlines

**3. The outline of Theorem 2B does not derive its explicit constants.** `paper/sections/sumsets.tex:237–241`, relying
on Lemma 4.5 (`:192–215`).
- *The text:* "Instantiate the Kővári–Sós–Turán chain of Lemma 4.5 at
  k = ⌊(log d / (18^{2M₂−1} log(16M₁M₂)))^{1/(2M₂−1)}⌋ ≥ 2 for d ≥ D₀(M₁, M₂), and substitute into 4r ≥ bkd".
- *What is missing:*
  - Lemma 4.5 asserts only that some constants c_lo, C_hi and D₀ exist.
  - Its outline says only "density cost exponential in k^{2M₂−1}".
  - So nothing in the text shows that the chain succeeds at this k once d ≥ (16M₁M₂)^{36^{2M₂−1}} + 2.
  - The explicit c(M₁, M₂) and D₀(M₁, M₂) of the statement are derived only in the Lean
    (`theorem2B_ExplicitConstant`, through `iterated_sumset_extract_from_finset` and `sumsetRecFactor`).
- *The missing argument* (checked against the Lean). Write n = 2M₂ − 1 and Λ = log(16M₁M₂), and set R₀ = M₁ and
  R_{t+1} = (16M₂R_t)^{k+2}.
  - Each extraction step succeeds while 16M₂(k + 1)R_n ≤ d. It leaves |A_n| ≥ d/R_n, with every summand in
    [0, ⌊d/(4M₂)⌋].
  - For k ≥ 2, induction gives R_n ≤ (16M₁M₂)^{3^n(k+2)^n} ≤ (16M₁M₂)^{9^n k^n}.
  - Then k^n ≤ log d/(18^n Λ) gives R_n ≤ d^{2^{−n}} ≤ √d. So the chain succeeds for d ≥ D₀, and |A_n| ≥ √d ≥ k.
  - Put y = (log d/(18^n Λ))^{1/n}. The condition y ≥ 2 is d ≥ (16M₁M₂)^{36^n}.
  - With k = ⌊y⌋ ≥ y/2, the bound 4r ≥ bkd gives r ≥ bdy/8 = bd(log d)^{1/n}/(144Λ^{1/n}).
- *Fix:* add this quantitative clause to Lemma 4.5 or to the outline of Theorem 2B.

**4. The outline of Lemma 4.2(b) uses a rank identity without stating it.** `paper/sections/sumsets.tex:111–113`.
- *The text:* "cuts out Q := ker((id − K₁∘τ∘K₂) ∘ E_band) of dimension dim_E Q ≥ bkd − rank_E(τ − K₂∘K₁)".
- *What is missing:* the step needs rank(id − K₁τK₂) = rank(τ − K₂K₁).
  - It holds because dim ker(id − AB) = dim ker(id − BA): x ↦ Bx is a bijection between the kernels. Apply this with
    A = K₁ and B = τK₂.
  - Then id − τK₂K₁ = τ(τ − K₂K₁), since τ² = id.
- *Fix:* add that sentence.
- The previous report accepted this repaired outline. The outline is correct, but this step is not written out.

**5. The outline of Lemma 3.2 skips a threshold check.** `paper/sections/cubes.tex:90–93`.
- *The text:* "maintains |S_t| ≥ d/D_t − Q/2 for 1 ≤ t < k, so d > max(8M_eff k², (2M_eff)^{2^k}) keeps
  |S_{k−1}| > Q".
- *What is missing:* the "so" needs d/D_{k−1} > 3Q/2, that is, d > (3/2)k²(2M_eff)^{2^{k−1}}.
  - This follows from (2M_eff)^{2^k} < d in every case except (M_eff, k) = (1, 2).
  - In that case it needs the term 8M_eff k²: the bound must exceed 24, and (2M_eff)^{2^k} = 16 does not.
- *Fix:* add one sentence.

### 3.3 Wording and citations

**6. A qualifier misdescribes paper 19's certificate floors.** `paper/sections/linear_capacity.tex:60–61`.
- *The text:* "(… Theorem C.7; neither is a capacity lower bound for nonlinear decoders)".
- *What is wrong:*
  - Theorems C.6 and C.7 of paper 19 bound the values that its certificates can reach. They bound no capacity from
    below, for any decoders.
  - Paper 19 says so without a qualifier: "Lower bounds on these numbers are not lower bounds on achievable code
    dimension" (its `paper/sections/appendix-mask-methods.tex:8–9`).
  - "For nonlinear decoders" suggests that the floors might be lower bounds for linear decoders. This paper's own
    19/32 < 5/8 rules that out.
- *Fix:* "neither is a lower bound on capacity, for any decoders".

**7. A parenthetical attaches thresholds to the wrong bound.** `paper/sections/linear_capacity.tex:229–233`.
- *The text:* "strictly below the 41/64 bound of [19, Theorem 3.4] (non-vacuous for d ≥ 14, improving on
  [19, Theorem 3.5] for d ≥ 35, and lying below (3/4)bd² for d ≥ 93)".
- *What is wrong:* the thresholds are those of Theorem 5.4(b). But the parenthetical follows Theorem 3.4, so it reads
  as describing that theorem. Theorem 3.4's own bound is below bd² only from d ≥ 22.
- *Fix:* move the parenthetical so that it follows "leading coefficient 19/32 for two classes".

**8. The README cites papers 17 and 19 by item number without naming them.**
- *Why it misleads:* in this paper, 3.4 is a remark, 3.5 is an example and 5.6 is a remark of its own, and there is
  no Theorem 6.6, C.6 or C.7.
- *Where:*
  - `README.md:15`: "the comparisons against Theorem 6.6 in Section 4 / Remark 4.7(a) … against Theorem 3.5 in
    Section 5".
  - `README.md:35`: "Theorem 3.4's `41/64`", "Theorem C.6", "Theorem C.7", "beating Theorem 3.4", "beats Theorem
    3.5" and "Theorem 3.5's difference-cover bound". Line 28 names paper 19 for its Theorem 6.6; line 35 never names
    it.
  - `README.md:40`, a heading: "(Section 7, Remark 5.6 and Problem 9.3)".
    - These belong to paper 17, but line 15 uses "Remark 5.6" for this paper's own Remark 5.6.
    - The headings at lines 31 and 37 ("Problem 9.1(a)", "Problem 9.1(b)") leave paper 17 unnamed too.
    - This is the README counterpart of the previous report's item 8.
  - `README.md:58`: "(… Problem 9.1(b) and Problem 6.1 of [`memo-class-uniform-codes`])". This reads as the memo's
    Problem 9.1(b). The memo's problems are numbered 6.1–6.3; Problem 9.1(b) is paper 17's.
- *Fix:* name the paper each time, as line 28 does.

**9. Proposition 2.1(b) claims slightly more than its Lean.** `paper/sections/model.tex:75–77`.
- *The text:* "every algebraically closed extension of F, and in particular F̄, contains a primitive n-th root of unity".
- *What the Lean has:*
  - `exists_isPrimitiveRoot_of_isAlgClosed` assumes (n : K) ≠ 0 in the algebraically closed field K.
  - The transfer from (n : F) ≠ 0 is proved only for K = `AlgebraicClosure F`
    (`exists_isPrimitiveRoot_algebraicClosure`, `lean/BoundedArityDecoders/ExtensionFieldTransfer.lean:130–142`).
- *Fix:* either of these:
  - write "every algebraically closed field K with (n : K) ≠ 0, in particular F̄";
  - add the three-line transfer, through the injectivity of `algebraMap`.

**10. Remark 9.4 omits Δ ≥ 1.** `paper/sections/sweep.tex:157–158`.
- *The text:* "with factor Δ^Δ/(Δ+1)^{Δ+1} ∈ (1/(e(Δ+1)), 1/(2(Δ+1))]".
- *What is wrong:* at Δ = 0 the factor is 1. The Lean (`pMin_two_sided_theta_inv_arity`) assumes 1 ≤ Δ.
- *Fix:* add "for Δ ≥ 1".

### 3.4 Trivial notes

- *Proposition 7.3(c)* (`paper/sections/swapcodes.tex:162–164`).
  - "= 2d − 2" and "realize all matrix units" are not in its Lean statement. That statement
    (`lean/BoundedArityDecoders/SwapCodeAnswers.lean:258–264`) gives only 2^m ≤ ∑_j 2^{j+1} and the full swap code.
  - Write "≥ d", and treat the matrix units as part of the proof.
- *Unqualified Lean names* (`README.md:35` and `:47`).
  - The README writes `difference_cover_real_bound`, `square_cover_bound` and `finrank_covarianceSpace`.
  - The declarations are `SharedDecoders.IsSharedCode.difference_cover_real_bound`,
    `SharedDecoders.IsSharedCode.square_cover_bound` and `SharedDecoders.finrank_covarianceSpace`, as the paper
    writes them.
- *A missing hypothesis* (`README.md:52`). The summary of Proposition 9.6 omits the hypothesis of part (b),
  (M.q + 1)(M.g + 1)^{M.k} ≥ 2 (`paper/sections/sweep.tex:252–253`).
- *Bibliography labels* (`paper/references.bib:8`, `:78` and `:88`).
  - These entries describe FirstPaper2026, AdaptiveTransfer2026 and SharedDecoders2026 as "Manuscript and Lean
    formalization".
  - But those papers mark 4, 7 and 1 results, respectively, as not formalized.
  - Four other entries say "partial".
- *Grammar* (`paper/sections/duality.tex:210–211`). "what is new here are packaging" should read "what is new here
  is the packaging of".
- *A constant assertion* (`tools/verify_linear_capacity_crossovers.py:152`).
  - `assert 12 * 12 - 12 * 12 + 4 > 0` evaluates a constant.
  - The comment's argument is right: the larger root of M² − 12M + 4 is 6 + 4√2 ≈ 11.66. So the line can go.

## 4. The title

Hans Brende asked whether the title still fits the paper after its revisions. It no longer describes the paper well,
and a broader title would serve it better. The choice is the authors'.

- *How the title came about.* The paper was retitled on 2026-11-11 (`1c025f3`) around two-stage composition, after
  the first external review recommended that focus. Sections 5 and 6 were added two days later (`079df20`).
- *What it leaves out.*
  - Sections 5 and 6 hold the 19/32 two-class bound, the c_M bound and the exact dimension 25.
  - For linear class-uniform codes, they improve the best bound known for paper 17's Problem 9.1(a) when
    char(F) ∤ d. That bound was 41/64, from paper 19's Theorem 3.4.
  - They also settle Problem 9.1(b) outside characteristics 2 and 3.
  - In the reviewer's judgment, they matter at least as much to the series as Theorems 2A and 2B, whose known gains
    over paper 19 need large class counts or astronomically large d (Remarks 3.4 and 4.7).
  - The title names only Sections 3 and 4, about 10 of the 33 pages of Sections 3–9.
- *What it does not say.* Every result of Sections 3–6 concerns linear decoders, while paper 19's capacity bounds
  hold for arbitrary decoders.
- *Recommendation:* **Ramsey-Free Composition and One-Stage Capacity Bounds for Linear Shared Decoders.**
  - It keeps the composition results first, as the abstract does.
  - It names Sections 5 and 6 in the words of Section 5's own heading.
  - It says "linear".
  - If the authors prefer to echo paper 19's title, "Linear Shared Transposition Decoders" also works.
  - With the new title, the abstract's first paragraph could present both themes, instead of "two main composition
    bounds" followed by "three further sections".
- *What a rename touches.* The folder name follows the title, so a rename changes:
  - the folder, the title in `paper/main.tex`, and the README heading;
  - the root README row;
  - three notes in `lean-backlog/notes/` that link to the folder: `identity-lift-comparison.md`,
    `native-cone-property-audit.md` and `three-term-seed-assemblies.md`;
  - the published PDF URL.

  No other paper cites paper 20, and no Lean package depends on it. The Lean library name `BoundedArityDecoders`
  can stay.

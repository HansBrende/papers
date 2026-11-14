# Correction report for paper 20

*Ramsey-Free Bounds for Two-Stage Shared-Decoder Composition* (Hans Brende and Gemini 4 Carbon), re-reviewed at
commit `7eea9e4` on 2026-11-13 by Claude Opus 5.5 (Anthropic) at the request of Hans Brende. A final full review
of the whole paper followed on the same day, at the same commit (§3). This report replaces the re-review of commit
`d94a7e0` (this file at `ee715b5`). The earlier reports are in this file's history: the review of commit `ee7043d`
(at `706b7a2`) and the first report (Claude Fable 5.2, 2026-11-11). Line numbers are at `7eea9e4`. File paths are
relative to the paper's folder.

## 0. Verdict

- Every item of the earlier reports is resolved (§1).
- A final full review found 22 further items (§3).
  - Three independent referees each read about a third of the paper and its Lean in full, and the reviewer checked
    each of their findings against the paper, the Lean and the cited sources before listing it.
  - None of the items affects a Lean theorem.
  - Four are false steps in outlines or false statements in the text (§3.1). The rest are overclaims (§3.2),
    citations (§3.3) and minor slips (§3.4).
- Nine items, marked †, come from wording that earlier versions of this report suggested. They are the reviewer's
  errors, not Carbon's.

## 1. What was checked at `7eea9e4` (re-review of the previous report's items)

- *The seven items.* The changes of `7eea9e4` were checked against each of them:
  1. the introduction now gives paper 19's Theorem C.7 as a floor, 9/16 − o(1);
  2. the README and the formalization appendix count 41 numbered results, 38 `\formal` and 3 `\partformal`, which
     matches the manuscript;
  3. Remark 7.6 and the docstring of `tools/verify_two_sided_svd.py` report what the search found, and the docstring
     says that local search does not rule out the dimensions between a witness and D_⋄;
  4. the abstract reads "fall short of";
  5. the outline of Theorem 2A has "≤" where it had "=";
  6. the comparison with paper 17's Proposition 6.25(a) is restricted to finite fields (but see §3, item N4);
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

## 2. What the final full review checked and found correct

The full review covered these, and found them correct:
- every numbered statement of Sections 2–9;
- all 117 status declarations: each exists, and its type matches the LaTeX statement, with no vacuous hypotheses;
- the Lean sources: no `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by` or `extern` in
  `BoundedArityDecoders` or in `lean-machine`;
- recomputations, among them:
  - the cube-extraction parameters;
  - the constants c(M₁, M₂) and D₀(M₁, M₂), and the crossover near 10^216.7;
  - Examples 3.5 and 3.6;
  - B_run and the averaging of Section 5;
  - the ℤ₆ determinant;
  - the three-term block and padded codes (exact ranks over several fields for m ≤ 4, s ≤ 3);
  - B_cf;
  - the OSR values (by realignment rank);
  - the zero-mutual-information claim;
  - dim H_E = χ(E)·d·dim A (on 400 random cases);
  - the boundary constructions of Section 9;
- the cited statements of papers 1, 4, 11, 17, 18 and 19 and of the memo, at the pinned revision.

## 3. Further items from the final full review

### 3.1 False steps and false statements

**N1. The outline of Lemma 6.1, step 2, fails as written.** `paper/sections/aperiodic_six.tex:50` and `:64–66`.
- *The outline:* it sets W := 𝒳_K ∩ rot₁⁻¹(𝒳_K) without defining 𝒳_K. It then claims that every Y ∈ W_{S_a} has each
  mode component π_η(Y) in W.
- *Why that fails:* if 𝒳_K is the scalar extension of 𝒳, the claim is false. A subspace of a code is a code of the
  same decoders. So with Y = y₁ + y₂ + y₄ (0 ≠ y_η in mode η of the maximal code) and 𝒳 = span{Y, rot₁Y}, Y lies in
  W_{S₀}, but π₁(Y) ∉ 𝒳, since ζ, ζ² and ζ⁴ are distinct.
- *Why the Lean is fine:* `aperiodicSix_shift_inf_finrank_le_14` first pushes 𝒳 into `codeOfDec decK`, the maximal
  code of the extended decoders. It then bounds `codeOfDec decK ⊓ comap (rot 1)`.
- *Fix:* define 𝒳_K as that maximal code, which contains the image of 𝒳 ∩ rot₁⁻¹(𝒳), and say that step 2 uses its
  maximality.

**N2. The outline of Lemma 4.2(b) has a false inference.** `paper/sections/sumsets.tex:109–112`.
- *The text:* "vanishing of K₁X on columns c ∈ J₀ forces (τX)_{:,c} = (K₂K₁X)_{:,c} = 0 on J₀ and hence X = 0".
- *What is wrong:* τX vanishing on the columns in J₀ only kills the rows J₀ of X. Also, the band constraint is on the
  intermediate state K₁X, not on the input. The inputs lie in a space of dimension up to bM₂kd, not bkd.
- *The argument in Lean* (`stackedBandPullbackData`):
  - K₁X is a band state whose columns are Σ_ν χ(νc)a_ν;
  - vanishing at the k points of J₀ gives a = 0 by part (a);
  - so K₁X = 0, and X = τK₂K₁X = 0.
- *Fix:* rewrite the outline that way.

**N3.† "Ω(bd²/M₂) for all d" at M₁ = 1 is false for small d.**
- *Where:* `paper/sections/introduction.tex:140–141`, `paper/sections/sumsets.tex:13–14` and `:237–238`, and
  `README.md:28`.
- *The source:* paper 19's Theorem 6.6 needs d ≥ N₀ = (2M₂ + 1)k − 1.
- *A counterexample at d = M₂ ≥ 2:* K₁ = id is a one-class rule. K₂ = τ is class-uniform with each column its own
  class. Then r = 0.
- *What holds:* for d ≥ 4M₂ + 1, Theorem 6.6 gives r ≥ bd²/(48M₂). Take k = 1 if d ≤ 8M₂ + 2, and
  k = ⌊(d+1)/(2(2M₂+1))⌋ otherwise.
- *Fix:* write "for all d ≥ 4M₂ + 1" in all four places.

**N4.† The parenthetical "which holds over every commutative semiring" in `paper/sections/duality.tex:161` is false.**
- *What is wrong:*
  - Over the zero semiring every operator equals τ, so the conclusion 2^m ≤ 2^t of Proposition 8.5(c) fails at t = 0.
  - The proposition is stated for fields.
  - The Lean (`Control_RowShearAndRowDiagonalAlternationSpec`, part 2) takes `[Field F]` and uses 0 ≠ 1.
- *Fix:* delete the parenthetical. This also removes the redundancy of the same sentence, which says "over finite
  fields" at both its start (line 161) and its end (line 166).

### 3.2 Overclaims

**N5. Comparison thresholds inside `\formal` theorem statements are neither formalized nor proved.**
- *Where:*
  - Theorem 5.4(b), `paper/sections/linear_capacity.tex:253–256`: "non-vacuous and strictly below [19, Thm 3.4] for
    d ≥ 14, strictly below [19, Thm 3.5] for d ≥ 35, and strictly below (3/4)bd² for d ≥ 93";
  - Theorem 5.5(b), `:301–304`: "< bd² for all primes d ≥ 3, beats [19, Thm 3.5] for all primes d ≥ 7, and is
    < (3/4)bd² for all primes d ≥ 11";
  - `README.md:35`.
- *What is wrong:*
  - No cited declaration states these thresholds. The Lean has only the bounds and the chain 19/32 < 5/8 < 41/64.
  - The comparisons with Theorem 3.5 need a minimization over u, v ≥ 1 and a tail estimate. No outline or script
    gives them.
  - So the lists of text-only parts (`paper/sections/formalization.tex:67–83`, `README.md:15`) are incomplete.
- *The values are correct:* they were recomputed exactly in the previous round.
- *Fix:* move the comparisons out of the theorem statements into the prose, where lines 38–50 already state them.
  Alternatively, mark both theorems `\partformal` and add the comparisons to both lists. In either case, add a script
  for the Theorem 3.5 thresholds.

**N6.† The claim of a win over Theorem TP for two-scale families is too broad.** `paper/sections/swapcodes.tex:126–127`.
- *The claim:* the two-sided bound "improves the leading coefficient over one-sided Theorem TP when s_A, s_B are
  proportional to d and the run and coarse counts are o(d)".
- *A family where it fails:* `HasCoarseFineIntervalDecomposition` allows any fine mask I ⊆ S, including I = S. Take
  S = {0, …, d/2 − 1}, the single fine mask S and one coarse interval, on both sides.
  - Then B_cf = (11/16)d² + d.
  - Theorem TP on the two interval classes {S, ℤ_d ∖ S} gives (d² + 2d)/2.
- *What holds:* the gain is over the Theorem TP bound that the decomposition data alone give, when every fine mask
  may be a singleton: (d² + min(s_A + c_A, s_B + c_B)·d)/2. That is the comparison Corollary 7.5 makes.
- *Fix:* say so.

**N7.† The d = 12 witness shows that the iteration is essential only in the text-only reading.**
- *Where:* `paper/sections/introduction.tex:144–148`, `paper/sections/sumsets.tex:297–300` and `README.md:29`.
- *Under the Lean reading (b, M₂) = (2, 1):* the band has dimension bM₂kd = 48 = bkd. The witness has dimension
  24 = bkd/2. That is consistent with a band-only bound r ≥ bkd/2, which is stronger than Theorem 4.4's r ≥ bkd/4. So
  this reading shows nothing about the iteration.
- *Under the text-only reading (1, 2):* 24 = bkd, so the band alone gives only r ≥ 0. Even this shows only that the
  annihilator steps cannot all be dropped.
- *Fix:* state the conclusion for the (1, 2) reading, and say that it is the text-only part of Example 4.9.

**N8. The README says the two models are identified, which the Lean does not prove.** `README.md:32`.
- *The README:* "Model equivalences (…) identify the `b = 1` model of [17] and the `b`-lane model of [19]".
- *What the Lean proves:* `Extension_LinearModelAndCharBridgesSpec` is an equivalence only at b = 1. For b lanes it
  is one-way, from `IsLinearClassUniformCode` to `IsSharedCode`, and `IsSharedCode` allows nonlinear decoders, as
  `paper/sections/model.tex:26–29` says.
- *Fix:* "identify the two models at b = 1, and embed the b-lane linear model into [19]'s shared-code model".

**N9.† The novelty of the cone size bound is overstated.** `paper/sections/sweep.tex:19–27`.
- *The claim:* "What is new in Lemma 9.1 below are the Lean (M.k+1)^D size bound on `Transpose.TM` cones and the
  rooted (1+M.k)-ary symbolic tree representation".
- *What paper 11 already has, in Lean:*
  - its Lemma 4.7(a), `MergeDepth.card_coneV_le` (`SkeletonCones.lean`), the bound Σ_{h≤D}(k+1)^h for every DAG of
    out-degree ≤ k+1;
  - its instance for the block machine of a `Transpose.TM`, `MergeDepth.blockMachine_card_cone_le`
    (`BlockMachine.lean`).
- *Fix:* cite them. Say that what is new is the instance on the native step DAG of frozen trace/cut fibres (spine
  plus last-visit edges), and the `CausalConeTree` extraction and evaluator.

**N10. Paper 4's necessity result is quoted as a possibility.**
- *Where:* `paper/sections/sweep.tex:216–218` and `README.md:11`, item (iii): "linear-time transposers can use
  curved, head-dependent, non-piecewise-affine motion".
- *What paper 4 proves:* in its Section 3, Theorems 3.10 (Theorem C) and 3.12 (Theorem Cq) and Corollary 3.24 show
  that every linear-time transposer must have such motion.
- *Fix:* "must use", citing those results.

### 3.3 Citations

**N11.† `isSharedCode_iff_compatible` is not part of paper 19's Lemma 3.1.**
- *Where:* `paper/sections/duality.tex:194–202` and `README.md:47`.
- *What paper 19 has:*
  - Its Lemma 3.1 states only the necessity direction (C_E ⊆ H_E), the dimension bdχ(E), the translate bound and
    rotation invariance. Its Lean is in `CapacityAmbient.lean`.
  - The equivalence `SharedDecoders.isSharedCode_iff_compatible` is in `CapacityGluing.lean`, and paper 19's text
    does not state it.
- *Consequence:* the sufficiency half of Theorem 8.7(a) is not a restatement of Lemma 3.1.
- *Fix:* credit Lemma 3.1 with what it states. Cite the converse as a Lean theorem of paper 19's library.

**N12.† The spine-edge mechanism is attributed to paper 17.** `paper/sections/sweep.tex:212–216`.
- *The text:* "As already observed in the commentary on [17, Problem 9.4(b)], because `TMDepStep` includes the
  control-state spine edge …".
- *What paper 17 says:* its commentary observes only that cut patterns divide the outputs into boundedly many classes
  drawn entry by entry. The spine edge and `TMDepStep` are this paper's.
- *Fix:* credit paper 17 with the conclusion, and Proposition 9.6 with the mechanism.

**N13. The text says paper 19 "initiated the study" of two-stage compositions.** `paper/sections/introduction.tex:34–36`.
- *What is wrong:* paper 17's Remark 6.14 already treats compositions K_t⋯K₁ of class-uniform hops, and proves
  dim ker(sw − K_t⋯K₁) ≤ (d² + d + tMd)/2 for hops with M interval classes. Paper 19 itself credits the many-hop gap
  of paper 17, Section 7.4.
- *Fix:* say that paper 19 studied exact and approximate two-stage factorizations for arbitrary partitions, and cite
  paper 17's Remark 6.14.

**N14.† W(2, 5) = 178 has no source.**
- *Where:* `paper/sections/introduction.tex:142`, `paper/sections/sumsets.tex:241` and `README.md:28`.
- *What is wrong:* this is the computation of Stevens and Shantaram (*Math. Comp.* 32 (1978), 635–636). It is not in
  paper 19 or in Lean, yet the bound b(d − 177) rests on it.
- *Fix:* cite it.

**N15.† "Tower-type" misdescribes Gowers' bound.**
- *Where:* `paper/sections/introduction.tex:71`, `paper/sections/cubes.tex:158–159` and
  `paper/sections/sumsets.tex:28`.
- *What is wrong:* Gowers' bound W(r, k) ≤ 2^{2^{r^{2^{2^{k+9}}}}} is a five-fold iterated exponential, not a
  tower.
- *Fix:* "five-fold exponential" (or "iterated exponential").

**N16. The open questions are cited to the wrong section of paper 19.** `paper/sections/introduction.tex:64–66`.
- *The text:* it "addresses three open questions … in two-stage composition ([19, Section 6])".
- *What is wrong:* paper 19's composition open questions are in its Section 8: a sharp class-product inequality, and
  a positive normalized rank deficit. This paper settles neither.
- *Fix:* cite Section 8, and say "makes progress on".

**N17. Theorem C.6 is cited for the 41/64 bound.** `paper/sections/introduction.tex:151–152`.
- *The text:* "In [19, Theorem 3.4 and Theorem C.6], … gave (41/64)bd² + (5/3)bd^{3/2}".
- *What is wrong:* Theorem C.6 is the 5/8 − o(1) floor of the certificate method, not the bound.
- *Fix:* cite Theorem 3.4 alone there.

### 3.4 Minor

**N18. Remark 7.6 classifies the tested partitions inconsistently.**
- *Where:* `paper/sections/swapcodes.tex:336–342`, and the same wording in `tools/verify_two_sided_svd.py:21–28` and
  `:234`.
- *What is wrong:*
  - d = 7, s = 3 has s = ⌊d/2⌋, so the first clause puts it among the partitions where the search reached D_⋄, but
    the second clause and the script say it did not.
  - d = 5, s = 2 has s < d − s, yet it reached D_⋄.
- *Fix:* list the cases.
  - D_⋄ was reached for (d, s) = (5, 2), (6, 3), (7, 4) and (8, 4), for d = 6 with s_A = 3 and s_B = 4, and for the
    d = 6 two-run partition.
  - It was not reached for (7, 3), (8, 3) and the d = 7 partition 1+1+5 against 2+2+3. The witnesses found there have
    dimensions 32, 40 and 27.

**N19. The outline of Proposition 8.4 misdescribes the row-shear machine.** `paper/sections/duality.tex:126–128`.
- *The text:* "copies each db-bit row to tape 0 and emits it cyclically shifted by rb bits".
- *What the Lean machine does* (`lean-machine/LeanMachine/ShuffleShear/RowShear.lean`):
  - tape 0 holds a save/emit template, not the row;
  - for row r the machine buffers only the first rb bits, on tape 1;
  - it streams the other (d − r)b bits from the input to the output;
  - it then emits the buffered bits.
- *Fix:* describe the machine that way.

**N20. The M₁ = 2 comparison names the wrong result and the wrong threshold.** `paper/sections/introduction.tex:142–144`.
- *What is wrong:*
  - The crossover d ≈ 10^216.7 comes from Theorem 2B's explicit c(2, 1) = 1/(144 log 32). Corollary 4.8's constant is
    only existential.
  - The relevant threshold at (M₁, M₂) = (2, 1) is D₀(2, 1) = 32^36 + 2 ≈ 1.53·10^54, not D₀(1, 1). `README.md:28`
    quotes D₀(1, 1) in the same comparison.
- *Fix:* name Theorem 2B, and quote D₀(2, 1).

**N21. The heuristic in the outline of Example 3.5 is wrong.** `paper/sections/cubes.tex:192–193`.
- *The text:* "7 nonzero Fourier modes each satisfy a rank-3 alignment system inside a 4-dimensional mode space
  (2 + 7 = 9)".
- *What is wrong:*
  - ℤ₁₃ has 12 nonzero characters, in 6 conjugate pairs.
  - No nonzero vector of an admissible W lies in a single mode: L(T₁w) = ω^j L(w) = L(w) forces L(w) = 0.
  - The Lean witness projects with rank 2 onto all 13 modes.
- *Fix:* delete the sentence, or replace it with a correct count.

**N22. One half of the asymptotic clause of Theorem 2A is not checked.** `paper/sections/cubes.tex:131–132`.
- *What is missing:* the (1 − ε)·log₂log₂ d clause checks (2M₁)^{2^{M₂(d)}} < d, but not 8M₁M₂(d)² < d.
- *Fix:* add that the second condition holds because M₂(d) = O(log log d).

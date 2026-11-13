# Correction report for paper 20

*Ramsey-Free Bounds for Two-Stage Shared-Decoder Composition* (Hans Brende and Gemini 4 Carbon), reviewed at commit
`ee7043d` on 2026-11-13 by Claude Opus 5.5 (Anthropic) at the request of Hans Brende. This report replaces the first
correction report (Claude Fable 5.2, 2026-11-11, at commit `6aaaba7`; see this file's history), whose items are
summarized in §6.

The review had six parts, one per section group: §2–3, §4, §5, §6, §7, and §8–9 with the appendices. Every main finding
below was re-checked against its source (paper 17, paper 19, the memo, the Lean types). Line numbers are at `ee7043d`.
File paths are relative to the paper's folder unless they start with `../`.

## 0. Verdict

- No false statement was found in the Lean library. Every cited declaration exists, its type matches the LaTeX, and none
  is vacuous. No `sorry` or extra axioms; the index regenerates byte for byte.
- The problems are in the prose:
  - three errors (§1);
  - several comparisons with earlier papers of the series that those papers already beat at the advertised parameters
    (§2);
  - missing citations (§3);
  - an overstatement of how much is formalized (G1).
- None of the fixes needs new mathematics. Optional strengthenings are marked as such.

## 1. Errors (must fix)

**E1. The lower bound 24 ≤ D₁ in characteristic 3 has no source.**
- *Where:* `paper/sections/aperiodic_six.tex:9` and `:114`, `introduction.tex:167–168`, `sweep.tex:268–270`,
  `README.md:38` and `:58`, `extension.md:50`.
- *What the sources say:* Memo Problem 6.1 only asks whether 25 is attainable in characteristic 3. Paper 17 (Problem
  9.1(b), and §8 after Proposition 8.2) says only that 25 is open there. Nothing in the series gives 24.
  - Copy rules cannot reach 24 for this partition: they would need the classes to tile ℤ₆ by translation, and
    {0, 1, 3} does not.
  - Valid in every characteristic is 21, from symmetric matrices with the single decoder A(Y)_r = Y_{r,0}, which gives
    X_{c,r} = X_{r,c}.
- *Fix:* write "21 ≤ D₁ ≤ 28 in characteristic 3 (symmetric matrices; Theorem TP)". Keep memo Problem 6.1 as the
  citation for "whether 25 is attainable is open". Alternatively supply a verified characteristic-3 certificate of
  dimension 24.

**E2. The one-sided baseline in Corollary 7.5 is attributed to the wrong result, with the wrong constant.**
- *Where:* `swapcodes.tex:251–252`.
- *What is wrong:* The text says Proposition 7.3 "sees s_A + 1 and s_B + 1 intervals and gives leading coefficient
  ½ + ½ min(α, β)".
  - Proposition 7.3 needs d = 2^m and aligned dyadic intervals; the coarse interval here has length d − s and d is
    general.
  - With s + 1 intervals, Proposition 7.3's own formula has β = 2(s + 1), which gives ½ + min(α, β), not
    ½ + ½ min(α, β).
  - The ½ + ½ min baseline is Theorem TP's interval clause, (d² + Md)/2 with M = s + 1.
- *Fix:* cite Theorem TP, stating how it applies to these swap codes. Say that the Theorem TP side of Corollary 7.5 is
  not in Lean: part (a) is a real inequality only, and no Lean theorem applies TP to `InContiguousCoarseFineSpan`.

**E3. Two outlines contain wrong steps.** The Lean proofs are independent and correct.
- `swapcodes.tex:69` (outline of Theorem 7.1). "X_{0,0}ᵀ − X_{1,1}ᵀ = X_{1,1} − X_{0,0}" should read
  "= X_{0,0} − X_{1,1}". The conclusion stands.
- `duality.tex:217–220` (outline of Theorem 8.7(a)). "Y = X₁ − rot_{−s}(X₂) ∈ C" is unjustified, since C need not be
  rotation-invariant.
  - Replace it with the Lean argument: from rot_{c₁}X₁ = rot_{c₂}X₂ we get X₁ = rot_s X₂, so take Y = X₂, with
    rot_s Y = X₁ ∈ C.
  - Linearity of C is not used; drop "on a linear subspace" or say so.

## 2. Overclaims (must fix)

**O1. Section 5 compares itself with the weak form of paper 19's Theorem 3.5.**
- *Where:* `linear_capacity.tex:21–36`, `abstract.tex:47–50`, `introduction.tex:151–158`, `README.md:35`.
- *The problem:* The text compares only with the square-root corollary (eq. sqrt-classes). Theorem 3.5 also states, and
  proves in Lean, eq. (many-classes): D ≤ bd² − bd(d − U)/(u + v) for all u, v ≥ 1 (`difference_cover_real_bound`).
  - Its leading coefficient, optimised over u and v, is about 1 − 1/(3√(3M)).
- *Consequences:*
  - It beats c_M = 1 − 5/(4M) + … for every M ≥ 41. At M = 41, with u = v = 11, it gives 0.96982 against
    c₄₁ ≈ 0.97010.
  - So "Theorem 5.5(b) improves on Theorem 3.5 at large primes" is false for M ≥ 41. It is true for 3 ≤ M ≤ 40, and
    there only past large crossovers: about d > 5·10⁵ at M = 40.
  - At M = 2 the threshold is d ≥ 35, not 29. At d = 29, eq. (many-classes) gives 703.25b against 733.6b.
  - "Applies to composite d ≥ 2M" is no advantage: eq. (many-classes) has no M ≤ d/2 restriction.
- *Fix:* compare with the optimised eq. (many-classes) throughout. State the true ranges: c_M is better exactly for
  2 ≤ M ≤ 40, and the M = 2 threshold is d ≥ 35.

**O2. Section 5: "Theorem 3.5 first beats the flag bound at M ≥ 11".**
- *Where:* `README.md:35`, `extension.md:34`, `linear_capacity.tex:22–26`.
- *What is wrong:* This holds only for the square-root form. Eq. (many-classes) already beats the flag bound from
  M = 7: u = 4, v = 5 gives 25/27 < 13/14.
- *Fix:* state both.

**O3. Theorem 2A is weaker than paper 19 at the parameters the text showcases.**
- *What paper 19 gives:* its Theorem 6.3 (`thm:two-linear-stages`).
  - At M₂ = 1 two distinct columns in one first-stage class already contradict ℓd ≤ M₂d + (ℓ−1)M₂·gcd(d, s), so
    d ≤ M₁. Paper 20 advertises d ≤ max(8M₁, 4M₁²).
  - At M₁ = 1 it gives d ≤ M₂². Paper 20 gives max(8M₂², 2^{2^{M₂}}).
- *Where:* `abstract.tex:18`, `cubes.tex:103`, `:105`, `:107`, `introduction.tex:89`, `README.md:21`, and the
  docstring at `AffineCubeConsequences.lean:590–592`.
- *Also wrong:* Remark 3.4 (`cubes.tex:130–134`) says Theorem 6.3 "supplies no quantitative upper bound on
  W(M₁, M₂ + 1)". That is false in these cases: W(M, 2) = M + 1 and W(1, ℓ) = ℓ. Explicit tower-type van der Waerden
  bounds also exist in the literature.
- *Fix:*
  - drop the M₂ = 1 parenthetical, or replace it with "(at M₂ = 1 the bound d ≤ M₁ of [19, Thm 6.3] is stronger)";
  - restrict the advantage claims to M₁, M₂ ≥ 2;
  - say what is actually gained: for fixed M₂ ≥ 2 the cutoff is polynomial in M₁, while every progression-based
    cutoff is at least M₂(W(M₁, 3) − 1), which is superpolynomial in M₁.

**O4. Theorem 2B is weaker than paper 19 at M₁ = 1, and the open problem built on it is already solved there.**
- *What paper 19 gives:* its Theorem 6.6 (`thm:two-stage-rank`) with W(1, ℓ) = ℓ and k ≈ d/(2(2M₂ + 1)) gives a rank
  deficit of order bd²/M₂. It is quadratic, holds for every d, and is in Lean (`twoHop_rank_interval_any_field`).
- *At M₁ = 2:* Theorem 6.6 at k = 2 gives b(d − 177), using W(2, 5) = 178. Theorem 2B beats it only for d ≳ 10^216.
- *Where:* `sumsets.tex:12–16`, Remark 4.7 (`:224–225`), `sweep.tex:261–263`, `README.md:57`.
- *Fix:*
  - state the improvement for M₁ ≥ 2 and large d;
  - note that at M₁ = 1 Theorem 6.6 already gives Ω(bd²/M₂);
  - replace "does not supply an explicit growth rate" with "is stated with qualitative W; Gowers' bound gives only an
    iterated-logarithmic rate for M₁ ≥ 2";
  - restrict the open problem "Ω_{M₁,M₂}(bd²)" to M₁ ≥ 2.

**O5. The "O(log d) ceiling" framing in Section 4.**
- *Where:* `introduction.tex:60–64`, `sumsets.tex:14–16`.
- *What is wrong:*
  - The fact itself (an O(log d)-length bound for non-wrapping progressions under random colourings) is uncited.
  - It is false as stated for progressions in ℤ_d with s = 0 or steps of small order.
  - Theorem 2B never passes that ceiling: Lemma 4.5 has k = O(log d). The real gain is replacing tower-type van der
    Waerden numbers by Kővári–Sós–Turán density bounds.
- *Fix:* say "non-wrapping progressions in {0, …, d−1}", add a citation (a standard first-moment colouring argument),
  and reframe the gain accordingly.

**O6. The d = 12 witness is misdescribed.**
- *Where:* `introduction.tex:124–126`, `README.md:29`, `sumsets.tex:273–275`, which describe "relaxing stage-1 shift
  covariance to an arbitrary linear readout".
- *What is wrong:* The Lean witness keeps shift covariance: one fixed L for all c. The readout in the real setting is
  already arbitrary linear.
- *What the witness shows:* a single half-density band relaxation, without the (2M₂)-fold sumset iteration, admits
  kd-dimensional solutions, so the iteration in Theorem 4.4 is essential.
- *Related:* only the b = 2, M₂ = 1 reading has a Lean equivalence, and it reaches kd = 24, not bkd = 48. The
  "b = 1, M₂ = 2" reading (`sumsets.tex:255–260`) is not formalized.
- *Fix:* say both.

**O7. The two-sided bound "improves strictly" is false at finite d.**
- *Where:* `swapcodes.tex:120–122`, which says it "improves strictly … whenever both sides localize fine intervals to
  proper regions of ℤ_d".
- *Counterexamples:*
  - On the contiguous family, Theorem TP minus B_cf equals (s(d − s) − 2s − d)/4, which is negative at s = 1. At d = 8,
    Theorem TP is at least as good for 48 of the 49 pairs.
  - With S equal to the even residues, B_cf = 1.1875d², which is vacuous.
- *Fix:* "improves the leading coefficient when s_A and s_B are proportional to d and the run and coarse counts are
  o(d)".
- *Same fix elsewhere:*
  - In the root README row, add "contiguous" and "in leading coefficient".
  - In the abstract (`:58–61`), identify ½ + ½ min(α, β) as Theorem TP's coefficient.

**O8. Theorem 7.4 is presented as a bound for Problem 9.3, which it is not in general.**
- *Where:* `abstract.tex:56–57`, `introduction.tex:179–181`, the §7.2 title, `swapcodes.tex:120`.
- *Why it is narrower:* `HasCoarseFineIntervalDecomposition` allows only masks ⊆ S, a coarse interval, or the full set.
  Nested families with three or more scales force the intermediate intervals into S, so Theorem 7.4 gives no profile
  bound for them.
- *Fix:* "a two-sided bound for two-scale (coarse–fine) families of Problem 9.3", plus one sentence on the nested-scale
  limitation.

**O9. Section 6 overstates where the result sits.**
- `aperiodic_six.tex:7–8`, "the smallest partition of ℤ_d with no shift almost-period in which a code beats the interval
  value": no source shows "smallest". Write "the partition of [17, Prop 8.2], which has no almost-period
  ([17, Remark 8.1(c)])".
- Section title: "Exact dimension 25 for {0,1,3} | {2,4,5} on ℤ₆ outside characteristics 2 and 3".
- `introduction.tex:64–69` credits run-extension with determining D₁ = 25. Run-extension (Theorem 1A) gives only ≤ 26;
  the value 25 needs the six-mode Fourier analysis. Split the sentence.

**O10. The "5/8 floor" is described more strongly than paper 19 shows.**
- *What paper 19 shows:* Theorem C.6 is a floor for its nested-component certificates on almost every two-class
  partition. The isolation variant, Theorem C.7, has 9/16. Neither is a capacity floor for nonlinear decoders, and
  neither attributes the floor to nonlinearity.
- *Where:*
  - `linear_capacity.tex:3` (title) and `:41–44`;
  - `introduction.tex:65–69`, which also lacks "when char(F) ∤ d", and `:130–133`;
  - `abstract.tex:44`;
  - the root README row and `extension.md:33`.
- *Fix:* "the nested-component certificates of [19] cannot go below 5/8 − o(1) on almost every two-class partition". In
  the root README, also name paper 19's 41/64 bound, which 19/32 improves.

**O11. "Column classes cannot absorb per-entry cut labels" is stronger than Proposition 9.6.**
- *Where:*
  - `introduction.tex:213–216`;
  - `README.md:49` and `:52`;
  - `sweep.tex:167` (§9.3 title) and `:194–203`;
  - the docstring at `MachineSweepConsequences.lean:21–22`.
- *What Proposition 9.6 shows:* negativity for two specific schemes, discarding cut outputs and a posited class count
  M_cls. It does not show how many classes an absorption needs.
  - The proof uses only M_cls ≥ L_cut + 1.
  - On periodic stretches few cut patterns occur, so the bracket may be positive. The real obstruction there is
    Remark 9.5(2).
  - The per-position conclusion is already in paper 17's commentary on Problem 9.4(b).
- *Fix:*
  - "illustrates that these two absorptions fail";
  - say that M_cls is a worst-case choice;
  - credit paper 17;
  - drop "showing why … requires" and "cannot".

**O12. Statements that hold only in leading coefficient or under unstated conditions (Section 5).**
- `linear_capacity.tex:209–211`. The 19/32 bound is below (3/4)d² only from d ≥ 93 at M = 2.
- `linear_capacity.tex:30–31` and `introduction.tex:155–156`. "Improves on Theorem 3.4 for all d ≥ 1" is vacuous for
  d ≤ 13.
- Theorem 5.3 "All-field sharpness" and line 160 "attained … over every field". The value m² + 3m is realised over every
  field, but Theorem 5.2 needs char(F) ∤ 2m.
- Titles saying "Universal 19/32" (`:204`, `:213`) need "char(F) ∤ d".
- `:47–48`, "strictly more linear constraints than H_{0,s}": fails for monochromatic orbits (M = 1, or s = 0).
- `:5–8` and `:46–47` cite paper 17's Problem 9.1(a) and Definition 6.3 as if they were stated for b lanes; they are
  stated for b = 1.
- `:57–58` is garbled ("matrices … have shifted rows").
- `:206–207`, "Grassmann identity": should be "inequality".
- `README.md:58`, "composite d for M ≥ 3". Theorem 5.2 already holds for composite d; only the averaged multi-class
  bound needs primes.

## 3. Missing or wrong citations

- **C1. The cube lemma.** Lemma 3.2 is the classical Szemerédi (density Hilbert) cube lemma; cite Szemerédi 1969 and
  Graham–Rothschild–Spencer. Lemma 3.1 specializes to [19, Lemma 6.1] (all R_t = R), with the same nested-span proof;
  say so.
- **C2. Behrend.** Behrend gives one 3-AP-free set. A partition of ℤ_d into 2^{O(√log d)} 3-AP-free classes needs a
  translate-covering step; say so and mark it as not formalized.
  - Where: `cubes.tex:103–109` and `:132–133`, `introduction.tex:61` and `:90`, `abstract.tex:16–17`, `README.md:21`.
- **C3. Paper 19's Lemma 3.1 and its Lean.**
  - Theorem 8.7(a), (c) and Proposition 8.8 restate this lemma:
    - `commonPreimage_le_covariance`, `finrank_covarianceSpace`;
    - `covarianceSpace`/`covarianceEquiv`, which is the anti-diagonal normalisation;
    - `covarianceSpace_rot`, `isSharedCode_iff_compatible`.
  - Cite it, and say that what is new is the `TensorProduct` packaging Ψ.
- **C4. The cone lemma.** Lemma 9.1 is paper 4's cone lemma (Lemma 4.4, Corollary 4.5). Lean versions exist in paper 11
  (`MergeDepth/FieldDag.lean`, `FunDag.cone`) and paper 18 (`AdaptiveTransfer/FrozenCutInvoice.lean`,
  `stepValue_eq_of_uncut_native_cut`, `native_cut_recovers`). Cite them. New here are the (k + 1)^D size bound and the
  symbolic tree evaluator.
- **C5. The paper 17 pin is stale.** Paper 17's commit `2f853e5` (Nov 11) adds Propositions 6.24–6.27 and Problem
  9.4(c). Its Proposition 6.25(a) covers stages whose rows read cosets of rows, and subsumes Proposition 8.5(c). Re-pin
  and compare. Theorem 8.3(a) remains distinct. The other cited numbers are unchanged.
- **C6. Paper 1's Conjecture 9.1 is misdescribed** (`introduction.tex:12–14`; correction report A9, only partly fixed).
  It says that no causal code solves complete exchange on the block networks of linear-length tape diagrams, in a robust
  co-entropy form. It is not an "asymmetric bipartite storage-coding conjecture". The Harvey–van der Hoeven direction is
  now correct.
- **C7. Open problem 4** (`sweep.tex:284–287`, `README.md:60`).
  - Problem 9.4(a) concerns oblivious schedules, not adaptive ones.
  - Cite paper 18's adaptive transfer (Theorem H.5, Corollary H.6).
  - Quote 9.5 exactly: a quantity "not raised at all scales by a single linear-time operation".
  - Mention 9.4(c).
- **C8. The other open problems.** Open problem 1 is paper 19's own open question; credit it. Open problem 3, on Walsh
  masks, is a variant of 9.3, which concerns dyadic interval masks; say so.
- **C9. "Θ(log d) scales [4, §3]"** (`sweep.tex:204–205`, `README.md:11`, `extension.md:8`) is not in paper 4's §3,
  which proves that linear-time transposers need curved, head-dependent, non-piecewise-affine motion. Fix the
  citation.
- **C10. Smaller citations.**
  - `aperiodic_six.tex:113`: "char 2 (25 ≤ D₁ ≤ 28, [17, Prop 8.2])". The 28 is Theorem TP (Theorem 6.4), and memo
    Theorem 3.2 also covers characteristic 2.
  - `sumsets.tex:10`: the quote of [19, Thm 6.6] omits its hypothesis d ≥ N₀.
  - Standard facts without citations: OSR(SWAP) = d², submultiplicativity of OSR.
  - Theorem 9.3(a)'s injectivity duplicates `LeanMachine.OrderedRecovery.eq_of_rank`.

## 4. Global items

- **G1. The claims that everything is formalized are not accurate.**
  - *Where:* `README.md:15`, the root README row ("Lean 4 formalization of every numbered result"),
    `formalization.tex:65–67` and `introduction.tex:221–228`.
  - *Proved only in the text:*
    - the asymptotic and Behrend consequences of Theorem 2A (`cubes.tex:103–109`; the Lean theorem is only the
      pointwise contrapositive);
    - the Theorem TP side of Corollary 7.5;
    - the general padded-family dimension 4m(m+1) + s(s+1)/2 + 2ms (`swapcodes.tex:104–109`);
    - the difference formula in Theorem 5.5(c);
    - "indeed preserves rank" in the outline of Theorem 4.4 (Lean proves ≤);
    - the explicit formulas of Lemma 4.1 (the Lean statement is existential);
    - the intertwining claim in Proposition 2.1(a), which is definitional.
  - *No Lean line at all:* Remark 5.6, which is numbered and makes a mathematical claim (it is correct).
  - *Fix:* use `\partformal` with a "Not formalized:" line where needed. Reword the READMEs as "every numbered result
    has a Lean counterpart; the following parts are proved in the text only: …".
- **G2. `extension.md`** duplicates the README's claims list and repeats several errors. Either delete it or bring it in
  line:
  - line 50: E1;
  - line 34: O2;
  - line 33: O10;
  - line 24: the untwisted P(ωZ) − P(Z), where the paper uses P(ωZ) − ω^D P(Z);
  - line 27: no char(F) ∤ 2m;
  - lines 14 and 18: no field or linearity qualifiers;
  - lines 6–7: "shared decoders … fail" inverts the point, since it is the capacity bounds that fail. Also
    "1 − 1/(Δ+1)" should be "1/(Δ+1)" and "ε ≍ 1/D" should be "ε = Ω(1/D)";
  - line 8: C9.
- **G3. The root README row** needs the fixes of G1, O3, O4, O7, O8 and O10. Two more:
  - "a Lean proof of the fourth paper's 1/(Δ+1) bound" should say that it is the storage-code (column-class)
    analogue;
  - "uniformly at d = 4" should be "over every field at d = 4 (paper 17's example, previously checked over F₂, F₃, F₅,
    F₇)".
- **G4. "Ramsey-free" (title and text). Optional, author's choice.** The cube lemma and Kővári–Sós–Turán are themselves
  Ramsey-type or extremal statements. What the bounds avoid is van der Waerden and Hales–Jewett numbers. Consider
  "van der Waerden-free", or say once what "Ramsey-free" means.

## 5. Minor items

- **Section 2 (`model.tex`).** Proposition 2.1(b): the step "every algebraically closed extension" goes through
  (n : K) ≠ 0 ⇔ (n : F) ≠ 0, which is trivial but unstated.
- **Section 3 (`cubes.tex`).**
  - `:12–13`: "L(T_c w) = L(w) for all c in a single class J", with L injective, is false unless 0 ∈ J. Use the
    reference shift c_ref, as Lemma 3.2(a) already does.
  - `abstract.tex:17–18`: the M₂ = 1 parenthetical is attached to the "M₂ ≤ (1−ε) log log d" clause, but M₂ = 1 is
    not a growing schedule. Also, "up to M₁ = o(…)" reads as sharp; use "whenever".
  - Lean names still say "Sharpness" (`Control_D13TwoCubeAPFreeSharpnessSpec`, label `ex:d13-sharpness`), but only
    9 ≤ max ≤ 10 is shown.
- **Section 4 (`sumsets.tex`).** Say once that log is the natural logarithm (as in `theorem2BExplicitConst`).
- **Section 5 (`linear_capacity.tex`), optional strengthening.**
  - `:274–280`: the proof of Theorem 5.5(b) gives a (5/4)bd error term, not bMd, and it also works for M = 2. At
    prime d this gives (19/32)bd² + (9/8)bd, which beats Theorem 5.4(b).
  - The sharper form also moves every crossover with Theorem 3.5 down.
- **Section 6 (`aperiodic_six.tex`).**
  - `:17–20`: add Theorem 1A's hypothesis "when char F ∤ 6".
  - `:115–116`: the failure in characteristics 2 and 3 is that F̄[ℤ₆] is not semisimple, so the six-mode decomposition
    is unavailable. That explains why the method fails; it does not prove openness.
  - `README.md:38`: "any equivalent two-class coloring" should be "any coloring with the same fibers (class
    relabeling)".
- **Section 7 (`swapcodes.tex`).**
  - `:104–109`: mark the general padded-family dimension "(not formalized for general m, s)". It checks numerically for
    m ≤ 4, s ≤ 3.
  - Remark 7.6 reports a "largest observed dimension … by SVD", but SVD of random elements gives the generic dimension.
    Describe the search procedure and give a script, or cut the remark.
  - Leftover Lean docstrings:
    - `DualityAndSwapConsequences.lean:1098`, "Bonus 1 Unified Remark 5.6 Disproof Corollary";
    - `SwapCodeAnswers.lean:10` ("answering two questions from Paper 17") and `:206` ("Answering Remark 5.6");
    - `ExtensionTwoSidedProfile.lean:31–32` claims "for all d ≥ 10", but the type proves only the k ≥ 9 clause.
- **Section 8 (`duality.tex`).**
  - `:13–14` and `:73–91`: the bound of Theorem 8.3(a) is attained, since Sᵐ = τ (Stone). Say so; it is a one-line
    Lean fact.
  - `:152`: the outline writes s where it means t.
  - `:135`: "invariant" should be "the source-arity bound is preserved".
  - `:160`: X_{:,c'} is a source column, not a target column.
  - "Shuffle-and-local" persists (correction report B3), but A ⊗ I_{db} with a dense A is not local.
- **Section 9 (`sweep.tex`).**
  - `:186–191` mixes two depth conventions:
    - "(M.k+1)^{D+1} > 1/ε" counts edges, as in paper 4, while Δ = b(M.k+1)^D counts vertices; the inference needs
      paper 4's bound at edge-depth D − 1;
    - paper 4's 4.14(c) is stated for oblivious machines; say that the same proof applies to a frozen fibre's
      trajectory.
  - `:150`: "whole-column support d" is no restriction; only the cell arity 2d − 1 constrains.
- **Appendix (`formalization.tex:35–48`).** The description of layer 2 omits the OSR, cone and one-hop content of three
  proof modules.

## 6. Status of the first correction report

Item numbers refer to the report of 2026-11-11, in this file's history.

- **Fixed:** A1–A8, A11, B1, B2, B5, B6, B8, B9 and C.
- **Partly fixed:**
  - A9: see C6;
  - A10: see C7;
  - B3: see the "shuffle-and-local" item in §5;
  - B7: see O10;
  - the "why" of A3: see O11.

## 7. Checked and correct

- *Lean statements.* All match their LaTeX. Among them:
  - Theorems 2A and 2B with the exact constants; c and D₀ match, D₀(1,1) = 16³⁶ + 2;
  - Theorems 5.2–5.5;
  - the main theorem of §6 (≤ 14, ≤ 25, `IsGreatest` 25 for char ∉ {2, 3});
  - Theorems 7.1, 7.2 and 7.4;
  - Theorems 8.2, 8.3 and 8.7;
  - Lemma 9.1 (non-vacuous: any transposer on a singleton fibre);
  - Theorem 9.3.
- *Numerics, recomputed exactly:*
  - the §6 determinant: 432, or 16/3 after scaling;
  - the alternating codes for m ≤ 5 over three fields;
  - 19/32 and c₃ = 37/54, c₄ = 191/256;
  - the d = 13 and d = 4 controls;
  - OSR(τ) = d², OSR(S) = 4, OSR(shear) = d, for d ≤ 16;
  - B_cf algebra;
  - 5/8 arithmetic.
- *Infrastructure.*
  - The lean-machine transition tables for shuffle, unshuffle and row shear are verified in O(L).
  - The Transpose statement resolves to paper 1's frozen file; sha256 matches `FROZEN.sha256`.

## 8. How remarkable is it?

It is a competent, broad, heavily formalized paper: about 22,000 lines of Lean, faithful and non-vacuous. It is
incremental, and it does not move Statement (T); the paper says so in its scope caveat. Its results, roughly in order of
substance:

1. **D₁({0,1,3} | {2,4,5}) = 25 over every field of characteristic other than 2 and 3 (§6).** This is the first exact
   value of D for a partition with no almost-period, where Theorem TP's 28 is not tight, and it settles paper 17's
   Problem 9.1(b) in those characteristics. The upper bound is new; the lower bound is the memo's. The method is a
   hand-made six-mode Fourier analysis that does not extend beyond d = 6, but the 2300-line Lean proof is durable.
2. **The 19/32 + o(1) two-class bound for linear decoders, when char(F) ∤ d (§5).** This is the best universal
   two-class bound now known. It improves paper 19's 41/64, which also covers nonlinear decoders and every field, and
   B_run is sharp on the alternating colouring. It is a constant improvement by elementary means, and the multi-class
   part is weaker than paper 19 for M ≥ 41 (O1).
3. **Theorems 2A and 2B (§3–4).** These substitute density arguments (the cube lemma, Kővári–Sós–Turán) for van der
   Waerden numbers. For fixed M₂ ≥ 2 the cutoff becomes polynomial in M₁, and for M₁ ≥ 2 the growth rate becomes
   explicit. Both are classical tools in a new place. Both lose to paper 19 at small parameters and at M₁ = 1 or
   M₂ = 1, and the gain in 2B only shows for astronomically large d.
4. **Theorem 7.4 (§7).** A technically new, characteristic-free two-sided bound, kernel-checked, improving the leading
   constant on two-scale families (3/4 → 11/16 at half density). The three-term swap codes add examples at d = 6, 7, 9
   and 12, and prove paper 17's d = 4 example over every field; the method provably stops above d = 12.
5. **Infrastructure (§8–9).** Verified linear-time Turing machines for shuffle, unshuffle and row shear, which are new to
   the series. The rest is a repackaging of paper 19's Lemma 3.1, formalizations of paper 4's cone lemma (with partial
   precedents in papers 11 and 18) and of its 1/(Δ+1) bound, and a nearly tautological Proposition 9.6.

Overall it is closer to a long memo than to a paper that changes the frontier. After the fixes it is a solid,
trustworthy record of these results.

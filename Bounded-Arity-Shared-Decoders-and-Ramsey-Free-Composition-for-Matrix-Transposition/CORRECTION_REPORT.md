# Correction report for paper 20

*Bounded-Arity Shared Decoders and Ramsey-Free Composition for Matrix Transposition*, reviewed at commit `6aaaba7`
on 2026-11-11 by Claude Fable 5.2 (Anthropic) at the request of Hans Brende.

## 0. Scope, method and verdict

**What was checked.** Three-way consistency between the README (the initial statement of claims), the Lean library
and the paper, and whether the structural claims move the wall described in paper 17.

- The library was rebuilt here: `lake build` succeeded (9400 jobs). `PaperAxioms.lean` prints 232 lines, all on
  `propext`, `Classical.choice`, `Quot.sound` or fewer. The sources contain no `sorry`, `axiom`, `native_decide`,
  `opaque`, `unsafe` or `set_option`.
- Two independent audits (Lean against README; paper text against README, Lean and the cited papers) and a direct
  reading of the specification files, `MachineSweepConsequences.lean`, the abstract and the introduction. Every
  quotation of another paper below was re-read in that paper's source.
- Not checked: the roughly 22,000 lines of proofs line by line; the proofs of the sibling libraries; external
  bibliographic data; the PDF (sources only).

**Verdict.**

1. *The Lean library is sound and the headline theorems are faithfully formalized.* Every `...Spec` proposition
   that the paper presents as a result has a theorem of exactly that type. No hallucinated proof was found.
2. *The paper's claims about what these theorems mean for the series are wrong in several places.* The capacity
   theorem is a weaker form of a bound the series has had since the fourth paper, and that paper also proves that
   this kind of bound can never contradict a transposer (§A1, §A2).
3. *The machine-facing layer is empty.* The two "native sweep extraction" theorems are true, but their capacity
   conclusions can never be below the trivial bound under their own hypotheses (§A3). The "conditional closures"
   assume hypotheses equivalent to their conclusion (§A4). Three Lean statements about cut cones are satisfied by a
   one-element footprint (§A5).
4. *Several statements about earlier papers are misquoted* (§A7–§A11), and one displayed formula is wrong (§A6).
5. *What stands and is new:* Theorems 4.4 (2A) and 5.6 (2B) on two-stage linear composition, the three-term
   examples at d = 6, 7, 9, 12, the all-field proof of the d = 4 example, and the linear-time machines for shuffle,
   unshuffle and shear (§D).

Paths below are relative to the repository root. `P20` is this folder, `P17` is
`Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes`, `P19` is
`Capacity-and-Composition-of-Shared-Transposition-Decoders`, `P4` is
`Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes`.

## A. Errors (false or contradicted statements, vacuous results)

### A1. The capacity theorem is not the first bound below rate 1; a stronger one is in the series

**Claimed.**
- `paper/sections/abstract.tex`, lines 22–24: "the first unconditional strictly-below-1 capacity bound on
  arbitrary nonlinear sets at every constant arity Δ ≥ 3 (where [Problem 9.4(b)] remained open at rate 1".
- `paper/sections/introduction.tex`, lines 93–98 and 185: "no nontrivial upper bound < 1 on arbitrary sets was
  known"; "the *first* nontrivial (< 1) capacity bound".
- `paper/sections/capacity.tex`, lines 15–17 and 191–193: "open at rate 1"; "had no bound below rate 1".
- README, §I and §II: "Wall 1 collapses unconditionally".

**Against this.**
- `P17/paper/sections/wall.tex`, lines 20–21: "The only general upper bound is the elementary one for relations of
  degree at most Δ, a rate of 1 − 1/(Δ+1) [Proposition 4.14 of the fourth paper], which is useless at the depths in
  question."
- `P4/paper/sections/decomposition.tex`, Proposition 4.14 ("The counting bound cannot replace the crux"):
  (a) the acyclic-subgraph bound; (b) "MAIS(I) ≥ (L − triv(I))/(B + 1)", by a uniformly random order.
- The same bound is quoted in `Directed-Recovery-Structures-in-Tape-Computations/paper/sections/open.tex` ("the
  acyclic-set argument already gives rate at most 1 − 1/(Δ+1) + o(1) …; mere positivity at each fixed degree is
  therefore not the open problem"), in
  `Nested-Elimination-and-Half-Rate-Bounds-for-Storage-Codes/paper/sections/construction.tex`, lines 37–38, and in
  `High-Rate-Separated-Storage-Codes-and-Tape-Transposition/paper/sections/consequences.tex`, line 49 ("The
  elementary gap 1/(Δ+1) obtained by ordering coordinates").
- Problem 9.4(b) of paper 17 (`P17/paper/sections/open.tex`) asks whether the bound is q^((1/2+o(1))d²). It does not
  say that rate 1 was open.

**The stronger bound in this paper's setting.** With the notation of Theorem 3.4 (`thm:set-capacity`):

> log_|Σ| |C| ≤ d² − (d² − |E| − dMΔ) / (Δ + 1).

Proof. Order all d² cells uniformly at random. Let A be the set of clean entries x = (c, r) all of whose footprint
cells F_x come before x. Since x ∉ F_x and |F_x| ≤ Δ, P[x ∈ A] ≥ 1/(Δ+1). Two elements of C that agree outside A
agree on A: go through A in the order; the footprint of each x ∈ A lies before x, so it is outside A or already
settled. Hence |C| ≤ |Σ|^(d² − |A|) for every order, and some order has |A| ≥ (#clean)/(Δ+1).

This is the multi-hop version of the one-hop argument of the paper. The deficit 1/(Δ+1) exceeds
Δ^Δ/(Δ+1)^(Δ+1) by the factor ((Δ+1)/Δ)^Δ, between 2 and e. At Δ = 2 it gives 2/3 where Corollary 3.5 has 23/27;
at Δ = 3 it gives 3/4 where the abstract has 229/256.

**Further remarks.**
- The proof of Theorem 3.4 uses only the recovery relation. That the decoders are shared enters only through the
  count dMΔ of self-referential entries. So the theorem does not combine sharing with bounded arity in any way
  that the degree bound did not.
- At Δ = 2 with one class, paper 17 (revision `a445cd8`, Proposition 6.22(b)) proves rate 1/2 + 3/(2d). The
  paper cites this. The README's "immediate clean finite problem" (maximum rate at M = 1, Δ = 2) is therefore
  answered: 1/2 + Θ(1/d). The Lean docstring of `OneClassArityTwoHalfBarrierQuestion`
  (`lean/BoundedArityDecoders/BoundedAritySetCapacity.lean`, line 282) still calls it open.
- Proposition 6.22(b) of paper 17 is for a function per position, so it also covers M = 2, Δ = 1, and a broken
  set E costs |E| in the exponent. It is not limited to "M = 1, E = ∅".

**Fix.** Remove every "first" and "open at rate 1". Present Theorem 3.4 as a Lean formalization of a weaker form
of Proposition 4.14(a),(b) of the fourth paper for shared decoders, or strengthen the Lean statement to 1/(Δ+1)
by replacing the Bernoulli one-hop set with the random-order set above. Correct 23/27 and 229/256 accordingly.
Add the fourth paper to `references.bib`.

### A2. The Θ(1/Δ) route to (T) is already closed in the series

**Claimed.** `paper/sections/sweep.tex`, lines 113–117 and 172–178, present a "direct Θ(1/Δ)-deficit route" as a
live open target; `PeriodicCellSweepReductionHypothesis` (`lean/BoundedArityDecoders/MachineSweepConsequences.lean`,
lines 1069–1094) asks for a constant Δ and an advice rate ε < (δ/2)·p_min(Δ)/(4c).

**Against this.** `P4/paper/sections/decomposition.tex`, Proposition 4.14(c): for a machine with k work tapes and a
genie of depth at most D and cost at most εL, "(k+1)^(D+1) > 1/ε. Consequently … the lower bound
(L − triv(I))/(B+1) given by (a) and (b) is smaller than εL; it never contradicts the existence of an index code
with εL bits, such as the revealed word G_Γ when M is a transposer." The comparison is repeated, and checked in
Lean, in the fifteenth paper (`consequences.tex`, lines 49–55).

Since the deficit of Theorem 3.4 is smaller than 1/(Δ+1), the same obstruction applies to it: with cones from a
depth-D cut the advice costs about L/D bits and the deficit is about L/(k+1)^D. No choice of D makes the second
larger than the first.

**Fix.** Cite Proposition 4.14(c) and remove the Θ(1/Δ) route from the list of open targets, or say what new
ingredient would make Δ independent of ε.

### A3. Theorems 8.2 and 8.3 can never give a bound below the trivial one

Both theorems (`thm:sweep-cut-absorbed`, `thm:sweep-cut-refined`; Lean `tmPeriodicSweepExtraction_cutAbsorbed`
and `tmPeriodicSweepExtraction_cutLabelRefined`) are true. Their capacity conclusion is the bound of Theorem 3.4
with a bracket d² − |E| − d·M·Δ. Under the theorems' own hypotheses this bracket is never positive.

**Common facts.** The dependency relation `TMDepStep` contains the spine edge u → u + 1. The hypothesis `hPathLen`
bounds every Γ-free path by D vertices. So for every step v ≥ D the largest cut step u*(v) < v exists and satisfies
v − D ≤ u*(v) < v; the step u*(v) + 1 lies in the cut cone of v, and `TMDepStep u*(v) (u*(v)+1)` holds. By the
fifth clause of `IsFrozenTraceCutFibre`, distinct output bits are emitted at distinct steps (for nonempty C).

**Theorem 8.2 (cut-absorbed).** A cell (r, c) with a bit emitted at a step v ≥ D lies in
`cutTouchingOutputCells`, which is part of E. At most D output bits are emitted before step D. So at most D cells
lie outside E, and d² − |E| ≤ D < 2^D ≤ Δ ≤ d·M₀·Δ.

**Theorem 8.3 (cut-label-refined).** By `hColCutsCover`, for every cell (r, c) ∉ E_sched and every bit, the cut
step u*(v) of its emission step must be one of the L_cut slots of column c. A cut step is u*(v) for at most D
emission steps. If column c has n unbroken cells, then L_cut ≥ (n·b − D)/D, that is n ≤ D(L_cut + 1)/b. Hence

> d² − |E_sched| ≤ d·D·(L_cut + 1)/b ≤ d·M₀·λ^L_cut·b·(k+1)^D = d·M_cls·Δ,

with λ = (q+1)(g+1)^k ≥ 2, using λ^L ≥ L + 1 and (k+1)^D > D. (λ = 1 means one control state and one work
symbol.) "Zero extra broken cells" is misleading: E_sched must already contain all but D(L_cut+1)/b cells of
every column.

**Why.** Cut labels are attached to output entries, and every output cone ends at a cut within D steps. Classes
of columns cannot absorb them. This is the point of paper 17's distinction between one function for all rows and
a function per position (`P17/paper/sections/open.tex`, commentary on Problem 9.4).

**Also.** The cell arity here is Δ = b(k+1)^D with b = ⌈log₂ d⌉, which grows with d; `sweep.tex`, line 176,
writes Δ = (k+1)^D against Δ := b(M.k+1)^D at line 61.

**Fix.** State the two facts above next to the theorems, and do not describe them as a bridge for Problem 9.4. The
non-vacuous content is `evalConeTree_traceConeTree_eq` (the symbolic tree evaluated through `M.δ` reproduces the
run on a frozen fibre). That is worth stating as the theorem.

### A4. Theorem 8.4: the hypotheses are equivalent to the conclusion

In `PeriodicCellSweepReductionHypothesis` and `OneClassSweepFibreReductionHypothesis`
(`MachineSweepConsequences.lean`, lines 1069 and 1190) the machine occurs only in the antecedent
`TransposesWithin`. The existential body (Δ, δ, ε, M_cls, B_adv, p, E, f, Q, C) does not mention the machine, and
it is refuted outright by `growingClassesPositiveDeficit` (respectively by the half-barrier hypothesis). So each
hypothesis is logically equivalent to "no linear-time transposer", and the theorem is "if there is no transposer
then there is no transposer". The paper's phrase "whose pigeonhole fibre C_d" (`sweep.tex`, line 129) suggests a
tie to the machine that the definition does not have.

**Fix.** Either tie f, Q and C to the machine's run (for example through `evalConeTree`), or present the statement
as a restatement and not as a reduction. Rename `TapeCodingConjectureNegationSpec`: it states ¬(T), which is not
the Tape Coding Conjecture of the first paper.

### A5. Three Lean statements about cut cones are satisfied by a one-element footprint

The conclusions of `TMTraceCutConeDeterminationSpec` part 2 (`NativeSweepInterface.lean`, lines 170–175),
`Diagnosis_TCPAndAdaptiveConeReductionSpec` part 2 (`DiagnosisAndBarriers.lean`, lines 214–229) and
`tmWholeCellCutConeBound` (`DiagnosisAndBridgesConsequences.lean`, lines 54–69) have the form
"∃ Q_bit of at most (k+1)^D entries such that X₁, X₂ ∈ C agreeing on Q_bit agree at (c, r)". The footprint
Q_bit = {(c, r)} satisfies this for every C. The proofs do go through the real cone, but the propositions do not
record it. Lemma 8.1 and Proposition 2.4(b) of the paper rest on these statements.

**Fix.** Require (c, r) ∉ Q_bit, or state that Q_bit is the set of input cells read in the cut cone.

Related: `PeriodicSweepInducesBoundedAritySharedCodeSpec` is a definitional unfolding (the fields of
`PeriodicCutConeSweep` are the conclusion; the proof is one line). The README sentence "a q-state machine induces
bounded-arity shared cones directly on nonlinear cut fibres" has no proved counterpart.

### A6. Theorem 7.1(a): the displayed formula is not the one that is proved

`paper/sections/swapcodes.tex`, line 32, defines the code as {X : Σ A_t X B_t = Xᵀ}. The Lean definition
(`P17/lean/SwapRigidity/Flag.lean`) and paper 17 use Xᵀ = Σ A_t X B_tᵀ. For this family B_tᵀ = −B_t, so the
printed equation has the opposite sign: Σ A_t X B_t = −Xᵀ + tr-terms, and in characteristic ≠ 2 the printed code
has dimension 0 at d = 3 and 8 at d = 6, not 8 and 24. The outline below the theorem computes the correct
expression. The same slip is in `introduction.tex`, lines 149 and 254.

**Fix.** Write Σ A_t X B_tᵀ.

### A7. Remark 5.6 of paper 17 is misdescribed

- Claimed: "we disprove the d(d+1)/2 pairing bound for three-term swap codes asked in [Remark 5.6]"
  (`abstract.tex`, lines 42–44); "does Σ A_ℓ X B_ℓ = Xᵀ obey dim S ≤ d(d+1)/2? — No" (`introduction.tex`,
  lines 149–150); root `README.md`: "disproof … for d ≥ 5".
- The remark (`P17/paper/sections/order.tex`, "Two is sharp") already states "Three terms can exceed the pairing
  value", with 8 > 6 at d = 3 and 11 > 10 at d = 4, and ends "We have no three-term example for d ≥ 5."
- What paper 20 adds: examples at d = 6, 7, 9, 12, and a proof over every field of the d = 4 example. The family
  gives 4m(m+1) + t(t+1)/2 + 2mt at d = 3m + t, which is below or equal to d(d+1)/2 for every other d ≥ 5
  (35 < 36 at d = 8, 55 = 55 at d = 10, 63 < 66 at d = 11, equality at d = 15, smaller for m ≥ 6). So every
  d ≥ 5 outside {6, 7, 9, 12} is open, not only d = 5.

**Fix.** "We give three-term examples above the pairing value at d = 6, 7, 9 and 12; for the other d ≥ 5 the
question of Remark 5.6 stays open."

### A8. Theorem 6.6 of paper 19 is misdescribed

- Claimed: "that bound yields only d − o(d) rank and collapses once M₁ grows as slowly as log log d"
  (`introduction.tex`, lines 103–105); "the sub-iterated-logarithmic o(d) bound" (lines 232–233).
- `P19/paper/sections/composition.tex`, Theorem 6.6: "r ≥ bk(d − N₀ + 1)/2 … For fixed class bounds, r/(bd) → ∞".
  The bound is b·d times a slowly growing factor. It is neither o(d) nor d − o(d).
- Paper 19 says that it uses no numerical estimate for the van der Waerden numbers. The collapse point "log log d"
  has no source there and no Lean counterpart here.
- "Hales–Jewett numbers grow faster than primitive-recursively" is not right as far as we know (Shelah's bounds
  are primitive recursive). Not checked against a source.

The README states the bound of paper 19 correctly (r/(bd) ≥ W⁻¹/4); the paper should do the same.

### A9. The Harvey–van der Hoeven consequence is overstated

`introduction.tex`, lines 12–14: "a negative answer to the O(L)-time question implies Ω(n log n) integer
multiplication". The reduction gives only: no linear-time transposer implies no linear-time multiplier. The same
sentence calls the Tape Coding Conjecture a "time-space trade-off form" of (T); Conjecture 9.1 of the first paper
is about causal codes on block networks.

### A10. Problems 9.1, 9.4 and 9.5 of paper 17 are not resolved, and two are misquoted

- Problem 9.5 asks for a quantity that is subadditive over the steps of a machine, large for the swap at every
  scale, and "not raised at all scales by a single linear-time operation". Operator Schmidt rank fails the last
  requirement by this paper's own Propositions 6.6(a) and 6.7(a): the linear-time row shear has rank d.
- Problem 9.4(a) asks for a version of Theorem TP for cone systems of oblivious schedules with a bound
  r(ε) ≤ 1/2 + C(ε + η); 9.4(b) asks for the half bound at windows w ≥ 3 over a fixed alphabet. The paper proves
  neither. Its dichotomy `OneClassBoundedArityHalfBarrierQuestion` is over the alphabet of ⌈log₂ d⌉-bit words,
  which grows with d; Problem 9.4(b) fixes the alphabet.
- Problem 9.1 is about the capacity of partitions with no almost-period. It says nothing about anti-diagonals
  (`introduction.tex`, lines 109–111).
- The table header "Kernel-verified resolution in this paper" (`introduction.tex`, line 135) is wrong for the
  rows on Problems 9.1, 9.4 and 9.5.

### A11. Smaller mismatches

- Theorem 7.4(c) (`swapcodes.tex`, lines 169–170) states profile M(j) = 1; the Lean theorem
  (`SwapCodeAnswersProofs.lean`, line 1380) proves profile 2.
- `introduction.tex`, line 26: "Codes without machines" is in Section 4.2 of paper 17, not 4.4.
- Proposition 3.8(b) (`capacity.tex`, lines 246–247) has "=" where Lean has "≥".
- Proposition 6.6(a) says "3-work-tape"; the Lean statement gives no tape count for the shuffle.
- Proposition 4.1(b) passes from a dense 3-AP-free set to colourings; only the set is in Lean.
- `verification.tex`, lines 22–24, mentions local `maxHeartbeats` settings; there are none.
- Example 5.8: the text has b = 2, M₂ = 1 and calls dimension 24 "full"; the Lean docstring has M₂ = 2, q = 4.

## B. Overstatements

- **B1.** "breaks through all three walls simultaneously", "builds the native transition-table bridge"
  (`introduction.tex`, lines 120–125); the walls "are gone" (`sweep.tex`, lines 113–115); "thresholds to which the
  series now reduces (T)" (`abstract.tex`). No theorem reduces (T) to the listed targets; see A2–A4.
- **B2.** Problem 9.3 "resolved" with an "exact" bound. Theorem 7.3 is Theorem TP of paper 17 applied to the
  common refinement of the interval endpoints, on one side at a time. It is a correct and useful observation
  (the literal problem has the bound (d² + 2d·Σ M_j)/2), but there is no matching lower bound, and at the full
  profile β = 4d − 4 > d, so the bound is vacuous there.
- **B3.** The pass bound t ≥ log₂ d (Theorem 6.5) is for products of the exact Stone shuffle or unshuffle with
  operators of the form I ⊗ B and A ⊗ I. "Row-local, column-local" (`introduction.tex`, line 246) reads as more.
  It is not a statement about machines, and it stops at the row shear.
- **B4.** Theorem 4.4 replaces the method of paper 19, not its result at small parameters: at M₁ = M₂ = 2 it gives
  d ≤ 256 where paper 19 has d ≤ 16.
- **B5.** Theorem 5.6 holds for d ≥ D₀ with D₀ about (16 M₁ M₂)^(36^(2M₂−1)), roughly 2·10⁴³ for M₁ = M₂ = 1. The
  paper should print the threshold next to the theorem.
- **B6.** "Genuinely sharp" for the cube lemma: Example 4.5 shows 9 ≤ max ≤ 10 at one instance.
- **B7.** "Realizing the single-shift 5/8 floor": paper 19's 5/8 is a floor for nested multi-shift certificates;
  the value appears here through a hypothesis on the component count.
- **B8.** "Reunites bounded read arity with decoder sharing": Section 6.7 of paper 17 defines one-class relations
  of window w, and Problem 9.4(b) poses this combination.
- **B9.** "A two-pass machine induces a composition of two shared stages" (`introduction.tex`, line 100) has no
  support; paper 19 says the opposite about what it proves (`P19/paper/sections/open.tex`).

## C. The README against what survived

- **Scripts.** `test_cube_doubling.py`, `check_norm.py`, `verify_all_claims.py` and `test_band_randomJ.py` are
  named as evidence and exist nowhere in the repository. The numerical controls were replaced by exact Lean
  witnesses, which is better; the README should say so and drop the script names and the error figures.
- **"Wall 1 collapses unconditionally", "Walls 2 and 3 crack open", "Proved & Stress-Tested".** See A1–A4, A10.
- **The d = 4 coded factorization** holds over fields with 5 ≠ 0, not "every field".
- **"Tight" t ≥ log₂ d.** No theorem that m shuffles compose to the swap is in Lean.
- **"Admits exact solutions when k exceeds the Kővári–Sós–Turán scale"** became one instance (d = 12, k = 2).
- **Attack on Δ = O(1) and on rank error ε·b·d²** (Blueprint Parts I and II): not done; they are open
  propositions.
- **Naming.** The README uses (T) for the impossibility statement; the series uses (T) for the question or for
  linear-time transposability.
- The README has no build instructions (the repository's `CONTRIBUTING.md` asks for them).
- The seven specification files still carry the header "Formal Claim Specifications (No Proofs Yet)".
- `PaperAxioms.lean` runs `#print axioms` on the `...Spec` definitions, including the open ones. That says nothing
  about proofs; it should list the theorems.

## D. What is correct and worth keeping

- **Theorem 4.4 (2A) and Lemma 4.2.** A two-stage exact factorization of the swap by class-uniform linear maps
  forces d ≤ max(8M₁M₂², (2M₁)^(2^M₂)), over every field, with the Cauchy–Schwarz extraction proved.
- **Theorem 5.6 (2B).** rank(τ − K₂K₁) ≥ c·b·d·(log d)^(1/(2M₂−1)) when the characteristic does not divide d,
  with the Kővári–Sós–Turán extraction proved and an explicit constant. This improves the growth rate of
  Theorem 6.6 of paper 19 for large d.
- **Three-term examples** at d = 6, 7, 9, 12 and the d = 4 example over every field.
- **Linear-time machines** for one Stone shuffle, one unshuffle and the row shear, as transition tables.
- **`evalConeTree_traceConeTree_eq`.** On a frozen cut fibre the symbolic cone tree evaluated through the
  transition function reproduces the run.
- **Theorem 7.3** as a remark on Problem 9.3 (see B2).
- **Theorem 3.4** as a formalized weaker form of a known bound (see A1).

None of these touches the wall of paper 17: the two-stage theorems are about linear maps on the same space with
boundedly many classes, which no machine is known to supply.

## E. Not checked

- Proof files line by line; sibling libraries; Mathlib and toolchain integrity.
- Whether `HasOddGirthLinearSeed` is satisfiable.
- External facts quoted from memory (Shelah's bounds; bibliographic data of external references).
- Whether the acyclic-subgraph bound is Lean-verified elsewhere in the series, which bears on "first
  Lean-verified bound below 1 at Δ ≥ 2".
- The PDF.

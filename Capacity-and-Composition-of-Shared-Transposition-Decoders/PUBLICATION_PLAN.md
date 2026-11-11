# Publishing plan

Status: released November 2026 after the completed reviews. The explicit
formalization exceptions below remain part of the published proof-status record.

The papers share a question, not a model: native adaptive executions in the first paper;
complete cyclic shared-decoder maps and linear correctness sources in the second.
Neither paper proves or disproves unrestricted linear-time tape transposition.
The manuscript must distinguish a theorem proved in Lean, a theorem with a precisely
identified formalization gap, and a complete written proof awaiting formalization.
An arithmetic consequence of an assumed structural inequality is not formalization
of the structural theorem. Every status in the README must match the actual declarations.

## Completed release checklist

1. Freeze the included theorem statements and map every numbered result to its proof.
2. Reuse sibling packages and Mathlib, with pinned dependencies; formalize every result
   whose missing infrastructure is not a substantial, potentially weeks-long project.
   Give every deferred item a concrete missing bridge and dependency, not just “future work.”
3. Check strengthenings, hypotheses, proof simplification and duplicated code.
4. Obtain independent English/Lean and proof/citation reviews; resolve their findings.
5. Generate the declaration index and axiom checks; build Lean and the PDF; inspect the PDF;
   check relative paths and publication metadata.
6. Review the inventory coverage table before release so no relevant substantial result
   is lost merely because an earlier section was easier to write.

## Narrative and inclusion

| Placement | Result family | Role |
|---|---|---|
| Part I: capacity | Deterministic translate pigeonhole; invariant-ambient iteration; universal two-class 41/64 ceiling | Main quantitative strengthening of the one-stage algebraic obstruction, with all fields and coupled lanes. |
| Part I: many classes | Difference-cover bound with inverse-square-root class dependence for M ≤ d/2 | Controls growing class counts, with explicit saturation. |
| Part I: constructions | Same-class cyclic lifting; fixed-two-class excess; paid two-work-tape realization | Distinguishes abstract code capacity from a paid native implementation, and additive excess from a positive limiting rate excess. |
| Part I: structure | Lossless covariance-space completion; parity-qualified deterministic interval attainment | Simplifies future capacity searches and identifies exact attainments. |
| Part I: boundaries/appendix | Nonlinear source and decoder boundaries; field-closure and symmetric-subspace retention bounds | Makes indispensable hypotheses and measured structural deficits explicit. |
| Part II: composition | Common-message progression; exact two-linear-stage obstruction; one-global-error rank bound | Explains why a one-stage code construction does not automatically compose to full transposition. |
| Part II: nonlinear | Uniform sandwich, distance from equivariance, balanced-intertwiner and literal-period/subgroup obstructions | Gives nonlinear mechanisms with their precise architecture restrictions. |
| Appendix/application | Anchored neighboring-bit map and reviewed masked-family strengthening | Tests the nonlinear tools on a complete first factor, without claiming unrestricted two-hop impossibility. |

The revised seventeenth paper (ac70dc4) already provides unbounded additive
excess at every fixed class count over every field, including the binary field.
It extends the memo's parity-coset rule and combines different seed codes in a
blow-up. Our distinct content is the general same-class seed lift, exact periodic
capacity reduction, full-kernel dimension and paid realization of the exhibited
binary rule. All these families have vanishing normalized excess; do not claim
novelty for fixed-class or binary additive excess alone. A nonlinear-vs-linear subcode gap for one chosen source
is not a gap between the maximum achievable capacities.

## Completed strengthening pass

- Review the family of binary masked-neighbor maps: invertibility, literal mask periods,
  the image of the fixed-column subspace, and the balanced-intertwiner criterion.
- Seek a uniform theorem or a precise countercontrol, rather than an unbounded finite census.
- Recheck the single-site endpoint argument independently before using it.
- Compare any new result with the anchored theorem and subgroup theorem; eliminate weaker
  duplicate statements and give only the strongest supported formulation.
- Record the result, limitations and evidence in `verification/strengthening-review.md`.
  The record and both independent reviews are now complete. Failure to solve
  the general family is not a reason to postpone the established results indefinitely.

## Formalization order

Shared model → deterministic covariance/TP → invariant-ambient and class-count lemmas;
common-message growth → finite Ramsey extraction → two-hop bridge;
complete-map covariance → sandwich/period/subgroup proofs → finite orbit/balance argument.
Cyclic run averages, finite concentration, orbit counting, Fourier rank extraction and
residual accounting are now checked. The native two-tape schedule compiler remains
the sole numbered written-only result and the substantial formalization exception.

## Formalization checkpoint

The original manuscript passed its full algebraic build, axiom audit and reviews.
The integration below extends that checkpoint: all ordinary numbered mathematical
proofs are now complete. The native compiler remains written-only. Current per-theorem status,
README and verification/integration.md supersede the earlier module/page counts.
The completed reviews support release with the stated native formalization exception.

## Remaining result integration todos

Inventory reconciliation, 10 November 2026. All eight packages below are now represented in focused appendices. A checked
box records manuscript integration, not complete Lean formalization. The README
and each theorem identify the precise remaining proof work. Optional diagnostics
not needed for the narrative remain recorded in verification/integration.md.

- [x] **B1. Exact capacity beyond linear sources.** Give the exact one-class
  cyclic orbit formula and an attaining total decoder for arbitrary
  correctness sets. Include the prime-dimension formula
  [q^(d²)+(d−2)q^d+q]/d and the all-dimension logarithmic deficit
  log_q d+o(1). Add the zero-padded line constructions, deterministic
  line/interval bounds on linear sources, and actual joint-intersection
  hypotheses for affine sources. The line construction is not asserted
  optimal. Explain why a high-entropy arbitrary fibre cannot replace a
  high-dimensional linear source.

- [x] **B2. Diagonal block defects and the exact exhibited kernel.** State
  the unequal-block refinement
  dim ker(τ−K) ≤ Σ_(i<j) s_i s_j + Σ_j dim ker(τ_(s_j)−K_j)
  for actual diagonal compressions and compatible tensor bases. Reuse
  descending elimination from periodic capacity. Separately certify the
  actual binary seed operator's full nullity 25, then show the paid lifted
  operator's entire agreement kernel has dimension b(d²/2+7d/6) at its
  admitted dimensions. The paper proves the full kernel equality in Lean; it does not
  assert optimality over seed rules. Check the finite rank certificate in Lean.

- [x] **B3. Specialized bounds and limits of certificate methods.** Prioritize
  the precisely defined numerical certificate classes: nested component
  bounds have an almost-every-mask 5/8−o(1) floor; full-starting-ambient
  isolated-row bounds have a 9/16−o(1) floor; and the direct many-class
  guarantee has matching inverse-square-root order in its random-partition
  regime. Include the structured digit-parity 9/16 bound and random-mask
  41473/65536 improvement as applications. The finite 2/3 alternative is
  a lower-priority corollary. Check any extension of original scalar
  statements to mixed lanes. Probabilities concern partitions; the floors
  limit specified proof methods, not actual code capacity or native machines.

- [x] **B4. Extension-linear residuals with linear decoders.** Before the
  scalar-closure appendix, state the sharper binary scalar theorem under
  E=F_(2^d) linearity of the actual residual C∩ker Π in the fixed reversed
  normal-basis coordinates. For active support size a and class counts a_J,
  prove D ≤ Md+d(a−max_J a_J); for two classes,
  D ≤ d(1+min(|J₀|,|J₁|)) ≤ (d²+2d)/2.
  Include one-class vanishing. Decoder linearity is binary, not necessarily
  E-linear. Retain scalar width unless a broader statement is separately
  proved. The current nonlinear-decoder 3/5 theorem does not subsume this.

- [x] **B5. All-width reflection barrier to linearization.** Add the binary
  construction for odd prime d=2m+1 and every width b: source dimension bdm,
  but every linearly decoded subcode for the same singleton/rest partition
  has dimension at most b[m(m+1)+d], even with lane mixing. Its asymptotic
  quarter-volume deletion includes bit and canonical widths; the existing
  above-half mixture uses suitable enlarged widths. Retain the prime
  hypothesis for the disjoint-view source construction; the formal linear-subcode
  upper bound holds in every odd dimension. The completion-induced mixed-quotient/demand-map isomorphism
  and triple example's small relation-map rank are optional supporting
  additions if they justify their definitions. No maximum-capacity gap follows.

- [x] **B6. A complete first factor and its compositional failure.** Pair the
  total bijective singleton/rest extension of the scattered normal-basis
  source with its remaining-factor obstruction. For every binary d≥2 and
  b≥1, construct the entire first map by equivariant orbit completion and a
  column-zero involution; for d≥3, the required second map needs d singleton
  classes. Prove the sparse input-state disagreement and reuse the current
  agreement bound. Add the even-dimension two/one-class endpoint-class
  blowup control. A cheap orbit evaluator is not supplied. Any clean-register
  corollary must retain trivial register symmetry, fixed initial/final
  values and global injectivity of the complete enlarged postprocessor.

- [x] **B7. Balance tests without transitivity.** Extend balanced intertwiners
  to invariant scalar-word actions whose nontrivial orbit sizes are divisible
  by a prime p coprime to alphabet size a. With t fixed scalar words, balanced
  fibres force t^(db) ≥ a^(db) (a^[db(d−1)] mod p).
  Include the semiregular cyclic consequence and the actual nontransitive
  order-five example. Reuse stabilizer indices without assuming tuple
  transitivity. The multiplier getter-degree and covariant, surjective but
  unbalanced F₈ examples are useful scope checks. A feasible orbit assignment
  for one class function does not supply a jointly bijective complete map.

- [x] **B8. Nonlinear corrections to an exhibited affine baseline.** Add a
  compact construction-boundary appendix. For a complete global-affine
  initialization, every unmarked map and final readout, prove that fixing
  the joint residual tuple leaves the same linear part K₀. Derive
  |C| ≤ |Z(C)| Q^D with D=dim ker(τ−K₀), the joint propagated-output-span
  refinement and exact sparse-support menu. Pay all retained state and
  input-dependent branches/schemas. Apply operator bounds only to an exhibited
  complete baseline. Sharp separable-rank and nonlinear row-then-column
  agreement bounds are suitable short examples. Credit the reused affine
  replay; do not infer a cheap baseline for arbitrary native computations
  or a running-time charge from correction rank alone.

Suggested order: B1 and B2 establish exact source/construction boundaries;
B4 and B5 complete the linearity distinctions; B6 and B7 strengthen
composition; B3 explains the capacity program's methodological limits; B8
provides a scoped operational application. Reuse current Lean machinery,
consolidate proofs and review each new statement before changing its status.

Keep generic two-work-tape scheduling, entry-expander implementations,
output-only transport classification, complete-program affine normalization
and graph/Tanner storage-code barriers in separate follow-ups. An example
included here needs its own public proof or a published reference.
Solver timeouts, duplicate controls and numerical checks are not new theorems.

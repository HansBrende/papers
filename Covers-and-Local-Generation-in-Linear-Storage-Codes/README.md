# Covers and Local Generation in Linear Storage Codes

Hans Brende and GPT-6 Astra (OpenAI), October 2026.

[Paper and LaTeX sources](paper/) ([PDF](paper/main.pdf), [CC BY 4.0](paper/LICENSE)).
[Lean library](lean/) ([Apache 2.0](lean/LICENSE)).

## The question

What structure must an above-half linear storage code have, and which such
codes could contribute to a coding approach to linear-time matrix transposition?
This companion treats finite Clebsch covers, asymptotic group-cover models,
and, separately, local generation.
It does not supply their hypotheses for arbitrary native tape computations.

## What is proved

The following are formalized in Lean, reusing Mathlib through `lean-machine`:

- **Exact homogenization:** an explicit coordinate permutation identifies the
  inflated check with independent copies of the original sheet-dependent check.
  Its kernel dimension is multiplied by the sheet count, preserving normalized
  nullity. This includes nonabelian sheet groups, repeated voltages, and zero
  coefficients.
- **Local-generation algebra:** the kernel-range dimension bound, its quotient
  deficit, and the sufficient condition that every chosen generator has the
  form `s + A s`. The graph hypotheses supplying that condition are not formalized.

Their axiom audits permit only `propext`, `Classical.choice`, and `Quot.sound`.
The following results have complete written proofs and are explicitly marked
**not formalized**:

- **Sharp finite Clebsch covers:** the prescribed binary adjacency code has
  dimension at most `N/2 + 2` on connected binary towers, with an
  equality/rigidity versus permanent-at-most-half dichotomy. The bound extends
  to regular deck groups `P × D` (a finite 2-group and odd abelian group) and
  `P × S₃`. It is sharp at every cyclic degree. Three-sheet covers have
  dimension at most 26; a named rigid seed supports further binary towers.
- **Reciprocal-block rigidity:** at block width `r`, the Clebsch check has rank
  at least `6r`, equality exactly for flat gains, and no rank `6r + 1`.
  Exact two-edge and minimum-pair-block identities are paired with the actual
  width-five counterexample to their unrestricted extension. These statements
  do not bound arbitrary recovery codes on a cover.
- **Fixed-width half rate:** for a fixed separated free-group voltage template
  and the specified ambient pro-p chain, one eventual bound works for all
  characteristic-p fields and homogeneous coefficient tuples.
- **Growing-width obstruction:** a sustained excess of delta above half rate
  requires at least 2 delta of the dimension in simple coefficient factors
  exceeding every fixed size, after algebraic closure.
- **Uniform rate zero:** independent-chord covers of a fixed graph with a
  spanning 2-factor have vanishing normalized kernel dimension for nonzero
  scalar edge checks, or arbitrary-width invertible edge blocks with a common
  full flag (also preserved by the diagonal blocks).
- **The limit of homogenization:** the formal construction above can acquire
  one large absolutely simple coefficient module. Small-factor mass does not
  follow automatically. The explicit example and its simplicity proof are written.
- **Local generation:** in characteristic two and odd girth greater than 2R+1,
  the dimension of a code plus the dimension spanned by its radius-R codewords
  is at most the sum of its attained coordinate dimensions.
- **Nonlinear local sources:** if the entire affine hull of a Cartesian-source
  encoder is recoverable, exceptional sources pay for excess support size and
  entropy. All-local sources force the hull to be locally generated and obey
  the weighted half bound. Recovery merely on the image is insufficient.
- **Growing group alphabets:** ordinary group-word recovery inherits the cover
  half and zero-rate bounds when its exponent matrix modulo p meets the respective
  homogeneous scalar hypotheses. The finite p-group alphabet can grow freely;
  arbitrary endomorphic expressions are not included in this scalar application.

The rank-approximation input is Jaikin-Zapirain–Souza, Theorem 8.1; its chain
hypotheses are retained. A separate finite-type parameter proof supplies uniformity.
The bibliography identifies the classical algebraic inputs, related storage-code
constructions, and earlier papers at pinned revisions. External priority for
the combinations of results has not been established.

## What is open

The `N/2 + 2` adjacency-code bound for arbitrary connected Clebsch permutation
covers remains open here. Arbitrary growing block width, unrestricted nonlinear codes, and a paid native
representation remain open. Large simple factors are necessary for an excess
within the cover setting, but are not sufficient. Recovery locality does not
imply local generation. No unrestricted transposition time bound is claimed.

## Formalization todos

These tasks cover the remaining written results; they are not assumed axioms
in the Lean library. Complete the finite interfaces before attempting the
asymptotic cover theorems, and reuse the dependencies below.

1. **Finish local generation and its nonlocal-dimension corollary.** Extend
   [`LinearRecovery.lean`](../lean-machine/LeanMachine/LinearRecovery.lean) from
   scalar/equal-width coordinates to the varying attained spaces. Prove that
   odd girth makes every radius-R ball bipartite by distance parity, including
   the cancellation in every boundary row. Feed the resulting splits into the
   checked dimension interface; then formalize the normalized limiting corollary.
   Reuse Mathlib's graph walks and our [`GraphBall.lean`](../lean-machine/LeanMachine/GraphBall.lean).
2. **Finite-cover certificates.** Formalize voltage lifts, subgroup separation
   by finite Schreier-graph completion, the weighted component-order rank
   witness, and the implication from long paired distances to infinite
   separation. Reuse [`ColorOrder.lean`](../lean-machine/LeanMachine/ColorOrder.lean)
   and the directed-recovery paper's
   [`IncidenceComponents.lean`](../Directed-Recovery-Structures-in-Tape-Computations/lean/DirectedRecovery/IncidenceComponents.lean);
   the group-cover and weighted rank connections still need proofs.
3. **Filtrations and field uniformity.** Prove the finite filtered-kernel
   inequality and the trivial-factor flag for a finite p-group in characteristic
   p; derive refinement monotonicity. Then formalize the bad-minor ideals and
   finite unit identity. Mathlib already supplies Zariski's lemma as
   `finite_of_finite_type_of_isJacobsonRing` in `Mathlib.RingTheory.Jacobson.Ring`;
   use it for finite residue fields instead of reproving Nullstellensatz.
4. **Imported rank approximation and fixed-width half rate.** The free-group
   inner-rank/division-ring identification and Jaikin-Zapirain-Souza Theorem 8.1
   remain substantial external formalization dependencies. Preserve the exact
   ambient embedding, chain, action convention, and normalization when importing
   or formalizing them. Combine these with items 2-3 and restriction of scalars.
5. **Growing-width results.** Formalize the typed invariant subquotients after
   algebraic closure, the factor-mass inequality, tightness/excess limits, and
   the common-flag corollary. Reuse Mathlib's finite-dimensional, composition-series,
   and filter-limit machinery; do not substitute a growing cutoff into a
   fixed-cutoff threshold. Include the prime-field/geometric-factor comparison.
6. **Weighted rate zero.** Formalize the unique determinant monomial from an
   oriented spanning 2-factor and the tree-current argument, then restriction
   of scalars over rational-function fields. Items 3-4 supply the scalar limit;
   the filtered-kernel bound supplies its common-flag extension. Check the
   one-edge example showing why nonzero weights are required.
7. **Homogenization's algebraic obstruction.** The check conjugacy and rate
   identity are complete. Formalize the explicit cyclic-chain example, its
   full matrix algebra over every field extension, and its separate all-code
   half bound. The extension from whole kernels to arbitrary subcodes by
   independent products is also still a written corollary.
8. **Source and group-word applications.** Formalize the Cartesian-fibre
   telescoping argument and quotient/support/entropy payments, retaining recovery
   on the full affine hull. For ordinary words, specialize the directed-recovery
   paper's central-layer argument to scalar exponent maps and combine it with
   the cover bounds. These applications retain the unformalized dependencies
   of items 1 and 4-6; a checked final inequality alone would not complete them.

9. **Finite Clebsch covers and rigidity.** Reuse the fourth paper's formalized
   Clebsch graph, check, and rank-six theorem. Formalize the binary-lift kernel
   exact sequence and rank-two rigidity propagation, then the reciprocal
   Schur identities, symplectic plane argument, and character/module splits.
   The seed's exact certificate below is checked in Python, not Lean; port
   its literal matrix-inverse identity rather than trusting the checker.

## Building and verifying

Clone the whole repository, preserving the sibling `lean-machine` directory.
Lean and Mathlib remain pinned to v4.34.1. From `lean/`:

```sh
lake exe cache get
lake build
lake env lean PaperAxioms.lean
```

From this paper directory, regenerate the index and axiom checks:

```sh
python3 tools/lean_index.py
```

From `paper/`, build the manuscript:

```sh
latexmk -pdf main.tex
```

Check the exact finite seed witness with:

```sh
python3 tools/check_clebsch_seed.py
```

The certificate records an explicit kernel basis and a 73-square signing
minor with its inverse. The standard-library checker reconstructs the graph
and verifies exact binary identities. It is not a Lean formalization.

The local `.lake/` cache is ignored. The proof-status labels distinguish the
verified algebra from the remaining graph and asymptotic proofs.

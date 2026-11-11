# Capacity and Composition of Shared Transposition Decoders

Hans Brende and GPT-6 Astra (OpenAI) · November 2026 · **Working draft**

[Paper PDF](paper/main.pdf) · [LaTeX](paper/) (CC BY 4.0) · [Lean](lean/)
(Apache 2.0) · [Publishing plan](PUBLICATION_PLAN.md)

## The question

How large can a correctness source be when a decoder sees a cyclic rotation of
the complete matrix and its receiver class? Which complete rules can compose to
transpose every input? Applying these algebraic answers to a tape machine still
requires a paid implementation or a proved reduction.

## Results and their role

The core capacity results include a deterministic two-class ceiling of
`41/64 + 5/(3√d)`, an inverse-square-root deficit for `M ≤ d/2` classes, and cyclic
lifts preserving a fixed class count. Complete linear composition, quantitative
rank loss, nonlinear balance and period obstructions impose separate conditions.
The formal two-class linear composition bound is `d ≤ 16`. Its sharper
progression bound uses `gcd(d,s)`; a monochromatic progression of length
`M₂+1` and step coprime to `d` forces `d ≤ M₂²`.

All eight integration packages are now included:

| Package | Addition | Proof status |
|---|---|---|
| B1 | Exact arbitrary-set cyclic capacity; line markers; deterministic linear and qualified affine line bounds | Lean, including exact cyclic orbits, all-dimension limits and line markers |
| B2 | Unequal-block diagonal defects; full agreement kernel of the displayed seed and cyclic lift | Lean, including all independent binary lanes and a kernel-checked seed certificate |
| B3 | Structured/random mask bounds; floors for specified certificate methods | Lean, including actual graph counts, finite probability, conditioning and method floors |
| B4 | Extension-linear actual residual with binary-linear decoders | Lean, including one- and two-class consequences |
| B5 | Every-width prime reflection source and linear-subcode barrier | Lean; the binary linear-subcode barrier is strengthened to every odd dimension |
| B6 | Complete scattered first factor and remaining-factor obstruction; endpoint blowup | Lean |
| B7 | Nontransitive orbit-divisor balance tests and an actual order-five example; multiplier and orbit-assignment diagnostics | Lean, including literal multiplier classes, ratio fibres and exact orbit-assignment balance |
| B8 | Complete affine-baseline replay; joint residual/support/span accounting | Lean, including chronological replay, joint entropy, exact sparse menus and sharp baseline examples |

Paper 17 at revision `ac70dc4` already gives fixed-class excess over every field,
including binary fields; that existence claim is credited there. Our arbitrary-seed
cyclic lift, exact periodic capacity and full agreement kernel retain their separate
content. Its entry-change and advice bounds do not subsume the other packages.
The generic fixed-advice counting argument is credited as prior work; B8 applies
it to complete chronological records and their actual propagated spans.
See [the crosscheck and integration record](verification/integration.md).

The exact arbitrary-set capacity prevents substituting high entropy for a linear
source. Method floors limit the specified certificates, not achievable code rate.
The exact lifted kernel concerns the displayed operator, not an optimal seed.
None of these statements decides unrestricted linear-time tape transposition.

## Formalization work and release gates

Each numbered result identifies its exact formal status. For a result marked
Lean, the formal statement and proof are authoritative; its English outline is a
guide. A partial label names the missing step. The permitted axioms are only
`propext`, `Classical.choice` and `Quot.sound`.

All numbered mathematical results are now formalized except the native
**two-work-tape implementation theorem**. Its written proof remains in the paper;
a full native transition table, execution and coordinate invariants, and uniform
time/state accounting are the substantial formalization todo. The algebraic
operator and its exact correctness-source dimension are already checked.

The completed work reuses the earlier entropy libraries, Mathlib's algebra and
Fourier infrastructure, and shared finite probability machinery in `lean-machine`.
The probability bounds are proved for actual finite random masks; no concentration
inequality or graph-counting assertion is taken as an axiom.

The previous [English–Lean](verification/english-lean-review.md),
[proof/citation](verification/proof-citation-review.md) and
[strengthening](verification/strengthening-review.md) reviews cover the earlier
checkpoint. The current integration record identifies the newer checks and their
scope; old module/page counts are not evidence for later additions. Draft status
remains until the formalization and release requirements are met.
The subsequent [cleanup and strengthening review](verification/cleanup-review-2026-11-10.md)
records the gcd composition bound, attained-prefix class count, smaller
random-mask thresholds and corrected prose qualifications.

## Building and verifying

Clone the entire repository. Sibling packages are required by relative paths;
Lean and Mathlib are pinned to 4.34.1. From this directory:

```sh
python3 tools/seed_recovery_certificate.py
python3 tools/lean_index.py
cd lean
lake exe cache get
lake build
lake env lean PaperAxioms.lean
cd ../paper
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The finite certificate generator is optional for normal builds: its portable
output is included and rechecked by Lean. The declaration index and axiom audit
are generated from the manuscript. Local `.lake/` caches are not published.
A successful build does not certify any step marked written-only or partial.
The paper-local index generator uses the shared `../tools/lean_paper_index.py`.

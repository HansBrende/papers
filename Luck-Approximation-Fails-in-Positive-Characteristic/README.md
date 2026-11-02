# Lück Approximation Fails in Positive Characteristic

Hans Brende and Claude Opus 5.5 (Anthropic), November 2026.

- [`paper/`](paper/): the paper ([`main.pdf`](paper/main.pdf)) and its LaTeX sources. License: CC BY 4.0
  ([`paper/LICENSE`](paper/LICENSE)).
- [`lean/`](lean/): the Lean 4 formalization (Lean and Mathlib v4.34.1). License: Apache 2.0
  ([`lean/LICENSE`](lean/LICENSE)). It requires the shared library [`lean-machine`](../lean-machine/) by a relative path,
  so the sibling directories of this repository must be in place.
- [`tools/`](tools/):
  - [`lean_index.py`](tools/lean_index.py) generates the index of Lean declarations and `lean/PaperAxioms.lean` from the
    paper's LaTeX sources;
  - [`gen_operator.py`](tools/gen_operator.py) regenerates `ConData.lean`, `Data.lean` and `CertData.lean`: certificates
    and caches, which Lean checks, and two free choices, using [`icosian_graph.py`](tools/icosian_graph.py) and [`gf.py`](tools/gf.py);
  - [`lambda_level1.py`](tools/lambda_level1.py) and [`a5_checks.py`](tools/a5_checks.py) reproduce the numerical
    remarks and the finite group theory of the lemma on `A₅` acting on the projective line.

## The question

Jaikin-Zapirain's arbitrary-field form of the Lück approximation conjecture: for a group `G`, a field `K` and a matrix `A`
over `K[G]`, the normalized ranks `rk_{G/Gᵢ}(A) = dim_K Im(x ↦ xA on K[G/Gᵢ]ⁿ) / |G : Gᵢ|` converge along every chain
`G > G₁ > G₂ > ⋯` of normal subgroups of finite index with trivial intersection (part (1)), to a limit that does not depend
on the chain (part (2)). Over subfields of `ℂ` this is Lück's approximation theorem and its extensions.

## What is proved

For the free group `F` of rank 89 there is one 110 × 110 matrix `A` over `𝔽₃[F]`, the Tanner operator of the Goren–Oort
configuration of a Hilbert modular surface of `ℚ(√5)` in characteristic 3, such that:

- **Theorem P** (formalized). Over every field of characteristic 3, the normalized ranks of `A` tend to 110 along every
  chain with 3-group quotients that is cofinal in the pro-3 topology.
- **Theorem H** (proved in the paper, not formalized). Along the congruence chain `N_k` of an arithmetic lattice
  `F ≅ Γ⁺(λ₀)`, whose quotients `F/N_k` are 11-groups, `dim_𝔽₃ ker φ_{F/N_k}(A) ≥ 20 |F : N_k|` for every `k`. The proof uses Riemann–Roch
  on a compactified Hilbert modular surface in characteristic 3, partial Hasse invariants and the uniformization of the
  supersingular locus.
- **Theorem A** (formalized from an explicit hypothesis). Part (2) of the conjecture fails for `F` over every field of
  characteristic 3; in particular the
  arbitrary-field conjecture is false. Lean proves this from an explicit hypothesis, `Luck.Op.KernelNotNegligible`
  (along some chain the normalized kernel of `A` does not tend to 0), which Theorem H implies.

Formalized, with no axioms beyond `propext`, `Classical.choice` and `Quot.sound`:
- the statement of the conjecture (`Statement.lean`), with a second, independent formalization proved equivalent
  (`Literal.lean`) and semantic checks (`SemanticChecks.lean`);
- a criterion for the failure of part (2): a full-rank limit along one chain and a normalized kernel that does not tend
  to 0 along another (`Chains.lean`);
- a kernel-checked certificate, the kernel bound on all cyclic 3-power covers, monotonicity of ranks along `p`-group
  extensions, convergence of ranks along every chain with `p`-group quotients (part (1) along such chains), and Theorem P;
- Theorem A from the hypothesis, and its unconditional form: if part (2) holds for `F` over some field of
  characteristic 3, then the normalized kernel of `A` tends to 0 along every chain (`Main.lean`).

The Lean matrix is defined from the construction itself (`Construction.lean`): the 120 icosians by the standard
formula, their reductions modulo 3 and modulo `λ₀`, the labels, the quartic monomials and restriction of scalars.
Generated data enter only as a coset certificate and packed caches, both checked by the kernel (`ConChecks.lean`,
`ConCache.lean`), and as free choices of a spanning tree, checked to be one, and of a voltage; nothing in the proof trusts
them.

Proved in the paper but not formalized: Theorem H and the results used only in its proof, namely the lemmas of its
section and three lemmas of the construction section (the base graph as a quotient of the tree, the self-duality of the
local code, and the identification of the kernels of `A` with Tanner codes on covers). Remarks labelled as numerical, as
proof sketches or as heuristics are not used in any proof.

## What is open

A formal or elementary proof of Theorem H; whether part (2) fails in characteristic 2 and in every positive
characteristic; convergence along the congruence chain (part (1)); Jaikin-Zapirain's refined conjecture for virtually
pro-`p` completions; other free groups. See the open-problems section of the paper.

## Building and verifying

The Lean package requires [`lean-machine`](../lean-machine/) by a relative path. Clone the whole papers repository so that
the sibling directories stay in place. Install [elan](https://github.com/leanprover/elan), then in `lean/`:

```bash
lake exe cache get
```

```bash
lake build
```

A clean build takes about 45 seconds. Check the axioms of every declaration cited in the paper (generated from the
paper's LaTeX sources):

```bash
lake env lean PaperAxioms.lean
```

Every declaration should report at most the axioms `propext`, `Classical.choice` and `Quot.sound`. After editing the paper,
regenerate the index of Lean declarations and `lean/PaperAxioms.lean` (from this directory):

```bash
python3 tools/lean_index.py
```

Regenerate the certificates and caches (needs `numpy`; the output is identical to the committed files):

```bash
python3 tools/gen_operator.py
```

Reproduce the numerical remarks (`numpy` needed except for the last command): the first nested level of the congruence
chain for the twisted and the untwisted gluing, a random cover with seed `s` (here `s = 1`; the paper uses `s = 1, 2, 3`),
the base level, and the finite group theory of the lemma on `A₅` acting on the projective line:

```bash
python3 tools/lambda_level1.py
```

```bash
python3 tools/lambda_level1.py untw
```

```bash
python3 tools/lambda_level1.py random 1
```

```bash
python3 tools/icosian_graph.py 11 tw untw
```

```bash
python3 tools/a5_checks.py
```

To build the PDF, run `latexmk -pdf -interaction=nonstopmode main.tex` in `paper/`.

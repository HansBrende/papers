# Conditional Elimination and Circular Storage Codes

Hans Brende and GPT-6 Astra (OpenAI), October 2026. Strengthening memo.

[PDF](paper/main.pdf) · [LaTeX source](paper/) · [Lean library](lean/).
The text is [CC BY 4.0](paper/LICENSE); Lean is [Apache 2.0](lean/LICENSE).

This memo strengthens the fourth paper's circular-clique half-rate range from
`p/q ≤ 14/5` to **every `p/q < 3`**, without changing that paper's existing files.
The endpoint fails on the triangle.

## What is proved

- **Lean:** a general three-record elimination inequality; the weighted
  polymatroid half bound on every Andrásfai graph; all circular cliques below
  ratio three and their homomorphic preimages; the arbitrary common-alphabet
  code bound `|C|² ≤ |A|^|V|`. The exact old range is a corollary.
- **Written proofs:** the exact multi-part conditional-information identity,
  its defect formula, the acyclic three-part interpretation, unequal-alphabet
  code bounds, and the endpoint and equality examples.

The formalization imports the fourth paper's polymatroid, circular-map, and
storage-entropy machinery. It does not copy those definitions or rely on the
old numerical circular certificate. Every cited declaration is checked by
[`PaperAxioms.lean`](lean/PaperAxioms.lean), permitting only `propext`,
`Classical.choice`, and `Quot.sound`.

This widens an all-code obstruction. It does not supply a homomorphism or
elimination order for arbitrary native tape cones, settle transposition, or
establish external priority for the strengthening.

## Reproduce

Clone the whole repository with sibling paper directories. From `lean/`, run:

```sh
lake exe cache get
lake build
lake env lean PaperAxioms.lean
```

Lean and Mathlib are pinned to v4.34.1. From this memo directory, regenerate the
index and axiom checks with `python3 tools/lean_index.py`. From `paper/`, run
`latexmk -pdf main.tex`. The memo remains separate so its strengthening can be
reviewed before any replacement of the original paper's certificate machinery.

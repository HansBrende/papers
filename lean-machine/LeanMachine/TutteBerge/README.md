# Tutte–Berge

Matchings of finite simple graphs, building on Mathlib's Tutte theorem (`SimpleGraph.tutte`).
Mathlib v4.34.1 has no matching number and no Tutte–Berge formula.

| File | Origin | Main declarations |
|---|---|---|
| `Berge.lean` | external, see below | `BergeMatching.isMaximum_iff_not_exists_augmenting` (Berge 1957); `BergeMatching.two_mul_card_add_le` (the weak Tutte–Berge inequality); `BergeMatching.exists_tutte_berge` (the Tutte–Berge formula); `BergeMatching.oddCount` |
| `MatchingNumber.lean` | ours | `SimpleGraph.matchingNumber`; the Tutte–Berge formula for it; `SimpleGraph.componentBlocks` and its barrier identity; `SimpleGraph.Subgraph.IsMatching.exists_fin_enum` |

## Provenance of `Berge.lean`

- **Source:** <https://github.com/jtraverso/berge-matching>, file `BergeLib/Berge.lean`, at commit
  `f01d042c071c778fb3f432312356136a92369076` (2026-10-19, "Version 2").
- **SHA-256 of the original file:**
  `fca379ce0af6197f7c8919971f2df98f6fb352fec5d0f172e1714a8cb3209960`.
- **Author and copyright:** Juan Pablo Traverso Gianini, 2026, per the file header and the
  repository's README.
- **Licence:** Apache 2.0. The repository's `LICENSE` has the same text as
  [`lean-machine/LICENSE`](../../LICENSE).
- **Original target:** Lean v4.35.0-rc3 and Mathlib `c55e6e7`, using the module system.
- **Not copied:** `GallaiEdmondsLib/` (the Gallai–Edmonds structure theorem), and the registry's
  statement files `Challenge.lean` and `Solution.lean`.

Before porting, the file was read in full. It contains only definitions, lemmas and standard
tactics: no code that runs at build time, and no `sorry`, `admit`, `axiom` or `native_decide`.

## Changes to `Berge.lean`

1. Removed the module-system syntax: `module`, `@[expose] public section`, and `public`. The
   libraries in this repository do not use the module system.
2. Replaced `import Mathlib` by the four Mathlib modules the file needs (found with `#min_imports`):
   `Mathlib.Basic.Finite.Sum`, `Mathlib.Combinatorics.SimpleGraph.Tutte`,
   `Mathlib.Data.Fintype.Lattice` and `Mathlib.Order.CompletePartialOrder`.
3. Added a provenance comment below the copyright header.

There are no other changes. The statements, names and proofs compile unchanged on Lean and Mathlib
v4.34.1.

## Our additions (`MatchingNumber.lean`)

- `SimpleGraph.matchingNumber G`: `ν(G)`, the largest number of edges of a matching. It comes with
  `le_matchingNumber` and `exists_isMatching_ncard_eq_matchingNumber`.
- **The Tutte–Berge formula for `ν(G)`:**
  - `two_mul_matchingNumber_add_oddCount_le`: `2 ν(G) + odd(G − U) ≤ |V| + |U|` for every `U`;
  - `exists_two_mul_matchingNumber_add_oddCount_eq`: equality holds for some `U`.
- **The components of `G − U` as barrier blocks.** `componentBlocks G U` is the set of vertex sets
  of the components of `G − U`.
  - They cover the vertices outside `U`, are pairwise disjoint, and have no edges between them
    (`biUnion_componentBlocks`, `pairwiseDisjoint_componentBlocks`,
    `not_adj_of_mem_componentBlocks`).
  - `two_mul_sum_card_div_two_add_oddCount`: `2 ∑_B ⌊|B|/2⌋ + odd(G − U) = |V| − |U|`.
- **The barrier form:** every `U` has `|U| + ∑_B ⌊|B|/2⌋ ≥ ν(G)`
  (`matchingNumber_le_card_add_sum_card_div_two`), and some `U` attains it
  (`exists_card_add_sum_card_div_two_eq_matchingNumber`). This is the form that bounds of the shape `|U| + ∑_B ⌊|B|/2⌋` need;
  the matching form of Theorem S in the fourth paper is one.
- `Subgraph.IsMatching.exists_fin_enum`: the edges of a matching, listed as pairs `(u i, w i)`
  whose endpoints are all distinct.

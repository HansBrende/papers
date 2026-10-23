# Memo: the padding theorem needs no idle tapes

Hans Brende and Claude Opus 5.5 (Anthropic), October 2026.

A note on the padding theorem of this paper (Theorem *Universal fully paid padding*, `thm:padding` in
[`paper/sections/padding.tex`](../paper/sections/padding.tex), formally
`TransposeFollowup.PaidPadding.exists_uniform_paid_padding`). The Lean proofs are in [`lean/`](lean/)
(Apache 2.0, [`lean/LICENSE`](lean/LICENSE)). They build on this paper's library, which is
required through a relative path and not copied.

## The finding

The padding theorem gives every padded machine `E · max(1, size(g(M)))` idle work tapes: they stay
blank, with their heads at cell zero. The paper explains why they are there. They make the
head-count hypothesis `4q ≤ 3k(M')η` of the layout cut inequality hold, where:
- `q` bounds the degrees of the expanding overlap graphs;
- `k(M')` is the number of tapes;
- `η` is the vertex-expansion constant.

The proof gives each vertex window one label, discards up to `q` edges at every window that a
label change spoils, and pays for them with the term `3k(M')·r·G·B_λ` of the zero-slack cut
inequality (`eq:zero-cut`), where `B_λ` is the number of label changes. Idle tapes enlarge
`k(M')`, and so that term.

**Neither the idle tapes nor the head-count hypothesis is needed.** Count entry cells offset by
offset inside the windows instead of window by window:
- a fixed pair of offsets colours the vertices twice, once at each offset;
- a label change inside a window only changes the colours at the offsets it affects;
- an edge whose two ends get different colours at a matched pair of offsets is an entry cell.

Expansion of the bipartite double cover of the overlap graph yields enough such edges at every
offset pair, so no edge has to be discarded and no tape count enters. The same count also proves the
finer inequality that charges each tape only for the cells it actually inherits across a class
boundary (its *entry cells*), at every slot length up to `7K` times the layout's block size, not
only at the block size.

## What is proved (Lean, standard axioms only)

**Machine level.** `exists_uniform_paid_padding_without_idle_tapes` is the paper's padding theorem
with `E = 0`: the tape count `K₀ + (k(M) + E)·max(1, size(g(M)))` becomes
`K₀ + k(M)·max(1, size(g(M)))`, and every other clause (state count, three-bit cells, part (a) on
computations, part (b) with the full limit conclusion) is unchanged. It is derived from
`exists_uniform_paid_padding_cell`, which strengthens part (a): the padded machine's run satisfies
both the cell-accurate inequality and the first paper's zero-slack cut inequality at every slot
length from `1` to `7K⌈nb/3⌉`, not only at the block size `⌈nb/3⌉`. Here `n` is the matrix
dimension and `b` the entry width. The padded machine is the paper's own `PaidPayload.machine`,
that is, the construction without `StationaryTapes`.

**Layout level.**
- `cellCutIneq_of_layout`: every excursion layout satisfies the cell-accurate inequality, with zero
  slack, at every slot length `1 ≤ r' ≤ 7Kr`. Its hypotheses:
  - expansion `η` of the overlap graph;
  - stretch `(2K−1)η ≥ 1`, implied by the paper's `4 ≤ (4K−1)η` (`stretch_of_followup`);
  - `2n ≤ |V|`;
  - `nb ≤ rG`.

  There is no degree bound and no hypothesis on the number of tapes.
- `cutIneq_of_layout` and `cutIneq_of_cellCutIneq` give the first paper's inequality for unit-step
  walks.
- `layout_cutIneq_without_head_count` states the result in the form of the paper's
  `ExcursionLayout.cutIneq`. It drops the degree bound `q` and the hypothesis `4q ≤ 3kη` (and also
  `0 < η` and `2 ≤ |V|`), and in exchange asks for:
  - unit-step walks, which head trajectories are;
  - `2n ≤ |V|` instead of `n ≤ 2|V|`.

  The paper's construction has `|V| = 2n`, so it meets both versions.

**Oblivious machines.** `cellCutIneq_of_oblivious` proves that every oblivious transposer satisfies
the cell-accurate inequality at every slot length up to `nb`, with zero slack and a boundary cost
of `⌈log₂(number of states)⌉` bits per label change. `cellCutIneq_of_oblivious_on` does the same
for a machine that is oblivious and correct on a set of at least `2^(n²b−D)` inputs, with slack
`D`. So the finer inequality is a genuine necessary condition. The padded machine meets it with
zero slack and zero boundary cost, so the padding barrier survives it.

## Consequences for the paper

- The padding barrier holds with `E = 0`: the machine that runs the excursions and then simulates an
  arbitrary payload already meets the first paper's cut inequality and its M* conclusions. This
  includes payloads that do nothing.
- It also holds against the finer entry-cell charge, at every slot length up to `7K⌈nb/3⌉`. This
  answers the paper's remark that its theorem "does not establish the corresponding inequality with
  that finer charge": the padded machine without idle tapes meets it. By
  `StationaryTapes.observations`, adding idle tapes leaves the halting time and the other tapes'
  paths unchanged and only adds entry cells to the right-hand side, so the paper's machine with
  them meets it too. This last step is immediate but not formalized here.
- The paper's tape bound improves by `E·max(1, size(g(M)))` tapes.

The scope is the same as the paper's: walk-only counting inequalities. Conditions that tie the
walks to the input and output schedule (the input/output-aware form of the first paper's Cut Lemma)
or to the content of the cells are not addressed by this memo.

## Building

From this paper's directory, fetch or verify the pinned external dependency, as for the paper:

```sh
python3 verification/fetch_openai_metric.py
```

Then, in `memo/lean/`:

```sh
lake exe cache get
lake build
lake env lean MemoAxioms.lean
```

The last command prints the axioms of the memo's results; each depends at most on `propext`,
`Classical.choice` and `Quot.sound`. One proof, `cellCutIneq_of_layout`, raises `maxHeartbeats`
to 1,000,000 for a long but routine elaboration. The files:
- `PaddingMemo/CellCut.lean`: the cell-accurate inequality, and oblivious machines satisfy it;
- `PaddingMemo/LayoutCell.lean`: the per-offset count for excursion layouts, and the return to the
  first paper's inequality;
- `PaddingMemo/MachineCell.lean`: the paper's padded machine without idle tapes;
- `PaddingMemo/MachineCellUncond.lean`: the unconditional theorem;
- `PaddingMemo/Comparison.lean`: the results in the paper's own form.

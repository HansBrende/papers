# lean-backlog

Statements that have a written proof but no Lean proof yet, set out so that they can be formalized
independently of the work that produced them. Nothing in this folder is verified.

## What is here

| Item | File | Statements in `Statements.lean` | Field | Status |
|---|---|---|---|---|
| A. Decoders of bounded weight: odd words have single traces; the half bound | [`A-bounded-weight.md`](A-bounded-weight.md) | `norm_trace_word_le`, `finrank_code_le`, `two_mul_finrank_code_le_of_le_one`, `finrank_code_le_nPlus`, `two_mul_nPlus_le`, `exists_linear_excess` | ℂ | open |
| B. Codes with a recovery matrix: trace bound, rank bound, sign change | [`B-recovery-matrix.md`](B-recovery-matrix.md) | `two_mul_finrank_fixed_le_of_contraction`, `norm_trace_sq_le_rank_mul`, `two_mul_finrank_fixed_le_of_sign` | ℂ; any field for the last | open |
| C. The second rule for whole-row decoders with invertible blocks | [`C-second-rule.md`](C-second-rule.md) | `finrank_rowCode_le` | any field | open |

All statements date from 12 November 2026. Their proofs are written out in the Markdown files. They were
checked numerically on small instances but have not been refereed.

## How the files fit together

- Each Markdown file has the statements in ordinary notation, a complete informal proof, a suggested
  route in Lean, and what the result is for.
- [`Statements.lean`](Statements.lean) has the same statements in Lean, each with `sorry` as its
  proof. It typechecks against Lean and Mathlib v4.34.1:
  ```
  cd lean-machine && lake env lean ../lean-backlog/Statements.lean
  ```
  It belongs to no Lake package and is not built with the papers.
- The Lean statements were written by the author of the informal ones and have not been reviewed
  by anyone else. If a statement turns out to be wrong, awkward or weaker than it should be, change
  it and say what changed and why in the item's Markdown file.

## What "done" means

- A proof with no `sorry`, `admit`, `native_decide` or new axioms, depending at most on `propext`,
  `Classical.choice` and `Quot.sound`.
- The finished code goes to [`lean-machine/`](../lean-machine/) under its rules (one file
  `LeanMachine/<Name>.lean` or a folder with a README; add the module to `LeanMachine.lean` and the
  theorems to `Axioms.lean`), or to a paper's library if a paper is written around it.
- Update the status column above, and remove the item's statements from `Statements.lean` once they
  are proved elsewhere.

## Order of work

B is the shortest and A uses B1, so B first, then A (A2 and A1 before A3), then C. The items are
otherwise independent.

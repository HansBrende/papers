# lean-backlog

Written results collected for Lean formalization, independently of the work that produced them.
Items A, B and C are verified in `lean-machine`. Item D (added 12 November 2026, evening) is open.

## What is here

| Item | File | Declaration names | Field | Status |
|---|---|---|---|---|
| A. Decoders of bounded weight: odd words have single traces; the half bound | [`A-bounded-weight.md`](A-bounded-weight.md) | `norm_trace_word_le`, `finrank_code_le`, `two_mul_finrank_code_le_of_le_one`, `finrank_code_le_nPlus`, `two_mul_nPlus_le`, `exists_linear_excess` | ℂ | **A1–A4 proved**, with strengthenings |
| B. Codes with a recovery matrix: trace bound, rank bound, sign change | [`B-recovery-matrix.md`](B-recovery-matrix.md) | `two_mul_finrank_fixed_le_of_contraction`, `norm_trace_sq_le_rank_mul`, `two_mul_finrank_fixed_le_of_sign` | ℝ/ℂ and embedded fields for B1–B2; characteristic not two for the sign equation; every field for the bipartite and rank-defect certificates | **proved**, with strengthenings; declarations linked in the item file |
| C. Whole-row decoders: joint frontier rank and the second rule | [`C-second-rule.md`](C-second-rule.md) | `finrank_rowCode_le_rank`, `finrank_rowCode_le_local`, `finrank_rowCode_le` | any field | **C1–C2 proved**, with a local-invertibility refinement |
| D. Comparison bounds over every field; Frobenius form of A4; the fixed-term problem | [`D-comparison.md`](D-comparison.md) | `finrank_code_baseChange`, `finrank_code_add_le`, `two_mul_finrank_code_le_pairing`, `two_mul_finrank_code_le_triangle`, `finrank_code_le_compress`, `exists_linear_excess_frobenius`, `problemR_of_problemS` | any field (D5: ℂ) | **open**: seven obligations in [`StatementsD.lean`](StatementsD.lean); two open problems stated as propositions |

All original statements date from 12 November 2026. Their written proofs are in the Markdown files.
A1–A4, B1–B3 and C1–C2 are now kernel-checked in Lean. Formalization
does not by itself assess novelty or the adequacy of hypotheses for a particular machine model.

## How the files fit together

- Each Markdown file has the statements in ordinary notation, proof outlines, a map to the verified
  declarations, and what the result is for.
- [`Statements.lean`](Statements.lean) now imports the completed libraries without redeclaring their
  results. It contains no proof placeholders. Check it against Lean and Mathlib v4.34.1:
  ```
  cd lean-machine && lake env lean ../lean-backlog/Statements.lean
  ```
  It belongs to no Lake package and is not built with the papers.
- [`StatementsD.lean`](StatementsD.lean) holds the open obligations of item D, each with `sorry`. It
  needs `lake build LeanMachine.BoundedWeight.Asymptotic` first and is checked the same way.
- The original statements remain in Git history. Compatibility checks verified them against the
  shared declarations with no weakened hypotheses. The item files describe the generalizations
  and refinements; their Lean declarations are authoritative.

## What "done" means

- A proof with no `sorry`, `admit`, `native_decide` or new axioms, depending at most on `propext`,
  `Classical.choice` and `Quot.sound`.
- The finished code goes to [`lean-machine/`](../lean-machine/) under its rules (one file
  `LeanMachine/<Name>.lean` or a folder with a README; add the module to `LeanMachine.lean` and the
  theorems to `Axioms.lean`), or to a paper's library if a paper is written around it.
- Update the status column above, and remove the item's statements from `Statements.lean` once they
  are proved elsewhere.

## Completion status

Item D is open (see its file). A, B and C are complete, including the originally optional C1 rank bound. No original proof
obligations remain. The shared library also supplies reusable spectral, approximation,
coordinate-capacity and sequential-dimension lemmas.

The field-scope review adds verified scalar-extension transfers and arbitrary-field
rank-defect and bipartite certificates. It does not prove a finite-field counterpart of A4.
B's item file also records a written, not yet Lean-verified, extension of B2 to arbitrary
ordered fields; this is an additional result, not an unfinished original backlog item.

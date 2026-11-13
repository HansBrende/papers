# lean-backlog

Written results collected for Lean formalization, independently of the work that produced them.
Items A, B and C are verified in `lean-machine`. Item D (added 12 November 2026, evening) is open.

**Roadmap:** [`wall.md`](wall.md) states where the wall stands today and lists the direct, indirect
and closed fronts of the attack on it. Read it before choosing work; Claude Fable keeps it current.

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
- [`StatementsWholeRow.lean`](StatementsWholeRow.lean) defines the open linear D1 and covariant-group
  D8 conjectures as `Prop`s, with separate fixed-field and uniform-in-field variants. It asserts neither
  conjecture. Its helper lemmas check covariance, group-algebra conventions, ambient dimension, and
  rank-nullity, using only standard Lean axioms. Check it from `lean-machine/` with
  `lake env lean ../lean-backlog/StatementsWholeRow.lean`.
- [`StatementsRowSpread.lean`](StatementsRowSpread.lean) defines the geometric bridge
  and open **nonlinear** whole-row rate targets, including the canonical growing alphabet.
  It proves the exceptional-column, raw-boundary, and rectangle adapters.
- [`WindowSpread.lean`](WindowSpread.lean) now proves the complete quantitative and
  qualitative geometric row-spread targets. Its stronger theorem allows an output prefix
  of at least `d*d*b` appends and proves new-cut cost at most `63εL/64`, at most `21εd/32`
  exceptional rows, unchanged depth, and every new cut before the horizon. The original
  theorem follows directly. All endpoints use only standard Lean axioms. The machine and
  asymptotic native-crux consequences remain written implications; no capacity conjecture
  or new transposer exclusion is proved.
- The proof chain reuses actual native definitions:
  [interval amortization](WindowAmortization.lean),
  [native visits and labels](WindowLabels.lean),
  [finite-list/count adapter](WindowCounting.lean),
  [exact guards](WindowGuards.lean),
  [coarse dependency paths](WindowConeWindows.lean),
  [work-window counting](WindowWorkCounting.lean),
  [input/output rows](WindowRows.lean),
  [cone row covers](WindowRowCover.lean), and
  [quantitative budgets](WindowBudgets.lean).
  [WindowPages.lean](WindowPages.lean) independently proves the noncrossing page quotient;
  it does not assert endpoint uniqueness after contraction.

Check the entire row-spread chain using the existing pinned dependencies:

```sh
cd High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean
lake env python3 ../../lean-backlog/check.py
```

The helper script puts `.olean` files only in the package's ignored `.lake` directory.
After this build, optional module names check selected modules against the built dependencies,
for example `lake env python3 ../../lean-backlog/check.py WindowSpread`.

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

Written research notes supporting item D, not yet Lean-verified:

- [Finite-field lifting, joint-image surgery and expansion cores](notes/finite-field-expansion.md).
- [Linear comparison kernels for fixed-seed identity lifts](notes/identity-lift-comparison.md),
  including a characteristic-two refinement and exact finite comparison certificates.
- [Loop-adjusted controls for sheared helper relations](notes/shear-loop-controls.md),
  with 29 exact finite capacities, one remaining interval, and the corrected baseline.
- [Three-term seed assemblies](notes/three-term-seed-assemblies.md): a +3 bound
  for compatible assemblies, the limits of the minimal-counterexample reduction,
  and a unitary-classification obstruction to involutive seeds.
- [Involutive decoders: paired cuts and product spaces](notes/involutive-product-spaces.md):
  a reduction to strictly expanding cores and a characteristic-free quadratic-growth
  exclusion, covering the common unital factor-space case.
- [An explicit small-coefficient shear bound](notes/shear-small-coefficient-bound.md):
  zero asymptotic rate below a proved threshold for the three-helper N family over complex numbers.

Written notes for the covariant whole-row front D8:

- [Closed words, one-sided certificates, and distant helper loops](notes/covariant-word-baselines.md):
  a `(2/3 − o(1))` floor on a particular upper-bound expression, the ordered-support boundary correction,
  an exact scalar-monomial baseline, and distant sector gains with zero regular-representation gain.
  Run `python3 lean-backlog/tools/covariant_word_controls.py` from the repository root for the exact
  finite checks; the mathematical results in this note are not yet Lean-verified.

Native extraction and source audit:

- [Whole-row shape after an additional cheap cut](notes/row-spread-of-cones.md):
  a fully Lean-verified extraction for every native trace, with explicit constants for
  $d\ge4$ and every $b\ge1$. Any common positive whole-row deficit, uniform along the
  canonical growing alphabets, would imply the full native crux at each fixed depth.
  This last implication retains a written proof. No capacity bound or new machine
  exclusion is asserted.
- [Simplex-code calibration](notes/simplex-code-calibration.md): a reviewed written
  construction of rate $2/3-o(1)$ at window $(1+o(1))d^{1/3}\log d$, improving
  the projective-plane window exponent. Exact finite controls include the Fano
  three-bit code with 119 information bits, and computer-assisted scalar Fano
  dimension 39 over both $\mathbb F_2$ and $\mathbb F_3$. These results are not
  Lean-formalized and do not settle the fixed-window question. The linked
  reproduction folder supplies independent certificate checks.
- [Far cells and the Clebsch control](notes/far-cell-calibration.md): a
  Lean-verified whole-row embedding of the existing Clebsch code puts ten
  bits on sixteen far cells with all near cells fixed. This refutes the
  conditioned far-half principle; by itself it does not refute the global
  near-cell allowance. The note also states the required reverse-degree and
  component-radius qualifications.
- [Diagonal codes and window-dependent excess](notes/diagonal-code-calibration.md):
  the reviewed hypercube construction rules out every fixed-radius allowance
  with a window-independent constant. All odd folded cubes force an exponential
  window coefficient. A general-group theorem also bounds mutual-only
  within-diagonal decoding by half rate plus a vanishing term, with
  correlations allowed and shared advice charged. The basis host at $d=16$ has exact all-alphabet capacity
  $q^{176}$; the Clebsch binary case remains 210–211. A bounded two-sector
  covariant enumeration supplies no gain. The placement lemma is strengthened
  and Lean-verified for arbitrary functions; general rank and capacity arguments
  have written proofs and exact controls, without a new native exclusion.
- [Two-token mutual graphs and an oriented-code control](notes/two-token-and-oriented-controls.md):
  the reviewed odd-closed-walk identity does not bound distinct sectors. The
  known Paley tournament's 16-word binary code and universal nonlinear upper
  bound `q^4` are Lean-verified in [PaleyTournament.lean](PaleyTournament.lean).
  Written group-component and spectral deletion bounds explain why the
  diagonal theorem does not extend by cheaply making the full mutual graph
  bipartite. A fixed-coordinate reveal corollary retains the code's entropy
  deficit; no general capacity bound follows. Exact controls run with
  `python3 lean-backlog/tools/two_token_controls.py`.
- [Row-spread controls](notes/row-spread-controls.md): exact finite checks and a written
  block-reversal counterexample to the stronger inference of a bounded global monotone
  row-word cover. Run `python3 lean-backlog/tools/row_spread_controls.py` from the repository
  root. No finite test replaces the unbounded written proofs.
- [Window pages and input attachments](notes/window-pages-and-input-attachments.md):
  the one-work-tape separator calibration, a sufficient row-separator bound, and a
  geometric control showing why work-window planarity alone is insufficient. The
  control does not claim a fixed one-work-tape compiler. Exact page controls run with
  `python3 lean-backlog/tools/window_page_controls.py`.
- [Grid labellings and amplified storage codes](notes/grid-labellings-and-amplified-codes.md):
  a written quantitative half-rate bound for fixed-window grid codes with coordinate
  components of size `o(log d)`, extended to every recovery rule of a product code with
  blocks of that size. It excludes slowly padded high-rate fibres from Paper 15 under
  every balanced grid labelling. A separate argument excludes the standard contiguous
  layouts of its original displayed decoder at canonical entry width. The original growing-block construction
  remains open under arbitrary labellings. The row-spread note's §8 records the paid
  reverse-degree normalization and exact coset-index criterion; their incidence controls
  run with `python3 lean-backlog/tools/grid_labelling_controls.py`. These grid results
  are not yet Lean-verified and give no new native-machine exclusion.

- [Native cone properties and the remaining extraction problem](notes/native-cone-property-audit.md):
  the D4 comparison table against Papers 13 and 15, exact theorem scopes, remaining schedule classes,
  and a written selected-fibre success test using Paper 15's existing patch bounds. No new
  transposer class is excluded. The later row-spread note supplies a conditional tie
  missing when this comparison was written; obtaining the needed coding deficit remains open.

Item D is open (see its file). A, B and C are complete, including the originally optional C1 rank bound. No original proof
obligations remain. The shared library also supplies reusable spectral, approximation,
coordinate-capacity and sequential-dimension lemmas.

The field-scope review adds verified scalar-extension transfers and arbitrary-field
rank-defect and bipartite certificates. It does not prove a finite-field counterpart of A4.
B's item file also records a written, not yet Lean-verified, extension of B2 to arbitrary
ordered fields; this is an additional result, not an unfinished original backlog item.

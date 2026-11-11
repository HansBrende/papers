# Formalization checkpoint: 10 November 2026

Working draft; not a release. This record supersedes the earlier checkpoints
for the current formalization count, while preserving their review scopes.

Of the 48 numbered theorems, lemmas, propositions and corollaries, 35 are fully
formalized, six are partial and seven have written proofs only. Every numbered
result has a written proof. Definitions and supporting Lean declarations are
not counted as numbered results.

All ordinary proof assemblies in this sprint are complete. These include the
actual replay and localized cuts, getter and paid-loader application,
coherent-cluster extensions, complete producer/consumer block lemma, and the
actual simulator transport chain through original entry-capacity certificates
and original-execution crossing expansion. The last chain proves the clock,
head shadows, FIFO bounds, path and cone transport, finite guard bills and
uniform successful-subset consequences from the published native simulator.

The remaining numbered results are:

| Result | Status | Missing construction or dependency |
|---|---|---|
| 6.1 | Written proof | Dynamic sparse-carrier compiler |
| 6.2 | Partial | Compiler in 6.1; budgets and subsequent estimates are checked |
| 7.1 | Written proof | Redundant-archive wrapper |
| B.2 | Written proof | Prefix-catalogue compiler |
| D.2 | Written proof | Raw-relative carrier compiler |
| D.3 | Partial | Compiler in D.2; budgets and tail assembly are checked |
| E.2 | Written proof | Historical-cache compiler |
| E.3 | Partial | Compiler in E.2; budgets, duration and span consequences are checked |
| F.2 | Partial | Catalogue bound; conditional selection and persistence are checked |
| F.3 | Written proof | Future-readable eraser and catalogue construction |
| F.4 | Partial | Bound in F.3; subsequent selection and uniform estimates are checked |
| I.2 | Written proof | Native block monitor and paid spool |
| I.3 | Partial | Monitor bounds in I.2; counting and weighted-date consequences are checked |

These are explicit native construction projects and their dependent
consequences. No desired execution correspondence is supplied as an extra
axiom. Completion by result count is not a remaining-effort estimate.

Validation at this checkpoint:

- Full builds of this paper, the companion decoder paper and `lean-machine`
  passed. The generated audits checked all 153 declarations cited here, all
  223 in the companion paper and all 1,230 shared-library audit requests.
  Every response matched its request, with dependencies contained in
  `propext`, `Classical.choice` and `Quot.sound`; the audits had no errors or
  warnings.
- The actual cone and eroded-cut arguments, crossing geometry and finite
  lift, and final successful-subset/uniform crossing assembly received
  independent scoped reviews. These do not certify the missing constructions.
- The 52-page PDF was rebuilt and every page visually inspected. No overfull
  boxes, unresolved references, clipping or overlapping text remained.
- The public-path and whitespace checks passed. Frozen first-paper sources
  are unchanged. Nothing was staged, committed or pushed in this sprint.

The companion paper has 72 of 73 numbered results fully formalized. Its sole
remaining item is the native two-work-tape implementation. Across both drafts,
107 of 121 numbered results are fully formalized; 14 remain incomplete.

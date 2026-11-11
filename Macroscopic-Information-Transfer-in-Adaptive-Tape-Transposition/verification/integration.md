# Draft integration checks

Completed 10 November 2026, before the subsequent appendix integration recorded
in [appendix-integration.md](appendix-integration.md). The paper remains a working draft. This record
certifies the stated finite Lean results, not the written native headline
theorems or a resolution of unrestricted tape transposition.

- Regenerated the declaration index and `lean/PaperAxioms.lean` from the
  manuscript. The root module imports all ten public modules.
- The complete `lake build` passed without warnings. All 30 generated
  axiom-print requests occurred exactly once, with dependencies contained in
  `propext`, `Classical.choice` and `Quot.sound`. These cover 27 local
  declarations and the three explicitly cited imported geometry declarations.
- The [English–Lean review](english-lean-review.md) checked the original nine
  modules and formal-status boundaries. Its historical scope and subsequent
  authoring addendum are explicit. The later slab addition received a separate
  [independent review](slab-geometry-review.md), including its actual-input
  adapter and exact constants. The [written-proof review](proof-review.md)
  records the arguments and cited sources it inspected. No unresolved
  substantive issue was reported within these scopes.
- Rebuilt the 28-page PDF with `latexmk`, without undefined references,
  undefined citations or overfull boxes. Visually inspected every rendered
  page, including the new slab lemma, formalization table, index and references.
  The index has underfull-box warnings from long declaration names, without
  clipping.
- The final repository-wide portable-path check passed on 3,698 current
  public files, including both final PDFs. No staged check was run: the draft
  changes have not been staged, committed or pushed.

The remaining obligations are listed in the README and formalization appendix.
They distinguish ordinary unfinished counting steps from the substantial native
decoder, compiler and execution-correspondence work. No extra axiom substitutes
for any of them. Package and Mathlib pins are unchanged.

# Publishing plan

Status: released November 2026 after the completed reviews. The explicit
formalization exceptions below remain part of the published proof-status record.

The papers share a question, not a model: native adaptive executions in the first paper;
complete cyclic shared-decoder maps and linear correctness sources in the second.
Neither paper proves or disproves unrestricted linear-time tape transposition.
The manuscript must distinguish a theorem proved in Lean, a theorem with a precisely
identified formalization gap, and a complete written proof awaiting formalization.
An arithmetic consequence of an assumed structural inequality is not formalization
of the structural theorem. Every status in the README must match the actual declarations.

## Completed release checklist

1. Freeze the included theorem statements and map every numbered result to its proof.
2. Reuse sibling packages and Mathlib, with pinned dependencies; formalize every result
   whose missing infrastructure is not a substantial, potentially weeks-long project.
   Give every deferred item a concrete missing bridge and dependency, not just “future work.”
3. Check strengthenings, hypotheses, proof simplification and duplicated code.
4. Obtain independent English/Lean and proof/citation reviews; resolve their findings.
5. Generate the declaration index and axiom checks; build Lean and the PDF; inspect the PDF;
   check relative paths and publication metadata.
6. Review the inventory coverage table before release so no relevant substantial result
   is lost merely because an earlier section was easier to write.

## Narrative and inclusion

| Placement | Result family | Role |
|---|---|---|
| Main | Direct adaptive slab replay and two original heads with many macroscopic returns | Removes the heavy-original-trace qualification from the earlier original-execution necessity; retains an ambient exceptional-success count. |
| Main | Direct raw-input/output causal cuts; selected-slab off-carrier cuts | Separates the global all-demand-set quantifier from the local selected-demand theorem. |
| Main | Dynamic sparse carrier simulation and simultaneous large storage | Allows arbitrary carrier handoffs; derives a simultaneous-storage necessity. |
| Main limitation | Redundant-store normalization | Explains why large or informative tape words need not carry independent useful information. |
| Appendices | Coherent carrier clusters, catalogue extensions, strict prior-output-prefix catalogues, persistent marginal information | Preserve substantial strengthenings without interrupting the central replay argument. |
| Appendix | Guarded simulator pullback, all-large-output original crossing expansion, original entry-quotient capacity, remote future-readable persistence | Included because the selected-slab direct result does not subsume them; all execution-level bridge gaps are explicit. |
| Appendices | Fixed local getters, shared scan checkpoints, raw-relative changing carriers and secondary modification episodes | Preserve distinct access contracts; charge one shared label, actual observer state and historical mutable versions. |
| Appendix | Whole-run historical feedback, exact native cut invoices and finite input erosion | Separate historical reuse from useful information and preserve exact finite interfaces. |

The adaptive replay is now proved by comparing actual runs with the same
paid message and deriving input injectivity. A total decoder on invalid
messages is unnecessary. The dynamic carrier compiler remains a different,
substantial execution-level construction; the existing batch simulator does
not implement its handoff protocol.

## Main proof order

Model → slab selection → snapshot/replay record → injectivity/count → return necessity
→ original-cut replay → dynamic carrier simulation → simultaneous stores → limitations.
Catalogue and persistence extensions reuse this spine.

## Current formalization boundary

The following ordinary assemblies are complete:

- Actual adaptive replay, sparse messages and input injectivity.
- Uniform original return, input-cut and off-carrier expansion bounds.
- Coherent-cluster multi-core replay, actual rounded chart metadata, native
  class counting and simultaneous return/cut tails.
- Multiport getter reconstruction, enlarged-rule and strict-prefix variants,
  exact metadata and uniform tails.
- The native scan loader and its archive-preserving consumer application,
  including actual whole-run zero-discrepancy getters.
- The complete causal block-program and read-only-consumer information bound.
- Conditional and remote persistence from explicit native thin-source bounds,
  with original uniform laws, common intervals, retained events and all rates.
- Feedback success counts and finite long-span-date consequences from the
  explicit whole-run monitor inequalities.
- Literal carrier/reference/cache state and label budgets, their tails from
  explicit common native simulation contracts, and actual storage persistence
  and changed-address duration/span consequences.

- Actual simulator shadow/FIFO adapters, guarded path, raw-cone and eroded-input
  transport, original-entry capacity and its uniform success tail.
- Original-execution crossing expansion: actual crossing-target connectors,
  exact finite guard bills, successful-fibre expansion and uniform constants.

All ordinary proof assemblies in this sprint are complete. They reuse the
existing aligned native compiler; they do not implement the separate
constructions below.

The substantial remaining construction/correspondence projects are:

- Dynamic carrier transition tables, physical handoff invariants, sparse
  decoding and exact state bills; their catalogue, raw-relative and historical
  cache extensions.
- The last-visit eraser and redundant-archive wrapper, with exact native output,
  state and time guarantees.
- The native block monitor and paid spool through actual halt, with exact
  dated-version correspondence and complete state/event budgets.

Consequences retain these dependencies even when all subsequent arithmetic is
formalized. No extra axiom, admitted proof, native computation shortcut or
assumed headline property replaces a missing construction. The source count
premises of the persistence wrappers are stated explicitly and remain justified
by the manuscript's written native proofs.

## Formalization checkpoint

Paper A's status lines currently classify 48 numbered results as 35 formal,
six partial and seven written-only. Paper B has 72 formal results and one
written-only native compiler. These counts are not estimates of remaining
work. The root modules include all public local modules, and the generated
indices and axiom checks follow the manuscript's cited declarations.
Independent reviews distinguish the actual native endpoints from conditional
consequences; historical review scopes are retained separately. The release
preserves these proof-status boundaries.

## Remaining result integration todos

Inventory reconciliation and integration, 10 November 2026. All seven
accepted packages below are now stated and proved in the manuscript. Checked
boxes certify manuscript integration, not full Lean verification or release.
Successive strengthenings are consolidated into the strongest supported
interfaces; the README and formalization appendix distinguish checked
finite results from the substantial native bridges still to be formalized.

- [x] **A1. Locally reconstructible incoming values.** Extend adaptive replay
  to fixed public getters with one fixed carrier, continuous raw-window ports,
  paid observer state, one support-priced immutable label, and the strictly
  prior correct-output string. Include the finite correction count and
  all-width ambient success tail. Add shared spatial checkpoints for
  deterministic scans, including noninvertible scans, and the paid
  finite-state archive-loading application. Getters are analysis interfaces:
  the original machine still has one raw head and unreadable output. Current
  or future output, free port jumps, fresh advice at each handoff and
  unaccounted mutable archive versions remain excluded.

- [x] **A2. Changing carriers relative to raw and scan references.** Extend
  the catalogue section to a fixed portfolio of input-dependent locally
  readable references, moving cutoffs, sparse errors and strict-prefix masks.
  Charge the observer, shared scan seed, common hash, current registers and
  frozen pre-transition handoff records. Prove the entire-transition
  multiport counting lemma and the finite simulation on one retained
  half-set. Derive the all-width exponential bound for inputs with at most
  one unmatched word at every configuration. Public catalogues do not already
  cover these raw-dependent families. The intermediate simulator has counted
  extra analysis interfaces, not ordinary native one-tape access.

- [x] **A3. Secondary modification episodes.** Follow A2 with the historical
  cache extension, removing its at-most-one-current-exception hypothesis.
  Define the canonical carrier and inactive unmatched episodes precisely;
  count distinct old addresses actually changed, including restores and a
  successful exit. Prove the cache support bound s+m+1 and the complete state
  and label bill. Outside the ambient success exception, some secondary
  episode changes more than δP distinct cells, lasts more than δP successful
  steps and has macroscopic head span. For more than two tapes, the other
  unmatched tape can vary. Preserve the fixed reference-system premise;
  independent information and output usefulness are not conclusions.

- [x] **A4. Whole-run historical feedback.** Add an appendix for the exact
  native block monitor. With B=db, P=d²b and Φ=Σ_v Bℓ_v over participating
  dated block versions, state
  (1+φ/P)(1+(P−log₂|F|)/B) ≥ c_*d
  for every nonempty timely-correct low-Φ set F. Include its success tail and
  many-long-span-version corollary. Supply the block-monitor inequality and
  paid output-spool correspondence through actual halt; private proofs cannot
  serve as public citations. Keep the cheap copy/park control beside it:
  Θ(Pd) historical feedback can arise in linear time. This statistic measures
  historical reuse, not independent information or running time.

Compact supporting integrations, after those four substantive packages:

- [x] **A-S1. Joint import entropy.** State the conditional entropy consequence
  of the existing replay injection under one law. Charge metadata, exterior
  bits and ordinary records once, and import tags and values jointly.
- [x] **A-S2. Exact frozen-trace cut invoice.** State the demanded-coordinate
  joint-support bound on one common trace. Full records include cut-root
  output bits; field-only records instead pay
  (q+ka)|Γ| + |Γ∩roots|. Do not silently transfer this saving to the adaptive
  geometry-menu theorem.
- [x] **A-S3. Finite eroded-input transfer.** Record the common-simulator-fibre
  source-input cut lift, radius-3s erosion, the 6sr loss for r raw interval
  components, and the exact joint fibre-deficit inequality. The existing
  stronger asymptotic direct-cut theorem does not state this finite interface.

Current placement and status: A1 is in `getters.tex`; A2 in `references.tex`;
A3 in `episodes.tex`; A4 in `feedback.tex`; A-S1 and A-S2 in
`accounting.tex`; A-S3 in `transfer.tex`. The scan checkpoint lemma,
historical support lemma, joint invoice lemma, exact native frozen-trace
proposition and finite interval erosion lemma are formalized. The finite
eroded-input information bound is stated at every positive width: the new
full-record injection supplies its information step without the older
canonical-width acyclicity route. Its actual simulator cut lift is also
formalized, together with original entry-capacity certificates and crossing
expansion. The adaptive replay, getter and paid-loader application, and complete
block-program lemma are formalized. The new carrier/catalogue/cache handoffs,
eraser, redundant archive and native monitor/spool retain their explicit obligations.

Retain sharper finite overlap/shadow and marginal-information constants as
supporting material; promote them only where a later statement uses them.
Numbering an existing proof step does not create another contribution.

Integration order: A1 → A2 → A3, with A4 independent. Reuse the current finite
record, native-write, slab and context-pruning libraries. Keep ordinary replay and counting work separate from the substantial native
compiler and monitor projects; the current boundary above identifies both.
Every addition needs a complete statement and proof, exact formal status,
relation to the existing theorem, and independent review.

Complete-bank preparation/consumer compilers, independent-owner routing and
fixed-word external-memory purification belong in separate follow-ups.
The native theorems here do not supply those different interfaces.

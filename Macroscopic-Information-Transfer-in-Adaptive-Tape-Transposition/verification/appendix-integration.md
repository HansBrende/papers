# Historical appendix integration checkpoint

10 November 2026, before the subsequent formalization sprint. Working draft; no release, commit or push. This record concerns
the subsequent appendix integration, not the historical review scopes in
[integration.md](integration.md).

The four substantive accepted packages and three supporting packages are now
included: fixed local getters and scan suppliers; changing raw-relative carriers;
secondary modification episodes; whole-run historical feedback; joint import
entropy; exact frozen-trace cut records; and finite eroded-input transfer. Their
proofs are in the manuscript, without private-source citations.

Six Lean modules were added to the ten-module library. `ScanCheckpoints` proves
actual scan locality and common-label bounds; `HistoricalCache` proves support
growth from actual old-address modifications; `InformationAccounting` proves
joint entropy and cardinality identities; `InputErosion` proves the finite
interval-cover loss. `FrozenCutInvoice` proves the complete native frozen-trace
reconstruction and both full and field-only bills. `FeedbackNumerics` proves
only the integer optimization after the explicit window inequality.

The frozen-cut proof assumes actual native trace agreement and actual correct
designated output bits, and derives reconstruction from the native transition
recursion and literal dependency-path cut. Injectivity and cone determination
are conclusions, not assumed certificates. The full invoice includes cut-root
output bits; the field-only invoice charges one bit at each cut desired root.
This direct injection makes the finite eroded-input information bound valid at
every positive entry width. The actual simulator cut lift still has a complete
written proof awaiting formalization.

Validation at this historical checkpoint:

- All sixteen public modules are imported by the root module. The full package
  build passed without warnings, completing 9,265 jobs.
- The generator produced 48 axiom requests: 44 declarations named by local
  status lines, one other local declaration explicitly cited in the text, and
  three imported geometry declarations. All 48 requests occurred exactly once
  in generated order, with dependencies contained in `propext`,
  `Classical.choice` and `Quot.sound`, and no errors or warnings.
- The manuscript has 48 numbered results: 15 formal, two partial and 31 with
  complete written proofs not formalized. These counts do not promote the
  numerical optimization to a formal proof of the block-information lemma.
- The expanded PDF build has 46 pages, without undefined references,
  undefined citations or overfull boxes. The bibliography has underfull-box
  warnings from pinned source URLs. Every page was rendered and visually
  inspected, with separate full-page checks of the frozen invoice,
  eroded-input transfer and feedback displays. No clipping, overlaps,
  missing glyphs or unreadable status lines were found. After the independent
  review corrections, the PDF was rebuilt and rendered again; all affected
  pages were reinspected with the same clean result.
- The repository-wide portable-path check passed on 3,751 current public
  files, including both PDFs at that checkpoint. No staged check was run;
  these draft changes are not staged, committed or pushed.

The exact native frozen-cut theorem and the all-width eroded-input scope were
independently reviewed. The review confirmed that the cut, actual native fields
and designated correct output roots are the premises, without an assumed
recovery certificate. In the simulator application, a cut chosen from one
source run is a fixed set in the common simulator graph. The stronger full
record coefficient `v_s` is stated explicitly; `v_s+1` remains an immediate
weaker bound.

The new independent written-proof review covered the getter, reference,
historical-cache, feedback and accounting appendices and the eroded-input
extension, together with the model, relevant replay/cut support and the
revised order-symmetry paper's entry/advice interface. It found no blocking
main-theorem defect after two localized corrections: the
cheap copy/rescan control now pays the monitor-window export delay and all
encoded planes, and the cut-choice warning now applies to pooled adaptive
encoders rather than separate universal fixed-fibre inequalities. The
underlying feedback and frozen-cut bounds are unchanged by these corrections.
This scoped review did not rerun the build or independently audit every
imported Lean declaration, and it preserves the explicit native
formalization gaps. Build and axiom results above are separate checks.

The earlier English–Lean and written-proof reviews are preserved as historical
records. They do not claim to cover these additions. Package pins and frozen
source files are unchanged.

At this historical checkpoint, remaining formalization was explicit. Ordinary finite hash selection, message
menus, block-program transcript/entropy work and asymptotic assembly have not
been relabelled as weeks-scale projects. The concrete scan loader is a smaller
remaining native construction. The larger missing projects construct the total
adaptive replay decoder, raw-relative and historical handoff transition tables,
actual simulator pullback and native block-monitor/spool correspondence. A
successful build certifies the checked declarations, not these written proofs.

# Independent written-proof and citation review

Status: PASS after three small clarifications. Working draft; this review is not a Lean proof of the written native compilers or a clearance of external priority.

At the time of the initial full review, the reviewer had not authored this paper's manuscript or native implementations. The review freshly read the complete mathematical manuscript, bibliography, front matter, formalization boundary and README listed below. It compared the stated interfaces with the cited source declarations and checked the proofs' resource and quantifier accounting. No new experiment or solver run was used.

## Findings

- **Adaptive replay and causal cuts.** The decoder keeps the protected dictionary across gaps, reconstructs the full old tuple before writes, charges all entry states and imports, and uses actual last visits, including preserving writes. It proves one input injection over each message class without assuming a common original trace. The description-free choice of omitted raw bits uses all retained/cut output ordinals and full correctness. Localized snapshot overlays are chronological and require correctness only at the next read; they do not assert equality of the entire skipped memory.
- **Geometry and exceptional sets.** The short/long slab branches use different snapshot bills. The displayed constants leave the stated saving. Sparse import supports are encoded jointly. The successful-set bounds are ambient cardinality bounds, fixed-table statements and uniform in all positive widths where claimed. Original arbitrary-output crossing expansion and entry-capacity asymptotics are explicitly canonical-width statements.
- **Dynamic carriers and catalogues.** All live syndromes, counters, positions, offsets and the frozen snapshot are in the finite controller product. An incoming dense carrier is at most one write above sparse, and a switch consumes no extra physical move. Lazy physical reuse ignores stale symbols until their first phase visit. The common hash is selected against original input trajectories, before simulation; neither adaptive hash-dependent source traces nor a union over hypothetical prefixes is used. The strict prior prefix is reconstructed before the entire transition and frozen catalogue snapshots retain their pre-append prefix ordinal.
- **Persistence and source transfer.** All top sets use one original law; one common selected subset and fixed pair/time interval are retained. The context-pruning ratio charges the attained fibre density, not just average guessing. The future-readable eraser is trace-specific and its last successful reads exclude the halt-test tuple. Simulator-to-source reconstruction pays the actual current window and fringe cells. Every attained trace fibre is counted. Guarded pullback retains the extra terminal batch, drain, delayed-output roots, input-boundary effects and endpoint deletion convention.
- **Redundant archives.** Both tagged input copies are paid, preserve the original work payload, and survive every unsynchronized core/cleanup phase until a final successful scan. The archive gap is strictly larger than the allowed masking diameter. Global deterministic dependence remains valid for mixtures of phases at a fixed absolute time. The construction does not assert useful rereads, independent stores, native access to its mathematical decoders, or identical divergent output prefixes.

Three edits were made: the order-chart lemma now explicitly assumes positive coordinate count and a nonempty family; the crossing-target discarded-level count now explains the distinct time-ordered epoch-pair factor; and a split TeX subscript in the simulator-state bill was repaired. None changes a numerical or native theorem.

## Citation/interface verification

Bibliographic titles, authors, dates and directory targets for all nine sibling-paper entries were checked from their `paper/main.tex` metadata at the bibliography's pinned repository revision `b29fa7ac3a932a98f069c6f7667c502781550ed3`. The Mathlib revision agrees with the repository's pinned dependency. The cited literature is local prior work; no independent external-priority search is represented here.

Additional actual source reads (paths relative to the papers repository):

- `Oblivious-Linear-Time-Tape-Transposers-Need-Macroscopic-Crossings/lean/NativeRelations/OneFreeHeadSmallExcursion.lean`, lines 172–206, 528–560 and 1210–1255: exact offset, chunk dichotomy and stripe interfaces, with bounded adjacent proof text. These permit arbitrary width and make no obliviousness assumption in the finite geometry.
- The same package's `NativeRelations/TightConstants.lean`, lines 2765–2855: actual correct-subset crossing theorem, its canonical width, fixed trace subset and entropy threshold. Its geometric entropy reserve depends on tape count/time/target density before simulator block size; the value-width factor enters the cut constant separately.
- `High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean/TapeStorageRates/NativeSimulation.lean`, lines 90–135: literal full-block boundary interface and beginning of the exact halting simulation.
- The same package's complete `NativeTypicalResources.lean`: successful-subset trace count and time coefficient independent of the chosen fixed batch size after its startup threshold. No full read of every transitive simulator implementation is claimed by this review.

## Formalization triage

The finite order-conflict chart is ordinary finite real analysis, not native compiler infrastructure. It can be formalized using finite coordinatewise prefix maxima, a monotone continuous max-envelope interpolating that finite chain, and a sum-parameter normalization. The converse is immediate from monotonicity and two error allowances. This is the next feasible formalization task; its written status remains until that construction compiles.

The finite sparse-position/counter menus, binomial/asymptotic assembly and finite typical-set selection are likewise ordinary mathematical obligations, though they must be kept separate from the substantially larger end-to-end native encoder/compiler proofs. A successful Lean build of the listed kernels alone does not certify those written assemblies. The proof-status boundary in the manuscript is honest about this distinction.

## Complete manuscript read pins

Pins record the bytes after the three stated clarity edits. No claim of full upstream-source or external-literature review is attached to these pins.

| File | Read lines | SHA-256 |
|---|---:|---|
| `paper/main.tex` | 1–44 | `d873a3e0122406db45f5e29d54e86350c65e91606de175ebfa5dbe3903af9638` |
| `paper/references.bib` | 1–93 | `7e003ab4dec8dbb8d44ab9e7df8749eabb0a00a11b68eb235bf1a80d1cfa8fab` |
| `README.md` | 1–97 | `8bb6d19b8d7ed10d70d06bde13cfe83796bce3fe3c192ce9a9a5eab64fa46f97` |
| `paper/sections/abstract.tex` | 1–18 | `095b5deee34c305e432d074f0c5008abef8d56cd4205e7152f809b55a3a01574` |
| `paper/sections/catalogues.tex` | 1–109 | `57b25407a6abddd6318a5f207ad3947049bbff68b2688d159352524ed405de93` |
| `paper/sections/clusters.tex` | 1–120 | `1c94d79758cc445a0e7da5da3fec27e18766c736926321ac9cd83dbeb3782685` |
| `paper/sections/formalization.tex` | 1–63 | `bd989f90542d870d87e2658afa4eb15f5f4bbf80c1f13cd6b5ccc97dedfae25d` |
| `paper/sections/fragments.tex` | 1–182 | `0f2a1e5abe7c6af0d687697e26ca8165985e5ff878eafdd5b0402932a3fe9858` |
| `paper/sections/introduction.tex` | 1–77 | `3cf17eaf2b4c9316cf4bc8731d06bf9666fc535b391fc26e29fe896aef185b2a` |
| `paper/sections/limitations.tex` | 1–90 | `c8c2577bbb7032bf8e423f5f33d14c9a8b4067b0aaa41d685f738e481f2898f6` |
| `paper/sections/model.tex` | 1–54 | `83d47dcc8c2795010883894be16b74a3dab49a7cafa40bb1d14f37aa11f233b2` |
| `paper/sections/open.tex` | 1–26 | `811249b1d19e3e007a8779fc5d7309f8d26a057b1ac22c34833d4178ec69d786` |
| `paper/sections/persistence.tex` | 1–207 | `515a358eae6bb59b712398c40f448de346f03da1507bbba620771589bf3cf889` |
| `paper/sections/replay.tex` | 1–116 | `ebc87d258577ccf42317f7b5bd061731cf5de9566b4f57a3ec6e6c9051e3fe0f` |
| `paper/sections/returns.tex` | 1–103 | `8eac848695856dcdb3be21dca7c4b15b0b0a9dca757fe18d68d0c7c3878d8ca0` |
| `paper/sections/storage.tex` | 1–129 | `5021eb8c295473bd537fc1599c332d4c81e0dd4e10cde2ccc90e71809144898b` |
| `paper/sections/transfer.tex` | 1–291 | `d4d59e3fe34097baa545917a1d6ded33cd82f73a4f058e4c3d55be7c78a7d248` |
| `paper/sections/verification.tex` | 1–19 | `c1550856c77f5de34c95eb60cbafa75cabc42bb8138f154e428b84fcc2dd10d4` |

## Subsequent finite-chart formalization

The finite order-conflict lemma has subsequently been fully formalized, including its literal maximum, normalized chart, coordinate-specific strengthening and converse. This reviewer authored that formalization and its revised proof outline; this addendum is a declaration-to-text check, not an independent audit of that new Lean code. The original source pins above remain a record of the earlier complete review, rather than current-byte pins for later manuscript/status changes.

The shared `MonotoneChainEnvelope` and `OrderConflictChart` modules and the paper's `OrderChart` adapter compile. A targeted axiom audit of the chain endpoint, coordinate-specific theorem and all three paper aliases reports only `propext`, `Classical.choice` and `Quot.sound`. The stated assumptions are exactly finite nonempty time and coordinate types. There is no strict-order, distinct-sum or bounded-coordinate assumption. Tied sums are handled by prefix maxima; the normalization preserves repeated knots. The converse requires only coordinatewise monotonicity and the stated approximation error.

Formalization files (relative to the papers repository):

| File | SHA-256 |
|---|---|
| `lean-machine/LeanMachine/MonotoneChainEnvelope.lean` | `5c02bec3ae93c5e3cea8ea7a1767cd92b0cc2447e6b939b402a433bb3a161dc8` |
| `lean-machine/LeanMachine/OrderConflictChart.lean` | `ab6ccdce8ea30b9dacbbc9d36e2838d4710183c59c88d5bb694cc0fc836b4a14` |
| `Macroscopic-Information-Transfer-in-Adaptive-Tape-Transposition/lean/AdaptiveTransfer/OrderChart.lean` | `572ef637cb2f158631569ec96ea8e9a1cfb23eca7f4d96b884b425378c83da3b` |

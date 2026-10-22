R1914 preservation tools — root executes all Lean/Lake; these tools never do.

Prepared baseline
- capture/names.json freezes all 6306 current audited declarations, including the
  nine Core declarations absent from the original R1912 type baseline.
- capture/baseline-inspect.lean exports 79 chunks of at most80 names.
- Root's baseline run succeeded. capture/baseline-compact.json records each
  type SHA256/size/universe list plus every full chunk's hash and provenance.
- baseline-types.tar.gz preserves the full chunks and relevant metadata in91
  members, verified by direct decompressed-byte comparison. All raw chunks remain.
- No894MB aggregate exists. The full chunks total roughly the old aggregate size
  temporarily; compression reduces storage. Hashes do not replace exact equality.

Final inspection, once adopted edits and ordinary build finish
  python3 /private/tmp/r1914-preservation/prepare.py final
Root runs generated capture/final-inspect.lean through its ordinary Lean harness.
Then:
  python3 /private/tmp/r1914-preservation/types.py seal final \
    --execution FINAL_TIMING_JSON --log FINAL_LEAN_LOG
  python3 /private/tmp/r1914-preservation/types.py compare
The comparison checks all6306 original names, exact decoded Expr repr strings,
and ordered universe parameters, one chunk pair at a time. New audit additions
are permitted but need the final normal axiom audit; they are not mislabeled as
original declarations. Raw differences produce a separate differences.json and
status differences_require_review. They are never dismissed as cosmetic.

If and only if actual differences exist
  python3 /private/tmp/r1914-preservation/prepare-kernel.py
Root can run capture/kernel/check.lean. This reuses the reviewed R1912 constructor
parser and Lean decoder. It requires exact original repr reconstruction, exact
current-environment repr match, identical ordered universe parameters, and native
Kernel.check of (fun h : originalType => h) currentConstant. Positive and
intentionally ill-typed negative controls run per <=8-record chunk.
The generator adds no axioms, aliases, normalizations or environment patches.
Missing retired generated proof names fail closed. If any occur, preserve that
failure and use a separately recorded proof of the exact archived source header,
as in R1912; do not relabel that route as an exact original-Expr conversion.
A semantic receipt should combine the raw exact count and only the actual
successfully checked kernel/source-header names. It must require terminal exit0
and unique full difference-name coverage, not merely a count or hash agreement.

Source guards, after the final source state is stable
  python3 /private/tmp/r1914-preservation/source-guards.py --output REPORT_JSON
These protect non-import bodies for all six theorem families and shared finite
coding/native machine model modules (an exact intact relocation is allowed).
They also check original names, trust tokens/options, acyclic complete imports,
8 configurations,204 external sources,117 protected sibling files and430 immutable
historical receipt logs. The3 mutable current summaries are excluded from log
immutability; root must archive their pre-edit bytes before rewriting them.
Other changed mathematical bodies are listed for explicit proposal-level review;
this guard does not pretend to prove every edit body-preserving automatically.

Archive choices; do not overlap compression with performance measurements
  python3 /private/tmp/r1914-preservation/pack-side.py final --output FINAL.tar.gz
or after comparison:
  python3 /private/tmp/r1914-preservation/types.py archive --output BOTH.tar.gz
Both use exclusive creation and direct decompressed-byte verification before
publication. Neither removes input chunks. Do not create both unnecessarily.
The two-sided archive preserves raw comparison evidence, even when unresolved;
its receipt explicitly does NOT certify semantic preservation. Add any later
kernel/source-header evidence to a separate verified archive, or include it in
the root's final evidence package. No archive need contain a giant aggregate.

Final root-owned gates
- One ordinary successful full build; all execution handles terminal.
- All original6306 names present; justified new declarations audited as well.
- Full actual axiom output only propext,Classical.choice,Quot.sound.
- Every raw mismatch resolved by explicitly labeled kernel/source-header checks.
- Exact reviewed source changes, protected original paper/configurations intact.
- Preserve failed attempts, run logs/timings, compact manifests, archive receipts,
  source maps and old summary bytes. Update support-build.json only after success.
- Claim measured gains only for matched benchmark workloads; do not mix archive
  CPU/I/O with measurement runs or infer end-to-end speedup from static counts.

Compact semantic receipt (small metadata only)
  python3 /private/tmp/r1914-preservation/finish-types.py \
    --execution KERNEL_TIMING_JSON --log KERNEL_LOG
If comparison is entirely exact, omit execution/log; no redundant kernel run is
needed. If root prepares a separately reviewed source-header fallback, pass its
explicit provenance JSON with --source-headers and its updated v2 plan with
--plan. The assembler requires all actual mismatch names exactly once, mandatory
controls, old/current literal provenance, correct route booleans, actual checker
hash and terminal exit0. It never edits comparison.json or old receipt evidence.

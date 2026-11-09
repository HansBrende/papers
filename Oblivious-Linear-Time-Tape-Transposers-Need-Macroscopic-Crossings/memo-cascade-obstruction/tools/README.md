# Reproducing the finite checks

These tools check source identity and small implementation examples. **They do
not prove the asymptotic cascade exclusion.** The memo identifies the written
arguments and the Lean proof of the canonical-width C5 declarative schedule.

Use a complete clone of this repository, keeping the sibling paper directories
in place. The scripts use Python 3.8 or later and its standard library only.
The geometry and C5 comparison checks also need a Rust toolchain compatible with the original
[experiments crate](../../experiments/). That crate has no external dependencies;
the build uses `--offline --locked`. No solver or network connection is used.
The scripts are licensed under [Apache 2.0](LICENSE).

Run from `memo-cascade-obstruction/`:

```sh
python3 tools/check_source_pins.py --output verification/source-check.json
python3 tools/lane_lift_control.py --output verification/lane-lift-control.json
python3 -B tools/check_geometry.py --output verification/geometry-control.json
python3 tools/check_c5_lean_trace.py --output verification/c5-lean-trace-control.json
```

The C5 comparison additionally requires `lake` on `PATH` and the current Lean
library built first. All four commands exit unsuccessfully on a failed check. Run without Python's
`-O` option: the finite controls require assertions. Omit `--output` to print
JSON to standard output. Receipts are deterministic, with no timestamps or local
paths. To compare without replacing a saved receipt, write to a temporary file
and use `cmp` against the corresponding file in `verification/`.

## Source pins

[`source-pins.json`](../verification/source-pins.json) records the original
sources at commit
[`9ffa8f2e5494988731a37c0bed8b0be6a046e5e8`](https://github.com/HansBrende/papers/tree/9ffa8f2e5494988731a37c0bed8b0be6a046e5e8).
The checker compares the current bytes of 26 files with their SHA-256 hashes:
the entire Rust crate's code, Cargo files and license, plus the principal
native-machine and regular-motion theorem interfaces and their package pins.
The current checkout may include later commits if these source files are
unchanged. A source archive also works; Git is not required by the checker.

This is a targeted source manifest, not a complete transitive Lean dependency
manifest or a Lean build certificate. It does not hash mutable repository or
paper READMEs. The memo's Lean instructions cover formal verification separately.

## Lane lift

`lane_lift_control.py` compares independent ordinary machines with a separate
interpreter of every physical transition in the oblivious `3b` simulation.
At every completed simulated step it compares controllers, head positions,
complete nonzero work contents, and output. It also checks the integer form of
the motion error bound. Repositioning reads and preserve-writes are executed.

The four cases use lane widths 2 and 3 on a literal two-by-two transpose and on
a nonlinear two-tape program. The transpose case is also checked directly against
the mathematical transpose. The nonlinear case exercises left/right/stay moves,
exterior raw reads, state, simultaneous writes and nonzero repositioning reads.

The saved [receipt](../verification/lane-lift-control.json) reports **4,928
inputs and 569,088 unit transitions**. Three deliberately wrong interpreters
are rejected: sharing a controller across lanes, making sequential work writes,
and allowing repositioning reads to alter data control. These are finite checks
of the general block simulation; widths 2 and 3 at side length 2 are not the
canonical logarithmic entry width. No cascade data completion is supplied.

## Original-export geometry calibration

`check_geometry.py` first checks the source pins, builds the **unchanged original
Rust crate** in a temporary directory, and asks its CLI for complete JSON exports
of C1–C5 at `d=16`, `b=1` and `b=4`. It does not generate a competing schedule.
The temporary build and exports are removed when it finishes. Add
`--keep-exports DIR` to preserve the original exports in a chosen local directory;
their hashes are recorded in the receipt. They need not be committed.

The [receipt](../verification/geometry-control.json) covers **ten exports and
273,065 original steps**. It checks:

- Every recorded head position and unit move, including waits and transit; raw
  read coordinates; and every append ordinal and transposed target coordinate.
- The stated safe total-time bounds on these instances.
- The closed-form first-half counter profile at all three forward scales of
  C1–C4: 24 loop checks, including C4's extra terminal stationary event.
- C1's first nonzero column shift: `3db` ticks per nonfinal row, `2db−1` for the
  last row, and the bounded deviation from its affine approximation.
- Rejection of three malformed exports: an incorrect initial position, a
  nonunit move, and an incorrect output target.

The exports retain every original instruction. Write annotations are used only
to locate existing loops; they do not restrict the memo's arbitrary-update
model. At `d=16`, C1's eventual parameter formulas for `d≥256` have not yet
stabilized. The checks establish neither convergence, all stage budgets, an
asymptotic threshold, nor transpose correctness of any cascade. They run no
Menger-cut calculation or dimension sweep.

## Exact C5 Lean–Rust trace comparison

`check_c5_lean_trace.py` evaluates the actual `C5.trace` Lean definition using a
temporary exporter, then compares it with the unchanged original Rust constructor.
There is no second Python schedule generator. Every input/work move, append flag,
pre-step position and terminal position is compared, including waits and resets.

The [receipt](../verification/c5-lean-trace-control.json) covers eight cases at
`d=4,8,16`, with widths drawn from `1`, `3` and the canonical width: **38,504 ticks**.
Missing-tick, changed-move and flipped-append mutations are rejected. Source and
loaded Lean object hashes are recorded; refresh the receipt after a rebuild that
changes those objects. The script does not run `lake build` or change sources.

This is finite transcription calibration. The asymptotic result is a kernel-checked
theorem about the Lean schedule; correspondence with Rust at every size remains
a written source audit. Arbitrary local updates are allowed at every compared tick;
Rust write annotations impose no extra preservation condition.

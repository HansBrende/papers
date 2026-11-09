#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Compare the actual Lean C5 tick word with unchanged original Rust exports.

From the memo directory, after building its Lean library:
    python3 tools/check_c5_lean_trace.py --output verification/c5-lean-trace-control.json

Requires Python's standard library, the pinned Lean package's existing compiled
modules, and the Rust toolchain. Rust builds offline/locked in a temporary
directory. The temporary Lean exporter imports the actual C5 definition;
there is no second Python implementation of the schedule. No lake build runs.
This is finite source-binding calibration, not a formal semantics of Rust.
"""

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

from check_source_pins import DEFAULT_REPO, MANIFEST, verify


PAPER = Path("Oblivious-Linear-Time-Tape-Transposers-Need-Macroscopic-Crossings")
MEMO = PAPER / "memo-cascade-obstruction"
CRATE = PAPER / "experiments"
MODULES = ("C5Trace", "C5Stages", "C5Schedule")
CASES = tuple((d, b) for d in (4, 8, 16)
              for b in sorted({1, d.bit_length() - 1, 3}))


def sha(data):
    return hashlib.sha256(data).hexdigest()


def lean_exporter():
    cases = ",\n".join(
        f"  Lean.Json.arr ((trace {d.bit_length() - 2} {b}).toArray.map exportTick)"
        for d, b in CASES)
    return f'''import CascadeObstruction.C5Schedule
import Lean

open CascadeObstruction.C5

def exportTick (x : Tick) : Lean.Json := Lean.Json.arr #[
  Lean.toJson (dirValue x.input), Lean.toJson (dirValue x.work0),
  Lean.toJson (dirValue x.work1), Lean.toJson x.emit]

#eval IO.println ((Lean.Json.arr #[
{cases}
]).compress)
'''


def compare(lean_ticks, rust_trace, d, b):
    """All pre-step positions, all unit moves, and all append events."""
    assert rust_trace["id"] == "c5_comb_fanout"
    assert (rust_trace["d"], rust_trace["b"], rust_trace["k"]) == (d, b, 2)
    assert rust_trace["computation_kind"] == "geometry_only"
    assert rust_trace["L"] == d * d * b
    assert len(lean_ticks) == rust_trace["T"] == len(rust_trace["steps"])
    input_pos, work_pos, appends = 0, [0, 0], 0
    for time, (tick, step) in enumerate(zip(lean_ticks, rust_trace["steps"])):
        assert len(tick) == 4 and type(tick[3]) is bool
        assert all(type(move) is int and move in (-1, 0, 1) for move in tick[:3])
        assert step["t"] == time
        assert step["in_pos"] == input_pos
        assert [work["pos"] for work in step["work"]] == work_pos
        expected = [step["in_move"], *(work["move"] for work in step["work"]),
                    step["append"] is not None]
        assert tick == expected, (d, b, time, tick, expected)
        if tick[3]:
            assert step["append"]["out_idx"] == appends
            appends += 1
        input_pos += tick[0]
        work_pos = [position + move for position, move in zip(work_pos, tick[1:3])]
    assert appends == d * d * b
    assert input_pos == d * d * b and work_pos == [d * d * b - 1, 0]
    return {"steps_checked": len(lean_ticks), "append_events_checked": appends,
            "terminal_input_position": input_pos, "terminal_work_positions": work_pos}


def rejection_controls(ticks, rust_trace, d, b):
    results = []
    for mutation in ("missing_tick", "moving_tick_changed_to_stay", "append_flag_flipped"):
        bad = deepcopy(ticks)
        if mutation == "missing_tick":
            del bad[len(bad) // 2]
        elif mutation == "moving_tick_changed_to_stay":
            time = next(i for i, tick in enumerate(bad) if tick[1] != 0)
            bad[time][1] = 0
        else:
            bad[0][3] = not bad[0][3]
        try:
            compare(bad, rust_trace, d, b)
        except AssertionError:
            results.append({"mutation": mutation, "rejected": True})
        else:
            raise AssertionError("malformed Lean word accepted: " + mutation)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=DEFAULT_REPO)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not __debug__:
        parser.error("run without -O: these controls require assertions")
    source_check = verify(args.repo)
    lean_dir = args.repo / MEMO / "lean"
    module_pins = []
    for name in MODULES:
        source = lean_dir / "CascadeObstruction" / f"{name}.lean"
        obj = lean_dir / ".lake/build/lib/lean/CascadeObstruction" / f"{name}.olean"
        if not obj.is_file() or obj.stat().st_mtime_ns < source.stat().st_mtime_ns:
            parser.error(f"build the current Lean module before calibration: {name}")
        module_pins.append({"module": "CascadeObstruction." + name,
                            "source_sha256": sha(source.read_bytes()),
                            "compiled_object_sha256": sha(obj.read_bytes())})
    exporter = lean_exporter()
    tests = []
    with tempfile.TemporaryDirectory(prefix="c5-lean-source-check-") as temp:
        temp = Path(temp)
        lean_source = temp / "ExportC5.lean"
        lean_source.write_text(exporter)
        exported = subprocess.run(["lake", "env", "lean", str(lean_source)], cwd=lean_dir,
                                  check=True, stdout=subprocess.PIPE).stdout
        lean_cases = json.loads(exported)
        assert len(lean_cases) == len(CASES)
        target = temp / "target"
        subprocess.run(["cargo", "build", "--quiet", "--release", "--offline", "--locked",
                        "--manifest-path", str(args.repo / CRATE / "Cargo.toml"),
                        "--target-dir", str(target)], check=True)
        binary = target / "release/paper16-experiments"
        for ticks, (d, b) in zip(lean_cases, CASES):
            original = subprocess.run([str(binary), "export", "c5_comb_fanout",
                                       str(d), str(b), "json"], check=True,
                                      stdout=subprocess.PIPE).stdout
            trace = json.loads(original)
            tests.append({"d": d, "b": b, "levels": d.bit_length() - 2,
                          "canonical_width": b == d.bit_length() - 1,
                          "L": d * d * b, "rust_export_sha256": sha(original),
                          "lean_ticks_sha256": sha(json.dumps(ticks, separators=(",", ":")).encode()),
                          **compare(ticks, trace, d, b)})
            if len(tests) == 1:
                mutations = rejection_controls(ticks, trace, d, b)
    report = {
        "status": "PASS",
        "scope": "Finite exact Lean C5 tick-word versus original Rust source calibration",
        "source_commit": source_check["source_commit"],
        "manifest_sha256": sha(MANIFEST.read_bytes()),
        "script_sha256": sha(Path(__file__).read_bytes()),
        "lean_exporter_sha256": sha(exporter.encode()),
        "lean_modules": module_pins,
        "tests": tests,
        "mutation_controls": mutations,
        "total_steps_checked": sum(test["steps_checked"] for test in tests),
        "limits": [
            "The Lean exporter uses already-built checked definitions; the executable comparison is a calibration, not a kernel theorem.",
            "No formal semantics of Rust or all-instance source equivalence is inferred from finitely many exports.",
            "Every positioning/terminal tick is compared; write annotations are deliberately not imposed on arbitrary data completions.",
            "No transpose data program, numerical asymptotic cutoff, or new arbitrary-width exclusion is obtained.",
        ],
    }
    text = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
        print(f"PASS: {len(tests)} exact C5 trace comparisons; {report['total_steps_checked']} steps")
    else:
        print(text, end="")


if __name__ == "__main__":
    main()

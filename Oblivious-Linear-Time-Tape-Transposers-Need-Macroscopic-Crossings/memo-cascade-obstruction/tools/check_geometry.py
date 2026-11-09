#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Small geometry calibration against ORIGINAL Rust schedule exports.

Usage (from the memo directory):
    python3 tools/check_geometry.py --output verification/geometry-control.json

Builds the pinned original crate offline in a temporary directory, then exports
C1--C5 at d=16 and b in {1,4}. No Python schedule generator, flow solver, or data
completion is used. Requires Python's standard library and the crate's Rust
toolchain. --keep-exports DIR optionally preserves the original JSON exports.
See tools/README.md: these finite checks are not an asymptotic proof.
"""

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

from check_source_pins import DEFAULT_REPO, MANIFEST, verify


CRATE = Path("Oblivious-Linear-Time-Tape-Transposers-Need-Macroscopic-Crossings/experiments")
CASES = (
    ("c1_torus_cascade", 2, 256),
    ("c2_bfly_cascade", 2, 256),
    ("c3_ten_entry_cascade", 3, 160),
    ("c4_no_overwrite_cascade", 3, 256),
    ("c5_comb_fanout", 2, 36),
)


def positions(step):
    return tuple(w["pos"] for w in step["work"])


def tpos(d, b, r):
    lane = r % b
    i, j = divmod(r // b, d)
    return (j * d + i) * b + lane


def validate_trace(trace, schedule_id, k, time_factor):
    """Check every original step, including waits, transit and raw rereads."""
    d, b, length, horizon = (trace[key] for key in ("d", "b", "L", "T"))
    assert trace["id"] == schedule_id
    assert trace["computation_kind"] == "geometry_only"
    assert d == 16 and b in (1, 4) and trace["k"] == k
    assert length == d * d * b and len(trace["steps"]) == horizon
    assert 0 < horizon <= time_factor * length
    expected_input, expected_work = 0, (0,) * k
    append_count = raw_reads = waits = 0
    extrema = [[0, 0] for _ in range(k)]
    for t, step in enumerate(trace["steps"]):
        assert step["t"] == t
        assert step["in_pos"] == expected_input and positions(step) == expected_work
        assert step["in_move"] in (-1, 0, 1) and len(step["work"]) == k
        scanned = expected_input if 0 <= expected_input < length else None
        assert step["in_scanned_cell"] == scanned
        raw_reads += scanned is not None
        assert type(step["in_loaded"]) is bool
        if step["in_loaded"]:
            assert scanned is not None
        for h, work in enumerate(step["work"]):
            assert work["move"] in (-1, 0, 1)
            assert work["write"] in ("pass", "load_in", "stage_write")
            waits += work["move"] == 0
            extrema[h][0] = min(extrema[h][0], work["pos"])
            extrema[h][1] = max(extrema[h][1], work["pos"])
        if step["append"] is not None:
            assert step["append"] == {
                "out_idx": append_count, "target_input": tpos(d, b, append_count)}
            append_count += 1
        expected_input += step["in_move"]
        expected_work = tuple(w["pos"] + w["move"] for w in step["work"])
    assert append_count == length
    return {"all_steps_checked": horizon, "appends_checked": append_count,
            "raw_reads_including_transit": raw_reads, "work_waits_checked": waits,
            "work_position_ranges": extrema, "safe_total_time_factor": time_factor}


def first_half_profiles(trace):
    """Check the closed-form counter profile at every actual forward scale.

    Anchors are the written allocation formulas, not a regenerated schedule.
    The first active visit at the anchor identifies the loop independently of
    its proposed duration. Subsequent positions and moves must match exactly.
    """
    schedule_id, length = trace["id"], trace["L"]
    if schedule_id == "c5_comb_fanout":
        return []  # This constructor has no variable-speed first-half loop.
    depth = trace["d"].bit_length() - 2
    steps, result, previous_end = trace["steps"], [], 0
    for r in range(1, depth + 1):
        m = length >> r
        if schedule_id in ("c1_torus_cascade", "c2_bfly_cascade"):
            seed = (5 if schedule_id.startswith("c1_") else 1) * (length + 4)
            anchor = (seed + 2 * length - 4 * m + 4 * (r - 1),
                      seed + 3 * length - 6 * m + 6 * (r - 1))
        elif schedule_id == "c3_ten_entry_cascade":
            anchor = (3 * length - 4 * m, 3 * length - 4 * m + 4 * r - 4,
                      length - 2 * m)
        else:
            anchor = (4 * length - 6 * m + 4 * r - 2,
                      3 * length - 4 * m + 4 * r - 2,
                      3 * length - 6 * m + 4 * r - 4)
        candidates = [t for t in range(previous_end, len(steps))
                      if positions(steps[t]) == anchor
                      and steps[t]["work"][1]["write"] == "stage_write"
                      and tuple(w["move"] for w in steps[t]["work"]) == (1, 1) + (0,) * (trace["k"] - 2)]
        assert candidates, (schedule_id, r, "missing first-half anchor")
        start = candidates[0]
        a, last = m // 3, m + m // 3 - 2

        def expected(t):
            return (anchor[0] + min(t, m - 1),
                    anchor[1] + min(m - 1, max((t + 1) // 2, t - a + 1))) + anchor[2:]

        for t in range(last + 1):
            assert positions(steps[start + t]) == expected(t), (schedule_id, r, t)
            if t < last:
                assert tuple(w["move"] for w in steps[start + t]["work"]) == tuple(
                    y - x for x, y in zip(expected(t), expected(t + 1)))
        terminal_event = schedule_id == "c4_no_overwrite_cascade"
        if terminal_event:
            assert all(w["move"] == 0 for w in steps[start + last]["work"])
        previous_end = start + last + int(terminal_event)
        result.append({"depth": r, "M": m, "start": start,
                       "loop_events": last + int(terminal_event),
                       "terminal_stationary_event": terminal_event,
                       "closed_form_configurations_checked": last + 1})
    return result


def first_torus_shift(trace):
    """The first C1 row shift: exact row durations and integer affine error."""
    if trace["id"] != "c1_torus_cascade":
        return None
    d, b, length = trace["d"], trace["b"], trace["L"]
    width = d * b
    scale = max(d // 16, 1)
    v = max((16 - ((3 * scale + 1) % 16) + 1) % d, 1)
    assert 0 < v < d
    tmp = length + 4
    start = length + max(abs(v * b - (length - 1)), abs(tmp - (length - 1)))
    duration = 3 * length - width - 1
    steps = trace["steps"]
    for row in range(d):
        assert positions(steps[start + 3 * row * width]) == (row * width + v * b, tmp + row * width)
    endpoint = ((d - 1) * width + v * b - 1, tmp + length - 1)
    assert positions(steps[start + duration]) == endpoint
    deviations = [0, 0]
    origin = (v * b, tmp)
    for t in range(3 * length + 1):
        p = positions(steps[start + t]) if t < duration else endpoint
        for h in range(2):
            deviations[h] = max(deviations[h], abs(3 * (p[h] - origin[h]) - t))
    bounds = [3 * (2 * width + 2), 3 * (width + 2)]
    assert all(x <= y for x, y in zip(deviations, bounds))
    return {"start": start, "v": v, "row_width": width, "rows_checked": d,
            "nonfinal_row_ticks": 3 * width, "final_row_ticks": 2 * width - 1,
            "phase_ticks": duration, "affine_error_numerators": deviations,
            "affine_error_numerator_bounds": bounds,
            "note": "Finite row-shift calibration; d=16 is below eventual parameter stabilization at d>=256."}


def rejection_controls(trace):
    results = []
    for mutation in ("wrong_initial_position", "nonunit_move", "wrong_transpose_target"):
        bad = deepcopy(trace)
        if mutation == "wrong_initial_position":
            bad["steps"][0]["in_pos"] = 1
        elif mutation == "nonunit_move":
            bad["steps"][0]["work"][0]["move"] = 2
        else:
            first = next(s for s in bad["steps"] if s["append"] is not None)
            first["append"]["target_input"] += 1
        try:
            validate_trace(bad, trace["id"], trace["k"], 256)
        except AssertionError:
            results.append({"mutation": mutation, "rejected": True})
        else:
            raise AssertionError("malformed export accepted: " + mutation)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=DEFAULT_REPO)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--keep-exports", type=Path)
    args = parser.parse_args()
    if not __debug__:
        parser.error("run without -O: these controls require assertions")
    source_check = verify(args.repo)
    if args.keep_exports:
        args.keep_exports.mkdir(parents=True, exist_ok=True)
    tests = []
    with tempfile.TemporaryDirectory(prefix="cascade-calibration-") as temp:
        target = Path(temp) / "target"
        subprocess.run(["cargo", "build", "--quiet", "--release", "--offline", "--locked",
                        "--manifest-path", str(args.repo / CRATE / "Cargo.toml"),
                        "--target-dir", str(target)], check=True)
        binary = target / "release" / "paper16-experiments"
        for schedule_id, k, factor in CASES:
            for b in (1, 4):
                original = subprocess.run([str(binary), "export", schedule_id, "16", str(b), "json"],
                                          check=True, stdout=subprocess.PIPE).stdout
                trace = json.loads(original)
                report = {"id": schedule_id, "d": 16, "b": b, "L": trace["L"],
                          "export_sha256": hashlib.sha256(original).hexdigest(),
                          **validate_trace(trace, schedule_id, k, factor),
                          "first_half_profiles": first_half_profiles(trace),
                          "first_torus_shift": first_torus_shift(trace)}
                tests.append(report)
                if len(tests) == 1:
                    mutations = rejection_controls(trace)
                if args.keep_exports:
                    (args.keep_exports / f"{schedule_id}-d16-b{b}.json").write_bytes(original)
    report = {
        "status": "PASS", "scope": "Finite geometry calibration against original crate exports",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "source_commit": source_check["source_commit"],
        "manifest_sha256": hashlib.sha256(MANIFEST.read_bytes()).hexdigest(),
        "tests": tests, "mutation_controls": mutations,
        "total_original_steps_checked": sum(t["all_steps_checked"] for t in tests),
        "limits": ["No asymptotic regularity, correctness-set bound, or constant is inferred from these cases.",
                   "Geometry-only exports do not specify a transposing computation.",
                   "The tests do not compute Menger cuts, validate all stage budgets, or prove any limit.",
                   "Write tags identify existing loops only; arbitrary-update scope comes from the written proof."],
    }
    text = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
        print(f"PASS: {len(tests)} original exports; {report['total_original_steps_checked']} steps")
    else:
        print(text, end="")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Finite independent controls for the oblivious 3b lane lift.

Usage (from the memo directory):
    python3 tools/lane_lift_control.py --output verification/lane-lift-control.json
Omit --output to write JSON to stdout. Requires only Python's standard library.

The reference executes separate macro machines. The other interpreter executes
all genuine unit transitions on block-encoded tapes. Neither imports the Rust
crate or any earlier simulator. These tests calibrate the implementation; they
do not prove the asymptotic cascade exclusion. See tools/README.md.
"""

from dataclasses import dataclass
from hashlib import sha256
from itertools import product
from pathlib import Path
import json
import argparse


@dataclass(frozen=True)
class Step:
    moves: tuple  # input first, then one entry per work head
    gate: str
    append: bool = False


@dataclass(frozen=True)
class Program:
    name: str
    n: int
    tapes: int
    states: int
    initial: int
    steps: tuple


def transition(program, t, state, raw, old):
    """The declared macro gate: all results use the same old tuple."""
    step = program.steps[t]
    if step.gate == "load":
        assert raw in (0, 1)
        return state, (raw,), None
    if step.gate == "emit":
        return state, old, old[0]
    if step.gate == "pass":
        return state, old, None
    assert step.gate == "nonlinear"
    a, c = old
    s0, s1 = state & 1, state >> 1
    outside = int(raw is None)
    r = 0 if raw is None else raw
    new0 = s1 ^ (a & c) ^ (outside & s0)
    new1 = s0 ^ (r & (1 ^ c)) ^ outside
    w0 = c ^ (s0 & r) ^ ((a | r) & s1)
    w1 = a ^ ((s0 ^ c) & (r ^ s1)) ^ outside
    out = s0 ^ a ^ (c & (r ^ s1)) ^ outside ^ (t & 1)
    return new0 | (new1 << 1), (w0, w1), out if step.append else None


def literal_transpose():
    # Load four input cells.  Then actually walk to output cells0,2,1,3.
    steps = [Step((1, 1 if t < 3 else 0), "load") for t in range(4)]
    steps += [Step((0, -1), "pass") for _ in range(3)]
    steps += [Step((0, 1), "emit", True), Step((0, 1), "pass"),
              Step((0, -1), "emit", True), Step((0, 1), "emit", True),
              Step((0, 1), "pass"), Step((0, 0), "emit", True)]
    return Program("literal_d2_transpose", 4, 1, 1, 0, tuple(steps))


def nonlinear_program():
    # Raw positions include -1,3,4 for a length3 input.  Work moves contain
    # left/right/stay and negative cells; the controller has two real bits.
    raw_moves = (-1, 1, 1, 1, 1, 1, -1, -1, 0, -1, -1, -1, 0, 1)
    work_moves = ((1, -1), (0, 1), (-1, 0), (-1, 1), (1, 0), (1, -1),
                  (0, -1), (-1, 1), (1, 1), (0, -1), (-1, 0), (1, 1),
                  (0, -1), (0, 0))
    steps = tuple(Step((r,) + w, "nonlinear", t in (2, 5, 8, 11, 13))
                  for t, (r, w) in enumerate(zip(raw_moves, work_moves)))
    return Program("stateful_nonlinear_exterior_reads", 3, 2, 4, 2, steps)


def nonzero(tape):
    return {p: value for p, value in tape.items() if value != 0}


def macro_reference(program, bits):
    """Ordinary independent machine; there is no block or lane arithmetic."""
    heads = [0] * (program.tapes + 1)
    tapes = [{} for _ in range(program.tapes)]
    state, output, frames = program.initial, [], []
    for t, step in enumerate(program.steps):
        raw = bits[heads[0]] if 0 <= heads[0] < program.n else None
        old = tuple(tapes[h].get(heads[h + 1], 0) for h in range(program.tapes))
        next_state, writes, emitted = transition(program, t, state, raw, old)
        assert (emitted is not None) == step.append
        for h in range(program.tapes):
            tapes[h][heads[h + 1]] = writes[h]
        state = next_state
        if emitted is not None:
            output.append(emitted)
        heads = [p + delta for p, delta in zip(heads, step.moves)]
        frames.append((state, tuple(heads), tuple(nonzero(x) for x in tapes),
                       tuple(output)))
    return frames


def compile_public_clock(program, b):
    """Compile all micro moves solely from the fixed original head word."""
    macro_heads = [0] * (program.tapes + 1)
    micro_heads = [0] * (program.tapes + 1)
    clock, macro_starts = [], []
    for t, step in enumerate(program.steps):
        macro_starts.append(tuple(macro_heads))
        assert micro_heads == [b * p for p in macro_heads]
        for lane in range(b):
            moves = tuple([int(lane + 1 < b)] * len(micro_heads))
            clock.append(("process", t, lane, moves))
            micro_heads = [p + delta for p, delta in zip(micro_heads, moves)]
        target = [b * (p + delta) for p, delta in zip(macro_heads, step.moves)]
        for _ in range(2 * b):
            moves = tuple((q > p) - (q < p) for p, q in zip(micro_heads, target))
            clock.append(("reposition", t, -1, moves))
            micro_heads = [p + delta for p, delta in zip(micro_heads, moves)]
        macro_heads = [p + delta for p, delta in zip(macro_heads, step.moves)]
        assert micro_heads == target == [b * p for p in macro_heads]
    assert len(clock) == 3 * b * len(program.steps)
    # Exact integer check at every tick; the discrepancy is affine between
    # these ticks, so endpoint bounds also cover interpolated real times.
    heads = [0] * (program.tapes + 1)
    max_error_numerator = 0
    for u in range(len(clock) + 1):
        t, remainder = divmod(u, 3 * b)
        original = macro_starts[t] if t < len(program.steps) else tuple(macro_heads)
        delta = program.steps[t].moves if t < len(program.steps) else (0,) * len(heads)
        for p, old_p, dp in zip(heads, original, delta):
            err = abs(3 * p - 3 * b * old_p - remainder * dp)
            assert err <= 9 * b
            max_error_numerator = max(max_error_numerator, err)
        if u < len(clock):
            heads = [p + delta for p, delta in zip(heads, clock[u][3])]
    return clock, max_error_numerator


def unit_step_lift(program, b, bits, clock, references, mutant=None):
    """Execute every physical tick, including actual reposition reads/writes."""
    heads = [0] * (program.tapes + 1)
    tapes = [{} for _ in range(program.tapes)]
    controllers = [program.initial] * b
    output = []
    stats = {"processing_ticks": 0, "reposition_ticks": 0,
             "negative_raw_reads": 0, "right_exterior_raw_reads": 0,
             "reposition_raw_ones": 0, "reposition_work_ones": 0}
    for u, (kind, t, lane, moves) in enumerate(clock):
        raw = bits[heads[0]] if 0 <= heads[0] < len(bits) else None
        old_work = tuple(tapes[h].get(heads[h + 1], 0) for h in range(program.tapes))
        old_control = tuple(controllers)
        stats["negative_raw_reads"] += int(heads[0] < 0)
        stats["right_exterior_raw_reads"] += int(heads[0] >= len(bits))
        if kind == "process":
            stats["processing_ticks"] += 1
            source_lane = 0 if mutant == "shared_controller" else lane
            new_state, writes, emitted = transition(
                program, t, old_control[source_lane], raw, old_work)
            if mutant == "sequential_work_writes" and program.tapes == 2:
                _, wrong_writes, _ = transition(
                    program, t, old_control[source_lane], raw, (writes[0], old_work[1]))
                writes = (writes[0], wrong_writes[1])
            controllers[lane] = new_state
            assert (emitted is not None) == program.steps[t].append
        else:
            stats["reposition_ticks"] += 1
            stats["reposition_raw_ones"] += int(raw == 1)
            stats["reposition_work_ones"] += sum(old_work)
            writes, emitted = old_work, None
            if mutant == "reposition_read_feedback" and raw == 1:
                controllers[0] ^= 1
            if mutant is None:
                assert tuple(controllers) == old_control
                assert writes == old_work
        assert all(x in (0, 1) for x in writes)
        assert all(0 <= s < program.states for s in controllers)
        # Simultaneous fields from the same immutable pre-step tuple.
        for h, value in enumerate(writes):
            tapes[h][heads[h + 1]] = value
        if emitted is not None:
            output.append(emitted)
        assert all(delta in (-1, 0, 1) for delta in moves)
        heads = [p + delta for p, delta in zip(heads, moves)]
        if (u + 1) % (3 * b) == 0:
            frame = [reference[t] for reference in references]
            assert controllers == [x[0] for x in frame], "lane controller mismatch"
            assert heads == [b * p for p in frame[0][1]], "macro head mismatch"
            for h in range(program.tapes):
                expected = {b * p + ell: value for ell in range(b)
                            for p, value in frame[ell][2][h].items()}
                assert nonzero(tapes[h]) == expected, "expanded work tape mismatch"
            expected_out = [frame[ell][3][j] for j in range(len(frame[0][3]))
                            for ell in range(b)]
            assert output == expected_out, "append order mismatch"
    return output, tuple(controllers), stats


def exhaustive(program, b):
    clock, max_motion_error = compile_public_clock(program, b)
    aggregate = {}
    digest = sha256()
    count = 0
    for bits in product((0, 1), repeat=b * program.n):
        references = [macro_reference(program, bits[ell::b]) for ell in range(b)]
        output, controllers, stats = unit_step_lift(program, b, bits, clock, references)
        if program.name == "literal_d2_transpose":
            expected = [bits[p * b + ell] for p in (0, 2, 1, 3) for ell in range(b)]
            assert output == expected, "literal transpose failed"
        for key, value in stats.items():
            aggregate[key] = aggregate.get(key, 0) + value
        digest.update(bytes(bits) + bytes(output) + bytes(controllers))
        count += 1
    state_bound = (len(clock) + 1) * program.states ** b
    q = (program.states - 1).bit_length()
    bit_bound = b * q + len(clock).bit_length()
    assert (state_bound - 1).bit_length() <= bit_bound
    return {"program": program.name, "lane_width": b, "source_length": program.n,
            "canonical_length": b * program.n, "exhaustive_inputs": count,
            "macro_steps": len(program.steps), "unit_steps_per_input": len(clock),
            "work_tapes": program.tapes, "work_alphabet_size": 2,
            "original_controller_values": program.states,
            "lifted_state_count_bound": state_bound,
            "lifted_controller_bit_bound": bit_bound,
            "motion_error_numerator_max": max_motion_error,
            "motion_error_numerator_bound": 9 * b,
            "all_macro_boundaries_match": True,
            "all_unit_moves_and_simultaneous_fields_checked": True,
            "output_and_final_controller_digest": digest.hexdigest(),
            "aggregate_actual_read_counts": aggregate,
            "public_clock_sha256": sha256(json.dumps(clock).encode()).hexdigest()}


def rejected_mutants(program):
    b = 2
    clock, _ = compile_public_clock(program, b)
    results = []
    for mutant in ("shared_controller", "sequential_work_writes", "reposition_read_feedback"):
        for bits in product((0, 1), repeat=b * program.n):
            references = [macro_reference(program, bits[ell::b]) for ell in range(b)]
            try:
                unit_step_lift(program, b, bits, clock, references, mutant)
            except AssertionError as error:
                results.append({"mutant": mutant, "rejected": True,
                                "input": list(bits), "reason": str(error)})
                break
        else:
            raise AssertionError("Control failed to detect mutant: " + mutant)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="write deterministic JSON here")
    args = parser.parse_args()
    if not __debug__:
        parser.error("run without -O: these controls require assertions")
    programs = (literal_transpose(), nonlinear_program())
    tests = [exhaustive(program, b) for program in programs for b in (2, 3)]
    nonlinear_tests = [x for x in tests if x["program"] == programs[1].name]
    for test in nonlinear_tests:
        counts = test["aggregate_actual_read_counts"]
        assert all(counts[key] > 0 for key in ("negative_raw_reads", "right_exterior_raw_reads",
                                              "reposition_raw_ones", "reposition_work_ones"))
    report = {
        "status": "PASS", "scope": "Finite lane-lift calibration; no cascade computation is simulated",
        "script_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "tests": tests, "mutation_controls": rejected_mutants(programs[1]),
        "total_exhaustive_inputs": sum(x["exhaustive_inputs"] for x in tests),
        "total_executed_unit_steps": sum(x["exhaustive_inputs"] * x["unit_steps_per_input"]
                                         for x in tests),
        "limits": ["Finite tests support the implementation, not a uniform proof.",
                   "Lane widths 2 and 3 at d=2 are controls, not the canonical b=log2(d).",
                   "The literal transpose control is exact on all inputs.",
                   "The nonlinear control checks simulation, not transposition.",
                   "No new reduction or novelty claim; no solver or schedule-size screen."]}
    text = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
        print("PASS: 4,928 inputs; 569,088 unit transitions; three wrong interpreters rejected")
    else:
        print(text, end="")


if __name__ == "__main__":
    main()

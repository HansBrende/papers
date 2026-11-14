#!/usr/bin/env python3
"""Exact existing-host controls for two-sided whole-row codes.

The cyclic lower formulas are checked as integer coefficient identities,
so these finite controls work over every abelian alphabet, not just a
sample of fields. The written proof covers every d>=2; this script checks
d=2,5, the saved basis-eight certificate, and the existing Fano lane code.
Standard library only; no optimizer, host search, file writes, or Lean claim.
"""

from collections import Counter
from contextlib import redirect_stdout
from fractions import Fraction
import importlib.util
import io
import json
from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parents[2]


def cyclic(d):
    assert d in (2, 5)
    parameters = [(i, j) for i in range(d) for j in range(i, d)] + ["t"]
    basis = {key: tuple(int(i == j) for i in range(len(parameters)))
             for j, key in enumerate(parameters)}

    def combine(*terms):
        return tuple(sum(a * v[i] for a, v in terms)
                     for i in range(len(parameters)))

    word = {(i, j): combine((1, basis[min(i, j), max(i, j)]),
                           (int(i < j), basis["t"]))
            for i in range(d) for j in range(d)}
    rho = [{r, (r + 1) % d} for r in range(d)]
    identities = 0
    for (i, j), value in word.items():
        sign = int(i < j) - int(i > j)
        for axis, r in ((0, j), (1, i)):
            low, high = sorted(rho[r])
            terms = [(1, (j, i)), (sign, (low, high)),
                     (-sign, (high, low))]
            assert all(cell[axis] in rho[r] for _, cell in terms)
            assert value == combine(*((a, word[cell]) for a, cell in terms))
            identities += 1
    for i in range(d):
        for j in range(i, d):
            assert word[j, i] == basis[i, j]
    assert combine((1, word[0, 1]), (-1, word[1, 0])) == basis["t"]

    rows = [{(r, c) for c in range(d)} for r in range(d)]
    columns = [{(r, c) for r in range(d)} for c in range(d)]
    seed = {(i, j) for i in range(d) for j in range(i, d)} | {(1, 0)}
    known = set(seed)
    steps = []

    def recover(kind, r):
        helper_blocks = rows if kind == "column" else columns
        helpers = set().union(*(helper_blocks[s] for s in rho[r]))
        target = columns[r] if kind == "column" else rows[r]
        assert helpers <= known
        added = target - known
        known.update(target)
        steps.append({"target": kind, "index": r, "new_cells": len(added)})

    assert rows[0] | rows[1] <= known
    recover("column", 0)
    assert columns[d - 1] <= known
    recover("row", d - 1)
    for r in range(d - 2, 1, -1):
        assert columns[r] <= known  # Upper cells and already recovered rows.
        recover("row", r)
    assert known == set(word)
    assert len(seed) == len(parameters) == d * (d + 1) // 2 + 1
    return {
        "d": d, "rho": [sorted(h) for h in rho],
        "two_sided_recovery_integer_identities": identities,
        "parameter_extraction_integer_identities": len(parameters),
        "upper_generator_cells": sorted(seed), "closure_steps": steps,
        "exact_all_alphabet_exponent_and_Shannon_value": len(seed),
    }


def basis_eight():
    directory = ROOT / "lean-backlog/tools/diagonal-calibration"
    case = next(case for case in json.loads((directory / "receipt.json").read_text())
                if case["d"] == 8)
    spec = importlib.util.spec_from_file_location(
        "existing_shannon_certificates", directory / "shannon_certificates.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    upper = module.verify(case)
    d, T = case["d"], case["T"]
    rho = [{c ^ t for t in T} for c in range(d)]
    assert all((p in rho[c]) == (c in rho[p])
               for p in range(d) for c in range(d))
    blocks, free = [], set()
    for diagonal in case["diagonals"]:
        g = diagonal["g"]
        if diagonal["kind"] == "loops":
            free.update((i, i ^ g) for i in range(d))
        else:
            blocks.extend(frozenset((i, i ^ g) for i in part)
                          for part in diagonal["parts"])
    for p, c in free:
        assert p in rho[c] and c in rho[p]
    for block in blocks:
        for p, c in block:
            for q, m in block - {(p, c)}:
                assert q in rho[c]  # Column c from rows rho(c).
                assert m in rho[p]  # Row p from columns rho(p).
    covered = free | set().union(*blocks)
    assert len(covered) == d * d
    assert sum(map(len, blocks)) + len(free) == len(covered)
    assert frozenset((c, p) for p, c in free) == frozenset(free)
    assert {frozenset((c, p) for p, c in block) for block in blocks} == set(blocks)
    sizes = Counter(map(len, blocks))
    dimension = len(free) + sum(len(block) - 1 for block in blocks)
    assert (len(free), sizes[2], sizes[4], dimension) == (24, 16, 2, 46)
    assert upper["complement_cells"] == dimension
    return {
        "d": d, "T": T, "free_cells": len(free),
        "pair_checks": sizes[2], "K4_checks": sizes[4],
        "two_sided_all_alphabet_exponent_and_Shannon_value": dimension,
        "row_order": upper["row_order"],
        "acyclic_cells": upper["acyclic_cells"],
        "transpose_invariant_partition": True,
        "construction": "Free symbols and sum-zero checks over any finite abelian group.",
    }


def fano():
    verifier = ROOT / "lean-backlog/tools/fano-shannon/verify_certificate.py"
    with redirect_stdout(io.StringIO()):
        data = runpy.run_path(str(verifier))
    rho, cells, triangles = data["lines"], data["cells"], data["triangles"]
    assert all((p in rho[c]) == (c in rho[p])
               for p in range(7) for c in range(7))
    counts = [0] * len(cells)
    for mask in triangles:
        block = [i for i in range(len(cells)) if mask >> i & 1]
        assert len(block) == 3
        for i in block:
            p, c = cells[i]
            counts[i] += 1
            for j in block:
                if i != j:
                    q, m = cells[j]
                    assert q in rho[c] and m in rho[p]
    assert counts == [3] * 28 and len(triangles) == 28
    assert data["rhs_total"] == Fraction(56, 3)
    for p in range(7):
        for c in range(7):
            if p in rho[c]:
                assert c in rho[p]
    return {
        "d": 7, "incident_free_cells": 21,
        "residual_cells": 28, "triangles": 28, "lanes": 3,
        "residual_base_alphabet_exponent": 56,
        "full_base_alphabet_exponent": 119,
        "normalized_two_sided_Shannon_value": "119/3",
        "attainment": "Every q>=2 gives q^119 full words in three lanes over Z/qZ; "
                     "scalar cell alphabet Q=q^3 attains Q^(119/3).",
        "not_claimed": "Scalar attainment of q^(119/3) for every fixed alphabet q.",
    }


def main():
    print(json.dumps({
        "status": "PASS", "cyclic": [cyclic(2), cyclic(5)],
        "basis": basis_eight(), "Fano": fano(),
        "scope": "Exact integer identities, helper support and existing Shannon "
                 "certificates; no optimizer or host search.",
    }, indent=2))


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O: this certificate uses assertions.")
    main()

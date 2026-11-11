#!/usr/bin/env python3
"""Searches for large acyclic sets in one-class relations (the numbers at the end of the section on sets).

A one-class relation of window w on the positions (c, r) of a d x d matrix has maps i_m, j_m on Z/d and
the helpers (i_m(r), c + j_m(r)).  A storage code over q symbols has at most q^(d^2 - |A|) elements for
every set A of positions without a directed cycle of the helper relation.

Usage (needs OR-tools: pip install ortools):
  python3 acyclic_set_search.py large SECONDS d w [d w ...]
      For each (d, w): the largest acyclic set that CP-SAT finds in SECONDS for five families.  These are
      results of a search, so they bound the least hitting set from above only.
        zero-off      zero offsets, random permutations as row maps.  Control: an acyclic set of d(d-1)/2
                      positions exists (order of the columns), and the search must reach that value.
        perm+off      alternately a random permutation with zero offset and the identity with random offsets
        affine        maps (a r + b, c + al r + be) with random a != 0, b, al, be
        random        random maps i_m, j_m
        unstructured  every position gets w helpers at random: not a one-class relation
  python3 acyclic_set_search.py pairing SECONDS d k [d k ...]
      The pairing (r, c) plus k helpers with random permutations as row maps and random offset functions.
      Prints a lower and an upper bound on the least number of positions that meets every cycle; they are
      equal when the lazy cover finishes.  The pairing forces at least d(d+1)/2.

  python3 acyclic_set_search.py calibrate SECONDS d w [d w ...]
      A second control for `large`: the pairing plus w - 1 random permutations with zero offsets.  The largest
      acyclic set has exactly d(d-1)/2 positions (at most one of each transposed pair; the positions with
      c > r are acyclic, since every helper of (c, r) lies in column c).  Prints what the search finds.

  python3 acyclic_set_search.py lower SECONDS d w
      For the instances of `large` at the first pair (d, w) of a run: a proved lower bound on the least number
      of positions that meets every cycle, for the three families with spread rows and offsets (the optimum
      of a cover of a growing list of cycles; every such optimum is a lower bound).

The runs quoted in the paper:  large 60 13 12 17 12 17 24 ; large 120 23 12 29 12 ; lower 200 13 12 ;
pairing 60 9 2 9 3 9 5 11 2 11 3 11 5 13 2 13 3 13 5 17 3 17 5 ; calibrate 120 17 12 23 12 29 12
(seed 20261111 in each case).
"""
import random
import sys
import time
from collections import deque

from ortools.sat.python import cp_model

SEED = 20261111


def relation(d, maps):
    return [sorted({i[r] * d + (c + j[r]) % d for (i, j) in maps}) for c in range(d) for r in range(d)]


def shortest_cycles(hs, alive):
    """One shortest cycle through each vertex of the helper digraph restricted to alive."""
    found = set()
    for s in alive:
        par = {s: None}
        queue = deque([s])
        hit = None
        while queue and hit is None:
            u = queue.popleft()
            for v in hs[u]:
                if v == s:
                    hit = u
                    break
                if v in alive and v not in par:
                    par[v] = u
                    queue.append(v)
        if hit is not None:
            cyc = []
            u = hit
            while u is not None:
                cyc.append(u)
                u = par[u]
            found.add(frozenset(cyc))
    return found


def is_acyclic(hs, alive):
    indeg = {v: 0 for v in alive}
    out = {v: [w for w in hs[v] if w in alive] for v in alive}
    for v in alive:
        for w in out[v]:
            indeg[w] += 1
    stack = [v for v in alive if indeg[v] == 0]
    seen = 0
    while stack:
        v = stack.pop()
        seen += 1
        for w in out[v]:
            indeg[w] -= 1
            if indeg[w] == 0:
                stack.append(w)
    return seen == len(alive)


def lazy_cover(hs, limit):
    """Lower bound on the least hitting set of the cycles: optimum of a cover of a growing list of cycles.
    Returns (lower bound, exact value or None)."""
    n = len(hs)
    start = time.time()
    cycles = shortest_cycles(hs, set(range(n)))
    lb = 0
    while True:
        model = cp_model.CpModel()
        x = [model.NewBoolVar(f"x{v}") for v in range(n)]
        for cyc in cycles:
            model.AddBoolOr([x[v] for v in cyc])
        model.Minimize(sum(x))
        solver = cp_model.CpSolver()
        rest = limit - (time.time() - start)
        if rest <= 1:
            return lb, None
        solver.parameters.max_time_in_seconds = rest
        solver.parameters.num_workers = 4
        status = solver.Solve(model)
        if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            lb = max(lb, int(round(solver.BestObjectiveBound() + 1e-6)))
        if status != cp_model.OPTIMAL:
            return lb, None
        alive = {v for v in range(n) if not solver.Value(x[v])}
        if is_acyclic(hs, alive):
            return lb, n - len(alive)
        cycles |= shortest_cycles(hs, alive)


def acyclic_set(hs, limit):
    """Size of an acyclic set found by the ordering model within the time limit."""
    n = len(hs)
    model = cp_model.CpModel()
    keep = [model.NewBoolVar(f"k{v}") for v in range(n)]
    pos = [model.NewIntVar(0, n - 1, f"p{v}") for v in range(n)]
    for v in range(n):
        for u in hs[v]:
            if u == v:
                model.Add(keep[v] == 0)
            else:
                model.Add(pos[u] + 1 <= pos[v]).OnlyEnforceIf([keep[u], keep[v]])
    model.Maximize(sum(keep))
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = limit
    solver.parameters.num_workers = 4
    solver.Solve(model)
    return int(round(solver.ObjectiveValue()))


def family(name, d, w, rng):
    ident, zero = list(range(d)), [0] * d
    if name == "zero-off":
        out = []
        for _ in range(w):
            p = ident[:]
            rng.shuffle(p)
            out.append((p, zero))
        return out
    if name == "perm+off":
        out = []
        for m in range(w):
            if m % 2 == 0:
                p = ident[:]
                rng.shuffle(p)
                out.append((p, zero))
            else:
                out.append((ident, [rng.randrange(d) for _ in range(d)]))
        return out
    if name == "affine":
        out = []
        for _ in range(w):
            a, b, al, be = rng.randrange(1, d), rng.randrange(d), rng.randrange(d), rng.randrange(d)
            out.append(([(a * r + b) % d for r in range(d)], [(al * r + be) % d for r in range(d)]))
        return out
    if name == "random":
        return [([rng.randrange(d) for _ in range(d)], [rng.randrange(d) for _ in range(d)]) for _ in range(w)]
    raise ValueError(name)


def run_large(limit, args):
    rng = random.Random(SEED)
    for d, w in zip(args[0::2], args[1::2]):
        n = d * d
        for name in ("zero-off", "perm+off", "affine", "random", "unstructured"):
            if name == "unstructured":
                hs = [sorted(set(rng.randrange(n) for _ in range(w))) for _ in range(n)]
            else:
                hs = relation(d, family(name, d, w, rng))
            size = acyclic_set(hs, limit)
            print(f"d={d} w={w} {name:12s} acyclic set found {size:4d}   d(d-1)/2 = {d*(d-1)//2}"
                  f"   share of positions {size/n:.3f}", flush=True)


def run_pairing(limit, args):
    rng = random.Random(SEED)
    for d, k in zip(args[0::2], args[1::2]):
        ident, zero = list(range(d)), [0] * d
        maps = [(ident, zero)]
        for _ in range(k):
            p = ident[:]
            rng.shuffle(p)
            maps.append((p, [rng.randrange(d) for _ in range(d)]))
        hs = relation(d, maps)
        lb, exact = lazy_cover(hs, limit)
        ub = exact if exact is not None else d * d - acyclic_set(hs, limit)
        print(f"d={d} window {k+1}: least hitting set in [{lb}, {ub}]   d(d+1)/2 = {d*(d+1)//2}", flush=True)


def run_lower(limit, args):
    d, w = args[0], args[1]
    rng = random.Random(SEED)
    n = d * d
    for name in ("zero-off", "perm+off", "affine", "random"):      # same order of random draws as `large`
        hs = relation(d, family(name, d, w, rng))
        if name == "zero-off":
            continue
        lb, exact = lazy_cover(hs, limit)
        note = "" if exact is None else f" (exact: {exact})"
        print(f"d={d} w={w} {name:9s} every set that meets all cycles has at least {lb} positions{note};"
              f"   d(d+1)/2 = {d*(d+1)//2}", flush=True)


def run_calibrate(limit, args):
    rng = random.Random(SEED)
    for d, w in zip(args[0::2], args[1::2]):
        ident, zero = list(range(d)), [0] * d
        maps = [(ident, zero)]
        for _ in range(w - 1):
            p = ident[:]
            rng.shuffle(p)
            maps.append((p, zero))
        size = acyclic_set(relation(d, maps), limit)
        print(f"d={d} w={w} pairing and zero-offset permutations: acyclic set found {size},"
              f" exact maximum {d*(d-1)//2}", flush=True)


if __name__ == "__main__":
    modes = {"large": run_large, "pairing": run_pairing, "calibrate": run_calibrate, "lower": run_lower}
    if len(sys.argv) < 5 or sys.argv[1] not in modes or len(sys.argv) % 2 == 0:
        sys.exit(__doc__)
    modes[sys.argv[1]](float(sys.argv[2]), [int(a) for a in sys.argv[3:]])

#!/usr/bin/env python3
"""Finite exact controls for row-spread-of-cones.md; not an asymptotic proof.

Run from the repository root:
  python3 lean-backlog/tools/row_spread_controls.py --random-cases 1000

Uses actual pre-transition head positions and every visit, including pauses.
No third-party packages, floating point, or native-machine correctness claim.
"""
from __future__ import annotations

import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import random


def positions(moves: tuple[int, ...] | list[int]) -> list[int]:
    out = [0]
    for move in moves:
        out.append(out[-1] + move)
    return out


def block_count(labels: dict[int, int]) -> int:
    """Count all maximal labelled blocks on Z, with never = -1 outside."""
    if not labels:
        return 1
    lo, hi = min(labels), max(labels)
    prev, count = -1, 1
    for x in range(lo, hi + 2):
        current = labels.get(x, -1)
        if current != prev:
            count += 1
            prev = current
    return count


def window_data(path: list[int], width: int) -> dict:
    assert width >= 1 and path
    assert all(abs(b - a) <= 1 for a, b in zip(path, path[1:]))
    labels: dict[int, int] = {}
    old_visit: dict[int, int] = {}
    counts, predecessors, before_phi, after_phi = [], [], [], []
    last_visit = []
    for i, start in enumerate(range(0, len(path), width)):
        window = path[start:start + width]
        visited = set(window)
        assert len(visited) == max(visited) - min(visited) + 1
        predecessor = {labels[x] for x in visited if x in labels}
        counts.append(len(predecessor))
        predecessors.append(predecessor)
        before_phi.append(block_count(labels))
        # Actual last-visit edges use chronological visits, not last writes.
        for t, x in enumerate(window, start):
            last_visit.append(old_visit.get(x))
            old_visit[x] = t
            labels[x] = i
        after_phi.append(block_count(labels))
        assert after_phi[-1] <= before_phi[-1] - len(predecessor) + 3
    assert sum(counts) <= 3 * len(counts)
    return dict(counts=counts, predecessors=predecessors,
                before_phi=before_phi, after_phi=after_phi, last_visit=last_visit)


def dependency(paths: list[list[int]]) -> list[set[int]]:
    horizon = len(paths[0])
    assert all(len(p) == horizon for p in paths)
    parents = [{t - 1} if t else set() for t in range(horizon)]
    for path in paths:
        last: dict[int, int] = {}
        for t, cell in enumerate(path):
            if cell in last:
                parents[t].add(last[cell])
            last[cell] = t
    return parents


def root_exempt_reach(parents: list[set[int]], cut: set[int]) -> tuple[list[set[int]], int]:
    """All Gamma-free ancestors, including the root even if in Gamma.

    Depth is measured in EDGES, matching full depth in Paper 14.
    """
    reach, height = [], []
    for t, incoming in enumerate(parents):
        live = incoming - cut
        ancestors = {t}
        for u in live:
            ancestors |= reach[u]
        reach.append(ancestors)
        height.append(max((height[u] + 1 for u in live), default=0))
    return reach, max(height)


def bad_window_cut(paths: list[list[int]], width: int, threshold: int) -> tuple[set[int], set[int], list[dict]]:
    data = [window_data(path, width) for path in paths]
    horizon = len(paths[0])
    count = (horizon + width - 1) // width
    bad = {i for i in range(count) if sum(d['counts'][i] for d in data) > threshold}
    cut = set()
    for i in bad:
        start, end = i * width, min(horizon, (i + 1) * width)
        if start:
            cut.add(start - 1)
        for d in data:
            cut |= {u for u in d['last_visit'][start:end] if u is not None and u < start}
    assert len(cut) <= len(bad) * (len(paths) * width + 1)
    assert len(cut) <= len(bad) * (len(paths) + 1) * width
    assert len(bad) * threshold <= sum(sum(d['counts']) for d in data)
    return bad, cut, data


def cone_check(paths: list[list[int]], raw: list[int], width: int, threshold: int,
               cut: set[int], entry_width: int, dimension: int,
               appends: list[int], out_window_threshold: int) -> dict:
    assert width == dimension * entry_width
    assert len(appends) == dimension * width
    assert all(a < b for a, b in zip(appends, appends[1:]))
    horizon = len(raw)
    assert max(appends) < horizon
    assert all(abs(a-b) <= 1 for a, b in zip(raw, raw[1:]))
    bad, extra, data = bad_window_cut(paths, width, threshold)
    parents = dependency(paths)
    original_reach, original_depth = root_exempt_reach(parents, cut)
    reach, depth = root_exempt_reach(parents, cut | extra)
    assert depth <= original_depth
    count = (horizon + width - 1) // width
    max_reached_windows = 0
    for t, incoming in enumerate(parents):
        i = t // width
        known = {i}
        if i:
            known.add(i-1)
        for d in data:
            known |= d['predecessors'][i]
        assert {u // width for u in incoming} <= known
        if i in bad:
            assert all(u // width == i for u in incoming - extra)
            assert all(u // width == i for u in reach[t])
        # Count reachable windows directly; no reconstruction from a quotient.
        reached = {u // width for u in reach[t]}
        max_reached_windows = max(max_reached_windows, len(reached))
        assert len(reached) <= (threshold + 2) ** original_depth
    for i in range(count):
        rows = {x // width for x in raw[i*width:(i+1)*width]
                if 0 <= x < dimension * width}
        assert len(rows) <= 2
    bad_rows, max_row_spread, boundaries = [], 0, set()
    for row in range(dimension):
        events = appends[row*width:(row+1)*width]
        first, last = events[0] // width, events[-1] // width
        interval_windows = last - first + 1
        crossed = set(range(first + 1, last + 1))
        assert boundaries.isdisjoint(crossed)
        boundaries |= crossed
        if interval_windows > out_window_threshold + 1:
            bad_rows.append(row)
            continue
        rows = {raw[u] // width for t in events for u in reach[t]
                if 0 <= raw[u] < dimension * width}
        max_row_spread = max(max_row_spread, len(rows))
        assert len(rows) <= 2 * (out_window_threshold + 1) * (threshold + 2) ** original_depth
    assert len(bad_rows) * out_window_threshold <= count
    return dict(windows=count, bad_windows=len(bad), extra_cut=len(extra-cut),
                original_depth=original_depth, enlarged_depth=depth,
                bad_rows=len(bad_rows), max_row_spread=max_row_spread,
                max_reached_windows=max_reached_windows)


def block_reversal_control(side: int, entry_width: int = 1) -> dict:
    """A unit-speed raw/output skeleton; direct root reads survive every genie.

    It copies rows in a blockwise reversed order, not matrix transpose.
    A fixed-state implementation is discussed separately in the proof note.
    """
    dimension = side*side
    width = dimension*entry_width
    length = dimension*width
    f = [(r//side)*side + side-1-r % side for r in range(dimension)]
    raw, appends, x = [], [], 0
    for r in range(dimension):
        target = f[r]*width
        while x != target:
            raw.append(x)
            x += 1 if x < target else -1
        for _ in range(width):
            appends.append(len(raw))
            raw.append(x)
            x += 1
    assert len(raw) == (5*side*side-5*side+1)*width
    assert len(raw) <= 5*length
    assert len(appends) == length
    assert raw[0] == 0
    assert all(abs(b-a) <= 1 for a,b in zip(raw,raw[1:]))
    edges = []
    for r in range(dimension):
        for c in range(dimension):
            for lane in range(entry_width):
                output = r*width+c*entry_width+lane
                source = raw[appends[output]]
                demand = c*width+r*entry_width+lane
                assert source == f[r]*width+c*entry_width+lane
                edges.append((source,demand))
    assert len({p for p,q in edges}) == length
    assert len({q for p,q in edges}) == length
    inc, dec = [], []
    for j in range(dimension):
        inc.append(1+max((inc[i] for i in range(j) if f[i] < f[j]),default=0))
        dec.append(1+max((dec[i] for i in range(j) if f[i] > f[j]),default=0))
    assert max(inc) == max(dec) == side
    return dict(side=side, dimension=dimension, entry_width=entry_width,
                input_length=length, ticks=len(raw), lis=max(inc), lds=max(dec),
                matching_edges=len(edges), direct_root_row_spread=1,
                note='Time-indexed geometric control; root reads alone use exactly one helper row.')


def band_word_controls(rng: random.Random, count: int = 100) -> dict:
    """Check offset decomposition, including gaps and varying domains."""
    branches_checked = 0
    for _ in range(count):
        maps_count, radius = rng.randint(0, 3), rng.randint(0, 2)
        interval = list(range(-4, 8))
        maps, bands, signs = [], [], []
        for j in range(maps_count+1):
            bands.append({(x,y) for x in interval for y in interval
                          if abs(x-y) <= radius and rng.randrange(4)})
            if j < maps_count:
                size = rng.randint(0,len(interval))
                domain = sorted(rng.sample(interval,size))
                target = sorted(rng.sample(interval,size))
                sign = rng.choice((-1,1))
                if sign < 0:
                    target.reverse()
                maps.append(dict(zip(domain,target)))
                signs.append(sign)
        actual = set()
        for start in interval:
            current = {start}
            for j in range(maps_count+1):
                current = {y for x,y in bands[j] if x in current}
                if j < maps_count:
                    current = {maps[j][x] for x in current if x in maps[j]}
            actual |= {(start,end) for end in current}
        decomposed = set()
        for offsets in product(range(-radius,radius+1),repeat=maps_count+1):
            branch = []
            for start in interval:
                current = start
                for j, offset in enumerate(offsets):
                    end = current+offset
                    if (current,end) not in bands[j]:
                        break
                    current = end
                    if j < maps_count:
                        if current not in maps[j]:
                            break
                        current = maps[j][current]
                else:
                    branch.append((start,current))
            sign = 1
            for s in signs:
                sign *= s
            assert all(sign*(v2-v1)>0 for (_,v1),(_,v2) in zip(branch,branch[1:]))
            decomposed |= set(branch)
            branches_checked += 1
        assert actual == decomposed
    return dict(words=count, offset_branches=branches_checked,
                result='Exact decomposition into monotone partial injections passed.')


def run(exhaustive_length: int, random_cases: int, seed: int) -> dict:
    rng = random.Random(seed)
    exhaustive = 0
    best = (0, 1, None)
    for horizon in range(1, exhaustive_length+1):
        for moves in product((-1, 0, 1), repeat=horizon-1):
            path = positions(moves)
            for width in range(1, min(horizon, 6)+1):
                data = window_data(path, width)
                total, count = sum(data['counts']), len(data['counts'])
                if total * best[1] > best[0] * count:
                    best = total, count, dict(path=path, width=width, counts=data['counts'])
                exhaustive += 1
    case_summaries = []
    totals = Counter()
    for case in range(random_cases):
        dimension = rng.randint(1, 9)
        entry_width = rng.randint(1, 3)
        width = dimension * entry_width
        length = dimension * width
        horizon = rng.randint(length, 3*length+3)
        tapes = rng.randint(1, 3)
        paths = [positions([rng.choice((-1, 0, 1)) for _ in range(horizon-1)])
                 for _ in range(tapes)]
        # Modes cover monotone/raw archives, long pauses, reversals and random walks.
        mode = case % 4
        if mode == 0:
            raw = [min(t, length-1) for t in range(horizon)]
        elif mode == 1:
            radius = max(1, length-1)
            raw = [min(t % (2*radius), 2*radius-t % (2*radius)) for t in range(horizon)]
        elif mode == 2:
            raw = positions([rng.choice((-1, 0, 1)) for _ in range(horizon-1)])
        else:
            raw = [min(t, 2*length-2-t) if t <= 2*length-2 else 0
                   for t in range(horizon)] if length > 1 else [0]*horizon
        appends = sorted(rng.sample(range(horizon), length))
        threshold = rng.randint(0, 5)
        out_threshold = rng.randint(1, 5)
        # Root-in-cut and empty-cut cases are intentionally included.
        cut = {t for t in range(horizon) if rng.randrange(4) == 0} if case % 3 else set()
        result = cone_check(paths, raw, width, threshold, cut, entry_width,
                            dimension, appends, out_threshold)
        totals['cone_cases'] += 1
        for name in ('bad_windows','extra_cut','bad_rows'):
            totals[name] += result[name]
        if case < 8:
            case_summaries.append(dict(case=case, dimension=dimension, tapes=tapes, **result))
    named = {}
    for dimension in (3, 5, 9):
        width, length = dimension, dimension*dimension
        archive = list(range(length)) + list(range(length-2, -1, -1)) + list(range(1, length))
        horizon = len(archive)
        raw = [min(t, length-1) for t in range(horizon)]
        append = list(range(horizon-length, horizon))
        # Geometry-only duplicate archives and a parked-input feedback control.
        for threshold in (0, 1, 3):
            key = f'duplicate_archive_d{dimension}_M{threshold}'
            named[key] = cone_check([archive, archive], raw, width, threshold,
                                    set(range(2, horizon, 3)), 1, dimension, append, 2)
        # Sparse output bursts: no assumption that all times between appends append.
        horizon = 5*length
        path = positions([(-1 if (t//width) % 2 else 1) for t in range(horizon-1)])
        raw = [min(t, length-1) for t in range(horizon)]
        append = list(range(0, horizon, 5))
        named[f'sparse_appends_d{dimension}'] = cone_check(
            [path, [0]*horizon], raw, width, 1, set(range(1, horizon, 4)),
            1, dimension, append, 2)
    # Both kinds of entering edge are genuinely needed, even with root exemption.
    witness = [0, 1, 2, 1, 0, -1]
    bad, extra, data = bad_window_cut([witness], 2, 0)
    state_only = {2*i-1 for i in bad if i}
    work_only = {u for i in bad for u in data[0]['last_visit'][2*i:2*i+2]
                 if u is not None and u < 2*i}
    parents = dependency([witness])
    assert 3 in parents[4] - work_only  # omitted state guard lets root 4 leave W_2
    assert 0 in parents[4] - state_only # omitted work guard lets root 4 leave W_2
    assert not (parents[4]-extra)
    negative = dict(path=witness, width=2, threshold=0, bad_windows=sorted(bad),
                    full_guard=sorted(extra), omitted_state_escape=[4,3],
                    omitted_work_escape=[4,0])
    reverse = [block_reversal_control(s,b) for s in (2,3,5,8) for b in (1,2)]
    band_controls = band_word_controls(rng)
    return dict(seed=seed, exhaustive_cases=exhaustive,
                max_sum_m_over_N=dict(numerator=best[0], denominator=best[1], witness=best[2]),
                totals=dict(totals), sample_cases=case_summaries, named_controls=named,
                guard_negative_controls=negative,
                block_reversal_controls=reverse, band_word_controls=band_controls,
                scope='Finite controls only; no asymptotic or machine-correctness inference.')


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--exhaustive-length', type=int, default=9)
    parser.add_argument('--random-cases', type=int, default=2000)
    parser.add_argument('--seed', type=int, default=20261113)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    receipt = run(args.exhaustive_length, args.random_cases, args.seed)
    if args.output:
        args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k:v for k,v in receipt.items()
                      if k not in {'sample_cases', 'named_controls', 'block_reversal_controls'}}, indent=2))


if __name__ == '__main__':
    main()

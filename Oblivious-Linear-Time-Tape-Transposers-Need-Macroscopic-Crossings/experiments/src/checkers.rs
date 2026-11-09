//! Exact dependency-graph checkers reproducing every numerical figure quoted in Paper 16:
//! - Crossing lower steps `CL_H` (`Definition 2.1` / `crossingLowerH`) and exact unit-capacity
//!   vertex-split Dinic minimum vertex cuts (`IsMengerVertexCut`, `Section 5`);
//! - Labeled comparison with Sprint 43's historical `Mix_{>2W}` + non-root separator on Appendix A;
//! - Radius-`D` ball-avoidance relations and certified cycle-packing upper bounds on acyclic sets
//!   at `E = L` (`Remark 5.8`);
//! - Chronologically disjoint expanding waves (`Remark 10.1` / `Proposition 8.3`);
//! - Macroscopic `Lambda`-skeletons, `d`-independence, and single-leg crossing expansion
//!   (`Section 6`, `Remark 6.8`, `Remark 10.1`);
//! - Coarse joint phase profiles `M_ph(floor(2^{-s} L))` (`Section 10.4`) and multi-scale leg counts
//!   (`Problem 11.1`);
//! - One-scale and localized/span-weighted two-scale closed interval-forest charges (`Problem 11.1`).

use std::collections::{HashMap, VecDeque};

use crate::model::{tpos, DepGraph, Revisit, Schedule};

// ============================================================================
// 1. Crossing Lower Steps `CL_H` & Legacy Sprint 43 `Mix_{>2W}` Comparison
// ============================================================================

/// Exact crossing lower-step mask `CL_H` at excursion threshold `exc_thresh = 2 * H`
/// (`Definition 2.1` / `MacroscopicThreshold.crossingLowerH`):
/// `mask[t] == true` iff `t == p` is the earlier endpoint of a revisit `(p, u)` on some work tape `j`
/// with `excursion > exc_thresh` that strictly crosses (`p < p' < u < u'` or `p' < p < u' < u`)
/// another revisit `(p', u')` on the SAME work tape `j` with `excursion > exc_thresh`.
pub fn crossing_lower_steps(dag: &DepGraph, exc_thresh: i64) -> Vec<bool> {
    let mut mask = vec![false; dag.t_len];
    for revs in &dag.revisits_by_tape {
        let mut long_by_p: Vec<(usize, usize)> = revs
            .iter()
            .filter(|r| r.excursion > exc_thresh)
            .map(|r| (r.p, r.u))
            .collect();
        let n = long_by_p.len();
        if n < 2 {
            continue;
        }
        long_by_p.sort_unstable();

        // Segment tree 1 over `long_by_p` (sorted by `p`): range maximum of `u`.
        let cap = n.next_power_of_two();
        let mut max_u_tree = vec![0usize; 2 * cap];
        for (i, &(_p, u)) in long_by_p.iter().enumerate() {
            max_u_tree[cap + i] = u;
        }
        for idx in (1..cap).rev() {
            max_u_tree[idx] = max_u_tree[2 * idx].max(max_u_tree[2 * idx + 1]);
        }
        let query_max_u = |mut l: usize, mut r: usize| -> usize {
            let mut ans = 0usize;
            l += cap;
            r += cap;
            while l < r {
                if (l & 1) == 1 {
                    ans = ans.max(max_u_tree[l]);
                    l += 1;
                }
                if (r & 1) == 1 {
                    r -= 1;
                    ans = ans.max(max_u_tree[r]);
                }
                l >>= 1;
                r >>= 1;
            }
            ans
        };

        // Segment tree 2 over `long_by_u` (sorted by `u`): range minimum of `p`.
        let mut long_by_u = long_by_p.clone();
        long_by_u.sort_unstable_by_key(|&(p, u)| (u, p));
        let mut min_p_tree = vec![usize::MAX; 2 * cap];
        for (i, &(p, _u)) in long_by_u.iter().enumerate() {
            min_p_tree[cap + i] = p;
        }
        for idx in (1..cap).rev() {
            min_p_tree[idx] = min_p_tree[2 * idx].min(min_p_tree[2 * idx + 1]);
        }
        let query_min_p = |mut l: usize, mut r: usize| -> usize {
            let mut ans = usize::MAX;
            l += cap;
            r += cap;
            while l < r {
                if (l & 1) == 1 {
                    ans = ans.min(min_p_tree[l]);
                    l += 1;
                }
                if (r & 1) == 1 {
                    r -= 1;
                    ans = ans.min(min_p_tree[r]);
                }
                l >>= 1;
                r >>= 1;
            }
            ans
        };

        for &(p, u) in &long_by_p {
            // Case 1: exists `(p2, u2)` with `p < p2 < u < u2`
            let lo_p = long_by_p.partition_point(|&(p2, _)| p2 <= p);
            let hi_p = long_by_p.partition_point(|&(p2, _)| p2 < u);
            let crosses_later = lo_p < hi_p && query_max_u(lo_p, hi_p) > u;

            // Case 2: exists `(p2, u2)` with `p2 < p < u2 < u`
            let lo_u = long_by_u.partition_point(|&(_, u2)| u2 <= p);
            let hi_u = long_by_u.partition_point(|&(_, u2)| u2 < u);
            let crosses_earlier = lo_u < hi_u && query_min_p(lo_u, hi_u) < p;

            if crosses_later || crosses_earlier {
                mask[p] = true;
            }
        }
    }
    mask
}

/// Brute-force `O(k * R^2)` reference implementation of `CL_H` for unit-test verification.
pub fn crossing_lower_steps_bruteforce(dag: &DepGraph, exc_thresh: i64) -> Vec<bool> {
    let mut mask = vec![false; dag.t_len];
    for revs in &dag.revisits_by_tape {
        let long: Vec<&Revisit> = revs.iter().filter(|r| r.excursion > exc_thresh).collect();
        for (i, a) in long.iter().enumerate() {
            for (j, b) in long.iter().enumerate() {
                if i != j
                    && ((a.p < b.p && b.p < a.u && a.u < b.u)
                        || (b.p < a.p && a.p < b.u && b.u < a.u))
                {
                    mask[a.p] = true;
                    break;
                }
            }
        }
    }
    mask
}

/// Labeled legacy Sprint 43 `Mix_η` step mask (`NonLifoInBandPU` when `exc_hi < i64::MAX`,
/// `NonLifoGt2WPU` when `exc_hi == i64::MAX`, excluding output-append steps), retained strictly
/// to compare Appendix A's historical probe column against exact `CL_W`.
pub fn legacy_sprint43_mix_band(sched: &Schedule, dag: &DepGraph, exc_hi: i64) -> Vec<bool> {
    let two_w = (2 * sched.d * sched.b) as i64;
    let mut mask = vec![false; dag.t_len];

    #[derive(Clone)]
    struct FamSpan {
        start: usize,
        stop: usize,
        multi_load: bool,
        hops: Vec<(usize, usize)>,
    }

    for (j, revs) in dag.revisits_by_tape.iter().enumerate() {
        let walk = &sched.work_pos[j];
        let mut by_owner: HashMap<(bool, usize), Vec<(usize, usize)>> = HashMap::new();
        for rev in revs {
            if rev.excursion <= two_w || rev.excursion > exc_hi {
                continue;
            }
            let side_up = walk[rev.p + 1] > rev.cell;
            let mut best_d = -1i64;
            let mut owner = rev.p + 1;
            for s in (rev.p + 1)..rev.u {
                let d_cur = if side_up {
                    walk[s] - rev.cell
                } else {
                    rev.cell - walk[s]
                };
                if d_cur > best_d {
                    best_d = d_cur;
                    owner = s;
                }
            }
            by_owner.entry((side_up, owner)).or_default().push((rev.p, rev.u));
        }

        let mut fams: Vec<FamSpan> = Vec::with_capacity(by_owner.len());
        for (_key, mut hops) in by_owner {
            hops.sort_unstable_by_key(|&(_, u)| u);
            let mut multi_load = false;
            for w in hops.windows(2) {
                if !(w[0].1 < w[1].1 && w[0].0 > w[1].0) {
                    multi_load = true;
                }
            }
            let start = hops.iter().map(|h| h.0).min().unwrap();
            let stop = hops.iter().map(|h| h.1).max().unwrap();
            fams.push(FamSpan {
                start,
                stop,
                multi_load,
                hops,
            });
        }

        for (a_idx, fa) in fams.iter().enumerate() {
            let mut non_lifo = fa.multi_load;
            if !non_lifo {
                for (b_idx, fb) in fams.iter().enumerate() {
                    if a_idx == b_idx {
                        continue;
                    }
                    let disjoint = fa.stop <= fb.start || fb.stop <= fa.start;
                    let nested = (fa.start >= fb.start && fa.stop <= fb.stop)
                        || (fb.start >= fa.start && fb.stop <= fa.stop);
                    if !disjoint && !nested {
                        non_lifo = true;
                        break;
                    }
                }
            }
            if non_lifo {
                for &(p, u) in &fa.hops {
                    mask[p] = true;
                    mask[u] = true;
                }
            }
        }
    }

    for &at in &sched.append_times {
        mask[at] = false;
    }
    mask
}

pub fn legacy_sprint43_mix_gt2w(sched: &Schedule, dag: &DepGraph) -> Vec<bool> {
    legacy_sprint43_mix_band(sched, dag, i64::MAX)
}

// ============================================================================
// 2. Unit-Capacity Vertex-Split Dinic Max-Flow (`IsMengerVertexCut`)
// ============================================================================

#[derive(Clone, Copy)]
struct FlowEdge {
    to: u32,
    next: u32,
    cap: u32,
}

/// Flat-CSR, `u32`-indexed, strictly non-recursive Dinic solver.
/// Every edge pair `(2*k, 2*k+1)` stores the forward and reverse arcs (`rev = idx ^ 1`),
/// eliminating both `u16` super-sink degree limits and call-stack recursion on million-step DAGs.
struct Dinic {
    head: Vec<u32>,
    cur: Vec<u32>,
    level: Vec<i32>,
    q: Vec<u32>,
    stack_v: Vec<usize>,
    stack_e: Vec<u32>,
    edges: Vec<FlowEdge>,
}

impl Dinic {
    fn new(n: usize) -> Self {
        Self::with_capacity(n, 3 * n)
    }

    fn with_capacity(n: usize, edge_pairs_hint: usize) -> Self {
        Self {
            head: vec![u32::MAX; n],
            cur: vec![u32::MAX; n],
            level: vec![-1; n],
            q: Vec::with_capacity(n),
            stack_v: Vec::with_capacity(n.min(65536)),
            stack_e: Vec::with_capacity(n.min(65536)),
            edges: Vec::with_capacity(2 * edge_pairs_hint),
        }
    }

    #[inline]
    fn add_edge(&mut self, u: usize, v: usize, cap: u32) -> u32 {
        let idx = self.edges.len() as u32;
        self.edges.push(FlowEdge {
            to: v as u32,
            next: self.head[u],
            cap,
        });
        self.head[u] = idx;
        self.edges.push(FlowEdge {
            to: u as u32,
            next: self.head[v],
            cap: 0,
        });
        self.head[v] = idx + 1;
        idx
    }

    fn bfs(&mut self, src: usize, snk: usize) -> bool {
        self.level.fill(-1);
        self.q.clear();
        self.level[src] = 0;
        self.q.push(src as u32);
        let mut qi = 0usize;
        while qi < self.q.len() {
            let u = self.q[qi] as usize;
            qi += 1;
            if u == snk {
                break;
            }
            let next_lvl = self.level[u] + 1;
            let mut ei = self.head[u];
            while ei != u32::MAX {
                let e = self.edges[ei as usize];
                let w = e.to as usize;
                if e.cap > 0 && self.level[w] < 0 {
                    self.level[w] = next_lvl;
                    self.q.push(w as u32);
                }
                ei = e.next;
            }
        }
        self.level[snk] >= 0
    }

    fn max_flow(&mut self, src: usize, snk: usize, limit: u32) -> u32 {
        let mut flow = 0u32;
        while flow < limit && self.bfs(src, snk) {
            self.cur.copy_from_slice(&self.head);
            self.stack_v.clear();
            self.stack_e.clear();
            self.stack_v.push(src);

            while !self.stack_v.is_empty() && flow < limit {
                let u = *self.stack_v.last().unwrap();
                if u == snk {
                    let mut push = limit - flow;
                    let mut bottleneck_pos = usize::MAX;
                    for (pos, &ei) in self.stack_e.iter().enumerate() {
                        let c = self.edges[ei as usize].cap;
                        if c < push {
                            push = c;
                            bottleneck_pos = pos;
                        }
                    }
                    for &ei in &self.stack_e {
                        self.edges[ei as usize].cap -= push;
                        self.edges[(ei ^ 1) as usize].cap += push;
                    }
                    flow += push;
                    if bottleneck_pos != usize::MAX {
                        self.stack_v.truncate(bottleneck_pos + 1);
                        self.stack_e.truncate(bottleneck_pos);
                    } else {
                        break;
                    }
                    continue;
                }

                let mut ei = self.cur[u];
                let u_lvl = self.level[u];
                let mut advanced = false;
                while ei != u32::MAX {
                    let e = self.edges[ei as usize];
                    let w = e.to as usize;
                    if e.cap > 0 && self.level[w] == u_lvl + 1 {
                        self.cur[u] = ei;
                        self.stack_v.push(w);
                        self.stack_e.push(ei);
                        advanced = true;
                        break;
                    }
                    ei = e.next;
                }

                if !advanced {
                    self.cur[u] = u32::MAX;
                    self.level[u] = -1;
                    self.stack_v.pop();
                    if self.stack_e.pop().is_some() {
                        let prev_u = *self.stack_v.last().unwrap();
                        let cur_e = self.cur[prev_u];
                        if cur_e != u32::MAX {
                            self.cur[prev_u] = self.edges[cur_e as usize].next;
                        }
                    }
                }
            }
        }
        flow
    }

    fn reachable_from(&self, src: usize) -> Vec<bool> {
        let mut vis = vec![false; self.head.len()];
        let mut q = VecDeque::new();
        vis[src] = true;
        q.push_back(src);
        while let Some(u) = q.pop_front() {
            let mut ei = self.head[u];
            while ei != u32::MAX {
                let e = self.edges[ei as usize];
                let w = e.to as usize;
                if e.cap > 0 && !vis[w] {
                    vis[w] = true;
                    q.push_back(w);
                }
                ei = e.next;
            }
        }
        vis
    }
}

pub struct MengerCutResult {
    pub cut_size: usize,
    pub target_count: usize,
    pub cut_vertices: Vec<usize>,
}

/// Exact minimum Menger vertex cut (`IsMengerVertexCut` in `PathSeparation.lean`, `Section 5`)
/// separating `Out(v0_outputs)` from `target_mask` in `dag`, certified by an independent
/// reachability check on `dag \ B_min`.
pub fn menger_min_vertex_cut(
    sched: &Schedule,
    dag: &DepGraph,
    v0_outputs: &[usize],
    target_mask: &[bool],
) -> MengerCutResult {
    let t_len = dag.t_len;
    assert_eq!(target_mask.len(), t_len);
    let target_count = target_mask.iter().filter(|&&b| b).count();
    if v0_outputs.is_empty() || target_count == 0 {
        return MengerCutResult {
            cut_size: 0,
            target_count,
            cut_vertices: Vec::new(),
        };
    }

    // Restrict Dinic network to `Cone(Out(V_0)) intersect Anc(target_mask)`. Every edge `t -> w`
    // in `DepGraph` satisfies `w < t`, so backward reachability to `target_mask` is a single
    // ascending pass `t = min_target .. t_len` with zero queue overhead.
    let mut in_cone = vec![false; t_len];
    let mut stack: Vec<usize> = Vec::with_capacity(v0_outputs.len());
    for &q in v0_outputs {
        let root = sched.append_times[q];
        if !in_cone[root] {
            in_cone[root] = true;
            stack.push(root);
        }
    }
    let mut min_target = usize::MAX;
    while let Some(u) = stack.pop() {
        if target_mask[u] && u < min_target {
            min_target = u;
        }
        for &w in &dag.out[u] {
            if !in_cone[w] {
                in_cone[w] = true;
                stack.push(w);
            }
        }
    }
    if min_target == usize::MAX {
        return MengerCutResult {
            cut_size: 0,
            target_count,
            cut_vertices: Vec::new(),
        };
    }

    let mut active = vec![false; t_len];
    for t in min_target..t_len {
        if in_cone[t] {
            active[t] = target_mask[t] || dag.out[t].iter().any(|&w| active[w]);
        }
    }

    let mut id_of = vec![u32::MAX; t_len];
    let mut orig_of = Vec::new();
    for (t, &vis) in active.iter().enumerate().skip(min_target) {
        if vis {
            id_of[t] = orig_of.len() as u32;
            orig_of.push(t);
        }
    }
    let m = orig_of.len();
    let src = 2 * m;
    let snk = 2 * m + 1;
    let inf = (v0_outputs.len() + 1) as u32;
    let mut dinic = Dinic::new(2 * m + 2);

    for (loc, &t) in orig_of.iter().enumerate() {
        dinic.add_edge(2 * loc, 2 * loc + 1, 1);
        if target_mask[t] {
            dinic.add_edge(2 * loc + 1, snk, inf);
        }
        for &w in &dag.out[t] {
            let w_loc = id_of[w];
            if w_loc != u32::MAX {
                dinic.add_edge(2 * loc + 1, 2 * (w_loc as usize), inf);
            }
        }
    }
    for &q in v0_outputs {
        let r_loc = id_of[sched.append_times[q]];
        if r_loc != u32::MAX {
            dinic.add_edge(src, 2 * (r_loc as usize), inf);
        }
    }

    let flow = dinic.max_flow(src, snk, inf) as usize;
    let reach = dinic.reachable_from(src);
    let mut cut_vertices = Vec::with_capacity(flow);
    let mut cut_mask = vec![false; t_len];
    for (loc, &t) in orig_of.iter().enumerate() {
        if reach[2 * loc] && !reach[2 * loc + 1] {
            cut_vertices.push(t);
            cut_mask[t] = true;
        }
    }
    assert_eq!(
        cut_vertices.len(),
        flow,
        "Max-flow / min-cut duality mismatch on {}",
        sched.id
    );

    // Independent post-cut verification: no path in `dag \ cut_mask` from `Out(V_0)` reaches `target_mask`.
    let mut vis = vec![false; t_len];
    let mut q_chk = VecDeque::new();
    for &q in v0_outputs {
        let root = sched.append_times[q];
        if !cut_mask[root] && !vis[root] {
            vis[root] = true;
            q_chk.push_back(root);
        }
    }
    while let Some(u) = q_chk.pop_front() {
        assert!(
            !target_mask[u],
            "Menger cut verification failed: target step {} still reachable on {}",
            u,
            sched.id
        );
        for &w in &dag.out[u] {
            if !cut_mask[w] && !vis[w] {
                vis[w] = true;
                q_chk.push_back(w);
            }
        }
    }

    MengerCutResult {
        cut_size: flow,
        target_count,
        cut_vertices,
    }
}

/// Labeled legacy non-root vertex separator (`IsBallPathSeparator`, forbidding root deletion),
/// returning `None` if a root itself lies in `target_mask`. Used only for Appendix A comparison.
pub fn legacy_nonroot_separator_cut(
    sched: &Schedule,
    dag: &DepGraph,
    v0_outputs: &[usize],
    target_mask: &[bool],
) -> Option<usize> {
    let t_len = dag.t_len;
    let mut is_root = vec![false; t_len];
    for &q in v0_outputs {
        let r = sched.append_times[q];
        if target_mask[r] {
            return None;
        }
        is_root[r] = true;
    }
    if v0_outputs.is_empty() || !target_mask.iter().any(|&b| b) {
        return Some(0);
    }

    let mut in_cone = vec![false; t_len];
    let mut stack = Vec::new();
    for &q in v0_outputs {
        let r = sched.append_times[q];
        if !in_cone[r] {
            in_cone[r] = true;
            stack.push(r);
        }
    }
    let mut any_tgt = false;
    while let Some(u) = stack.pop() {
        if target_mask[u] {
            any_tgt = true;
        }
        for &w in &dag.out[u] {
            if !in_cone[w] {
                in_cone[w] = true;
                stack.push(w);
            }
        }
    }
    if !any_tgt {
        return Some(0);
    }

    let mut id_of = vec![u32::MAX; t_len];
    let mut orig_of = Vec::new();
    for (t, &vis) in in_cone.iter().enumerate() {
        if vis {
            id_of[t] = orig_of.len() as u32;
            orig_of.push(t);
        }
    }
    let m = orig_of.len();
    let src = 2 * m;
    let snk = 2 * m + 1;
    let inf = (m + 5) as u32;
    let mut dinic = Dinic::new(2 * m + 2);
    for (loc, &t) in orig_of.iter().enumerate() {
        let vcap = if is_root[t] { inf } else { 1 };
        dinic.add_edge(2 * loc, 2 * loc + 1, vcap);
        if target_mask[t] {
            dinic.add_edge(2 * loc + 1, snk, inf);
        }
        for &w in &dag.out[t] {
            dinic.add_edge(2 * loc + 1, 2 * (id_of[w] as usize), inf);
        }
    }
    for &q in v0_outputs {
        let r_loc = id_of[sched.append_times[q]] as usize;
        dinic.add_edge(src, 2 * r_loc, inf);
    }
    let flow = dinic.max_flow(src, snk, inf);
    if flow >= inf {
        None
    } else {
        Some(flow as usize)
    }
}

/// Standard deterministic output subpopulations `V_0 subset [0, L)` tested in `Remark 5.8`,
/// `Remark 10.1`, and `Appendix A`: full output, halves, quarters, middle eighth, parity-striped
/// rows/columns/checkerboard, and the window-potential / off-diagonal quarters from `Sprint 43`.
pub fn standard_subpopulations(d: usize, b: usize) -> Vec<(&'static str, Vec<usize>)> {
    let l = d * d * b;
    let w = d * b;
    let q_len = (l / 4).max(1);
    let mut out = vec![
        ("all", (0..l).collect()),
        ("first_half", (0..(l / 2).max(1)).collect()),
        ("mid_half", (l / 4..(3 * l) / 4).collect()),
        ("q0", (0..q_len).collect()),
        ("q1", (q_len..(2 * q_len).min(l)).collect()),
        ("q2", ((2 * q_len).min(l)..(3 * q_len).min(l)).collect()),
        ("q3", ((3 * q_len).min(l)..l).collect()),
        ("mid_eighth", ((3 * l) / 8..(4 * l) / 8).collect()),
        (
            "even_rows",
            (0..l).filter(|&z| ((z / w) & 1) == 0).collect(),
        ),
        (
            "even_cols",
            (0..l).filter(|&z| (((z / b) % d) & 1) == 0).collect(),
        ),
        (
            "checker",
            (0..l)
                .filter(|&z| (((z / w) + ((z / b) % d)) & 1) == 0)
                .collect(),
        ),
        (
            "diag_band_q",
            (0..l)
                .filter(|&z| {
                    let q = tpos(d, b, z);
                    let r = (q / b) / d;
                    let c = (q / b) % d;
                    (r + c) % d < (d / 4).max(1)
                })
                .collect(),
        ),
    ];
    if l >= 16 * w {
        let s2_win: Vec<usize> = ((2 * w)..(l / 4 - 2 * w)).collect();
        if !s2_win.is_empty() {
            out.push(("s2_q1_win", s2_win));
        }
        let upper_q: Vec<usize> = (0..l)
            .filter(|&z| {
                let q = tpos(d, b, z);
                z >= l / 2 + 2 * w && q + 2 * w < l / 4
            })
            .collect();
        if !upper_q.is_empty() {
            out.push(("upper_q", upper_q));
        }
        let antidiag_q: Vec<usize> = (0..l)
            .filter(|&z| {
                let q = tpos(d, b, z);
                q >= 1 && z >= 1 && q + z + w < (3 * l) / 4 && z < l / 4
            })
            .collect();
        if !antidiag_q.is_empty() {
            out.push(("antidiag_q", antidiag_q));
        }
    }
    out
}

// ============================================================================
// 3. Radius-`D` Ball System & Cycle-Packing Acyclic-Set Upper Bound (`Remark 5.8`)
// ============================================================================

/// Extract the exact radius-`D` ball-avoidance relation `ballAvoidSystem(cut_mask, D)` on `[0, L)`:
/// for each output index `r in 0..L` with target input bit `p = tpos(d, b, r)`, `rel[p]` is the
/// sorted list of scanned input positions `{ scanned_input_cell(s) : dist_{dag \ cut_mask}(t_r, s) <= D }`.
pub fn extract_ball_avoid_relation(
    sched: &Schedule,
    dag: &DepGraph,
    radius: usize,
    cut_mask: &[bool],
) -> Vec<Vec<usize>> {
    let l = sched.len_bits();
    let t_len = dag.t_len;
    let mut rel = vec![Vec::new(); l];
    let mut dist = vec![u32::MAX; t_len];
    let mut touched = Vec::new();
    let mut q = VecDeque::new();

    for r in 0..l {
        let target_p = tpos(sched.d, sched.b, r);
        let root = sched.append_times[r];
        if cut_mask[root] {
            continue;
        }
        touched.clear();
        q.clear();
        dist[root] = 0;
        touched.push(root);
        q.push_back(root);

        let mut inputs = Vec::new();
        while let Some(u) = q.pop_front() {
            if let Some(inp) = sched.scanned_input_cell(u) {
                inputs.push(inp);
            }
            let d_u = dist[u] as usize;
            if d_u < radius {
                for &w in &dag.out[u] {
                    if !cut_mask[w] && dist[w] == u32::MAX {
                        dist[w] = (d_u + 1) as u32;
                        touched.push(w);
                        q.push_back(w);
                    }
                }
            }
        }
        for &u in &touched {
            dist[u] = u32::MAX;
        }
        inputs.sort_unstable();
        inputs.dedup();
        rel[target_p] = inputs;
    }
    rel
}

/// Certified upper bound on the maximum acyclic set (`MAIS`) of `cone_rel` (`Remark 5.8`):
/// excludes self-recoverable bits (`p in rel[p]`), packs vertex-disjoint mutual cliques (`|K| >= 2`,
/// contributing `<= 1` vertex each to any acyclic set), and packs vertex-disjoint directed 3-cycles
/// (`contributing <= 2` vertices each to any acyclic set).
pub fn certified_acyclic_upper_bound(cone_rel: &[Vec<usize>]) -> usize {
    let l = cone_rel.len();
    let mut is_self = vec![false; l];
    let mut unrecovered = 0usize;
    for q in 0..l {
        if cone_rel[q].binary_search(&q).is_ok() {
            is_self[q] = true;
        } else {
            unrecovered += 1;
        }
    }

    let mut recip = vec![Vec::new(); l];
    for q in 0..l {
        if is_self[q] {
            continue;
        }
        for &p in &cone_rel[q] {
            if p > q && !is_self[p] && cone_rel[p].binary_search(&q).is_ok() {
                recip[q].push(p);
                recip[p].push(q);
            }
        }
    }
    for r in &mut recip {
        r.sort_unstable();
    }

    let mut order: Vec<(usize, usize)> = (0..l)
        .filter(|&q| !is_self[q] && !recip[q].is_empty())
        .map(|q| (q, recip[q].len()))
        .collect();
    order.sort_unstable_by(|a, b| a.1.cmp(&b.1).then_with(|| a.0.cmp(&b.0)));

    let mut placed = is_self;
    let mut saved = 0usize;
    let mut clique = Vec::new();
    for &(seed, _) in &order {
        if placed[seed] {
            continue;
        }
        clique.clear();
        clique.push(seed);
        for &cand in &recip[seed] {
            if !placed[cand]
                && clique
                    .iter()
                    .all(|&m_v| m_v == seed || recip[cand].binary_search(&m_v).is_ok())
            {
                clique.push(cand);
            }
        }
        if clique.len() >= 2 {
            for &w in &clique {
                placed[w] = true;
            }
            saved += clique.len() - 1;
        }
    }

    for u in 0..l {
        if placed[u] {
            continue;
        }
        let mut found_c3 = None;
        'c3: for &v in cone_rel[u].iter().take(48) {
            if v == u || placed[v] {
                continue;
            }
            for &w in cone_rel[v].iter().take(48) {
                if w == u || w == v || placed[w] {
                    continue;
                }
                if cone_rel[w].binary_search(&u).is_ok() {
                    found_c3 = Some((v, w));
                    break 'c3;
                }
            }
        }
        if let Some((v, w)) = found_c3 {
            placed[u] = true;
            placed[v] = true;
            placed[w] = true;
            saved += 1;
        }
    }
    unrecovered - saved
}

// ============================================================================
// 4. Disjoint Expanding Waves (`Remark 10.1` / `Proposition 8.3`)
// ============================================================================

/// Reusable cone max-flow workspace for evaluating many subsets of `cand_steps` against a fixed
/// `(sched, dag, v0)` cone without rebuilding the vertex-split graph.
struct ConeFlowWorkspace {
    dinic: Dinic,
    base_caps: Vec<u32>,
    sink_edge_of_cand: Vec<Option<u32>>,
    src: usize,
    snk: usize,
    inf: u32,
}

impl ConeFlowWorkspace {
    fn new(sched: &Schedule, dag: &DepGraph, v0: &[usize], cand_steps: &[usize]) -> Self {
        let t_len = dag.t_len;
        let mut in_cone = vec![false; t_len];
        let mut stack = Vec::with_capacity(v0.len());
        for &q in v0 {
            let r = sched.append_times[q];
            if !in_cone[r] {
                in_cone[r] = true;
                stack.push(r);
            }
        }
        while let Some(u) = stack.pop() {
            for &w in &dag.out[u] {
                if !in_cone[w] {
                    in_cone[w] = true;
                    stack.push(w);
                }
            }
        }

        let mut id_of = vec![u32::MAX; t_len];
        let mut orig_of = Vec::new();
        for (t, &vis) in in_cone.iter().enumerate() {
            if vis {
                id_of[t] = orig_of.len() as u32;
                orig_of.push(t);
            }
        }
        let m = orig_of.len();
        let src = 2 * m;
        let snk = 2 * m + 1;
        let inf = (v0.len() + 1) as u32;
        let mut dinic = Dinic::with_capacity(2 * m + 2, 4 * m + v0.len() + cand_steps.len());

        for (loc, &t) in orig_of.iter().enumerate() {
            dinic.add_edge(2 * loc, 2 * loc + 1, 1);
            for &w in &dag.out[t] {
                let w_loc = id_of[w] as usize;
                dinic.add_edge(2 * loc + 1, 2 * w_loc, inf);
            }
        }
        for &q in v0 {
            let r_loc = id_of[sched.append_times[q]] as usize;
            dinic.add_edge(src, 2 * r_loc, inf);
        }

        let mut sink_edge_of_cand = Vec::with_capacity(cand_steps.len());
        for &t in cand_steps {
            let loc = id_of[t];
            if loc != u32::MAX {
                let ei = dinic.add_edge(2 * (loc as usize) + 1, snk, 0);
                sink_edge_of_cand.push(Some(ei));
            } else {
                sink_edge_of_cand.push(None);
            }
        }

        let base_caps: Vec<u32> = dinic.edges.iter().map(|e| e.cap).collect();
        Self {
            dinic,
            base_caps,
            sink_edge_of_cand,
            src,
            snk,
            inf,
        }
    }

    fn query_range(&mut self, lo: usize, hi_incl: usize, limit: u32) -> usize {
        for (e, &bc) in self.dinic.edges.iter_mut().zip(self.base_caps.iter()) {
            e.cap = bc;
        }
        let mut any = false;
        for opt_ei in &self.sink_edge_of_cand[lo..=hi_incl] {
            if let Some(ei) = *opt_ei {
                self.dinic.edges[ei as usize].cap = self.inf;
                any = true;
            }
        }
        if !any {
            return 0;
        }
        self.dinic.max_flow(self.src, self.snk, limit) as usize
    }

    fn query_cand_indices(&mut self, cand_idxs: &[usize], limit: u32) -> usize {
        for (e, &bc) in self.dinic.edges.iter_mut().zip(self.base_caps.iter()) {
            e.cap = bc;
        }
        let mut any = false;
        for &ci in cand_idxs {
            if let Some(ei) = self.sink_edge_of_cand[ci] {
                self.dinic.edges[ei as usize].cap = self.inf;
                any = true;
            }
        }
        if !any {
            return 0;
        }
        self.dinic.max_flow(self.src, self.snk, limit) as usize
    }
}

/// Exact maximum number of chronologically separated (`max W_r < min W_{r+1}`) subsets of
/// `all_mask` that each achieve `|B_min(Out(v0) -> W_r)| >= ceil(c_thresh * |v0|)`, computed by
/// earliest-deadline galloping binary search (`optimal by Menger monotonicity`).
pub fn max_disjoint_expanding_waves(
    sched: &Schedule,
    dag: &DepGraph,
    v0: &[usize],
    all_mask: &[bool],
    c_thresh: f64,
) -> (usize, usize) {
    let steps: Vec<usize> = (0..all_mask.len()).filter(|&t| all_mask[t]).collect();
    let req_flow = ((c_thresh * (v0.len() as f64)).ceil() as usize).max(1);
    let n = steps.len();
    if n < req_flow {
        return (0, n);
    }

    let req_u32 = req_flow as u32;
    let mut ws = ConeFlowWorkspace::new(sched, dag, v0, &steps);
    let mut n_waves = 0usize;
    let mut cur_lo = 0usize;
    while cur_lo + req_flow <= n {
        if ws.query_range(cur_lo, n - 1, req_u32) < req_flow {
            break;
        }

        let mut lo_fail = cur_lo + req_flow - 1;
        let f0 = ws.query_range(cur_lo, lo_fail, req_u32);

        let best_hi = if f0 >= req_flow {
            lo_fail
        } else {
            let mut step_sz = req_flow.max(16);
            let hi_pass = loop {
                let cand = (lo_fail + step_sz).min(n - 1);
                if cand >= n - 1 {
                    break n - 1;
                }
                if ws.query_range(cur_lo, cand, req_u32) >= req_flow {
                    break cand;
                }
                lo_fail = cand;
                step_sz *= 2;
            };
            let mut l = lo_fail;
            let mut r = hi_pass;
            while l + 1 < r {
                let mid = l + (r - l) / 2;
                if ws.query_range(cur_lo, mid, req_u32) >= req_flow {
                    r = mid;
                } else {
                    l = mid;
                }
            }
            r
        };

        n_waves += 1;
        cur_lo = best_hi + 1;
    }
    assert!(n_waves * req_flow <= n);
    (n_waves, n)
}

/// Count how many fixed-size chronological chunks (`chunk_size` steps of `all_mask`) independently
/// expand by `>= ceil(c_thresh * |v0|)` (`Proposition 8.3` / `Sprint 46` scaling check up to `d = 128`).
pub fn chronological_expanding_chunks(
    sched: &Schedule,
    dag: &DepGraph,
    v0: &[usize],
    all_mask: &[bool],
    chunk_size: usize,
    c_thresh: f64,
) -> (usize, usize) {
    let steps: Vec<usize> = (0..all_mask.len()).filter(|&t| all_mask[t]).collect();
    let req_flow = ((c_thresh * (v0.len() as f64)).ceil() as usize).max(1);
    let n = steps.len();
    if n < req_flow || chunk_size == 0 {
        return (0, 0);
    }
    let req_u32 = req_flow as u32;
    let mut ws = ConeFlowWorkspace::new(sched, dag, v0, &steps);
    let mut pass = 0usize;
    let mut tot = 0usize;
    let mut lo = 0usize;
    while lo < n {
        let hi = (lo + chunk_size).min(n) - 1;
        tot += 1;
        if hi + 1 - lo >= req_flow && ws.query_range(lo, hi, req_u32) >= req_flow {
            pass += 1;
        }
        lo = hi + 1;
    }
    assert!(pass * req_flow <= n);
    (pass, tot)
}

// ============================================================================
// 5. Macroscopic Skeletons & Single-Leg Crossing Expansion (`Section 6`, `Remarks 6.8 & 10.1`)
// ============================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TapeSkeleton {
    pub lambda: i64,
    pub times: Vec<usize>,
    pub steps: Vec<bool>,
    pub grid: Vec<i64>,
    pub epoch_of: Vec<usize>,
}

/// Exact greedy `Lambda`-milestone skeleton (`Definition 6.1` / `MacroscopicSkeleton.tapeSkeleton`).
pub fn extract_tape_skeleton(walk: &[i64], lambda: i64) -> TapeSkeleton {
    assert!(lambda >= 1);
    let t_len = walk.len();
    assert!(t_len > 0 && walk[0] == 0);

    let mut times = vec![0usize];
    let mut steps = Vec::new();
    let mut grid = vec![0i64];
    let mut epoch_of = vec![0usize; t_len];
    let mut cur_g = 0i64;
    let mut cur_ep = 0usize;

    for t in 1..t_len {
        let diff = walk[t] - cur_g * lambda;
        if diff.abs() >= lambda {
            assert_eq!(diff.abs(), lambda);
            let step_up = diff > 0;
            cur_g += if step_up { 1 } else { -1 };
            times.push(t);
            steps.push(step_up);
            grid.push(cur_g);
            cur_ep += 1;
        }
        assert!((walk[t] - cur_g * lambda).abs() < lambda);
        epoch_of[t] = cur_ep;
    }
    assert!(steps.len() * (lambda as usize) <= t_len);
    TapeSkeleton {
        lambda,
        times,
        steps,
        grid,
        epoch_of,
    }
}

pub fn count_skeleton_legs(steps: &[bool]) -> usize {
    if steps.is_empty() {
        return 0;
    }
    let mut legs = 1usize;
    for w in steps.windows(2) {
        if w[0] != w[1] {
            legs += 1;
        }
    }
    legs
}

pub fn leg_of_epoch(steps: &[bool]) -> Vec<usize> {
    let m = steps.len();
    let mut leg = vec![0usize; m + 1];
    for i in 1..m {
        leg[i + 1] = if steps[i] == steps[i - 1] {
            leg[i]
        } else {
            leg[i] + 1
        };
    }
    leg
}

pub fn format_skeleton_legs(steps: &[bool]) -> String {
    if steps.is_empty() {
        return "0".to_string();
    }
    let mut runs: Vec<i64> = Vec::new();
    for &s in steps {
        let v = if s { 1i64 } else { -1i64 };
        if let Some(last) = runs.last_mut() {
            if (*last > 0) == (v > 0) {
                *last += v;
                continue;
            }
        }
        runs.push(v);
    }
    if runs.len() <= 10 {
        runs.iter()
            .map(|&r| if r > 0 { format!("+{r}") } else { format!("{r}") })
            .collect::<Vec<_>>()
            .join(",")
    } else {
        let head = runs[..3]
            .iter()
            .map(|&r| if r > 0 { format!("+{r}") } else { format!("{r}") })
            .collect::<Vec<_>>()
            .join(",");
        let tail = runs[runs.len() - 2..]
            .iter()
            .map(|&r| if r > 0 { format!("+{r}") } else { format!("{r}") })
            .collect::<Vec<_>>()
            .join(",");
        format!("{head},...,{tail}({}legs)", runs.len())
    }
}

/// Necessary crossing-capable condition on a `Lambda`-skeleton (`Proposition 6.5` /
/// `IsCrossingCapableSkeleton(H, Lambda, grid)`).
pub fn is_crossing_capable_skeleton(h_thresh: i64, lambda: i64, grid: &[i64]) -> bool {
    let m1 = grid.len();
    if m1 < 4 {
        return false;
    }
    for eps in [1i64, -1i64] {
        let h: Vec<i64> = grid.iter().map(|&g| eps * g).collect();
        let mut pref_min = vec![i64::MAX; m1];
        let mut cur_mn = h[0];
        for i1 in 1..m1 {
            pref_min[i1] = cur_mn;
            cur_mn = cur_mn.min(h[i1]);
        }
        let mut suf_max = vec![i64::MIN; m1];
        let mut cur_mx = h[m1 - 1];
        for i2 in (0..(m1 - 1)).rev() {
            suf_max[i2] = cur_mx;
            cur_mx = cur_mx.max(h[i2]);
        }
        for i1 in 1..(m1 - 2) {
            let h0 = pref_min[i1];
            if (h[i1] - h0 + 2) * lambda < 2 * h_thresh + 3 {
                continue;
            }
            for i2 in (i1 + 1)..(m1 - 1) {
                if (h[i1] - h[i2] + 2) * lambda < 2 * h_thresh + 3 {
                    continue;
                }
                let h3 = suf_max[i2];
                if (h3 - h[i2] + 2) * lambda < 2 * h_thresh + 3 {
                    continue;
                }
                let ov = h[i1].min(h3) - h0.max(h[i2]);
                if (ov + 2) * lambda >= 3 {
                    return true;
                }
            }
        }
    }
    false
}

pub struct SingleLegExpansionSummary {
    pub per_tape_legs: Vec<String>,
    pub total_legs: usize,
    pub any_crossing_capable: bool,
    pub max_single_leg_cut_ratio: f64,
    pub best_tape_and_leg: (usize, usize),
}

/// Evaluate `Lambda`-skeletons across all work tapes and find the maximum Menger cut ratio
/// `|B_min(Out([0, L)) -> legCrossingLowers(j, r))| / L` carried by a SINGLE skeleton leg `(j, r)`
/// at excursion threshold `exc_thresh = 2 * H` (`Theorem 6.7`, `Remark 6.8`, `Remark 10.1`).
pub fn analyze_skeleton_and_single_leg_expansion(
    sched: &Schedule,
    dag: &DepGraph,
    lambda: i64,
    h_thresh: i64,
) -> SingleLegExpansionSummary {
    let l = sched.len_bits();
    let v_all: Vec<usize> = (0..l).collect();
    let exc_thresh = 2 * h_thresh;
    let mut per_tape_legs = Vec::with_capacity(sched.k);
    let mut total_legs = 0usize;
    let mut any_capable = false;
    let mut cand_legs: Vec<(usize, usize, Vec<usize>)> = Vec::new();

    for j in 0..sched.k {
        let skel = extract_tape_skeleton(&sched.work_pos[j], lambda);
        per_tape_legs.push(format_skeleton_legs(&skel.steps));
        let n_legs = count_skeleton_legs(&skel.steps).max(1);
        total_legs += count_skeleton_legs(&skel.steps);
        if is_crossing_capable_skeleton(h_thresh, lambda, &skel.grid) {
            any_capable = true;
        }

        // Partition `> 2*H` crossing lowers on tape `j` by the skeleton leg of `p`:
        let leg_of_ep = leg_of_epoch(&skel.steps);
        let revs = &dag.revisits_by_tape[j];
        let mut long_by_p: Vec<(usize, usize)> = revs
            .iter()
            .filter(|r| r.excursion > exc_thresh)
            .map(|r| (r.p, r.u))
            .collect();
        if long_by_p.len() < 2 {
            continue;
        }
        long_by_p.sort_unstable();
        let n = long_by_p.len();
        let cap = n.next_power_of_two();
        let mut max_u_tree = vec![0usize; 2 * cap];
        for (idx, &(_, u)) in long_by_p.iter().enumerate() {
            max_u_tree[cap + idx] = u;
        }
        for idx in (1..cap).rev() {
            max_u_tree[idx] = max_u_tree[2 * idx].max(max_u_tree[2 * idx + 1]);
        }
        let mut long_by_u = long_by_p.clone();
        long_by_u.sort_unstable_by_key(|&(p, u)| (u, p));
        let mut min_p_tree = vec![usize::MAX; 2 * cap];
        for (idx, &(p, _)) in long_by_u.iter().enumerate() {
            min_p_tree[cap + idx] = p;
        }
        for idx in (1..cap).rev() {
            min_p_tree[idx] = min_p_tree[2 * idx].min(min_p_tree[2 * idx + 1]);
        }

        let mut leg_lists: Vec<Vec<usize>> = vec![Vec::new(); n_legs];
        for &(p, u) in &long_by_p {
            let mut l1 = long_by_p.partition_point(|&(p2, _)| p2 <= p) + cap;
            let mut r1 = long_by_p.partition_point(|&(p2, _)| p2 < u) + cap;
            let mut mx_u = 0usize;
            while l1 < r1 {
                if (l1 & 1) == 1 {
                    mx_u = mx_u.max(max_u_tree[l1]);
                    l1 += 1;
                }
                if (r1 & 1) == 1 {
                    r1 -= 1;
                    mx_u = mx_u.max(max_u_tree[r1]);
                }
                l1 >>= 1;
                r1 >>= 1;
            }
            let mut l2 = long_by_u.partition_point(|&(_, u2)| u2 <= p) + cap;
            let mut r2 = long_by_u.partition_point(|&(_, u2)| u2 < u) + cap;
            let mut mn_p = usize::MAX;
            while l2 < r2 {
                if (l2 & 1) == 1 {
                    mn_p = mn_p.min(min_p_tree[l2]);
                    l2 += 1;
                }
                if (r2 & 1) == 1 {
                    r2 -= 1;
                    mn_p = mn_p.min(min_p_tree[r2]);
                }
                l2 >>= 1;
                r2 >>= 1;
            }
            if mx_u > u || mn_p < p {
                let r_leg = leg_of_ep[skel.epoch_of[p]];
                leg_lists[r_leg].push(p);
            }
        }

        for (r_leg, mut pts) in leg_lists.into_iter().enumerate() {
            if !pts.is_empty() {
                pts.sort_unstable();
                pts.dedup();
                cand_legs.push((j, r_leg, pts));
            }
        }
    }

    // Since `min_cut(Out([0, L)) -> S) <= min(L, |S|)` unconditionally, testing candidate legs
    // in decreasing order of `|S|` on a single reusable `ConeFlowWorkspace` and stopping once
    // `min(L, |S|) <= best_cut` returns the exact global maximum single-leg cut without rebuilding
    // the vertex-split graph across legs, then certifies the winning leg via `menger_min_vertex_cut`.
    cand_legs.sort_by(|a, b| b.2.len().cmp(&a.2.len()).then_with(|| (a.0, a.1).cmp(&(b.0, b.1))));
    let mut best_cut = 0usize;
    let mut best_pair = (0usize, 0usize);
    let mut best_pts: Vec<usize> = Vec::new();
    if !cand_legs.is_empty() {
        let mut union_steps: Vec<usize> = Vec::new();
        for (_, _, pts) in &cand_legs {
            union_steps.extend_from_slice(pts);
        }
        union_steps.sort_unstable();
        union_steps.dedup();
        let mut ws = ConeFlowWorkspace::new(sched, dag, &v_all, &union_steps);
        let mut cand_idxs = Vec::new();
        for (j, r_leg, pts) in cand_legs {
            if pts.len().min(l) <= best_cut {
                break;
            }
            cand_idxs.clear();
            cand_idxs.extend(pts.iter().map(|p| union_steps.binary_search(p).unwrap()));
            let cut = ws.query_cand_indices(&cand_idxs, ws.inf);
            if cut > best_cut {
                best_cut = cut;
                best_pair = (j, r_leg);
                best_pts = pts;
            }
        }
        if !best_pts.is_empty() {
            let mut mask = vec![false; dag.t_len];
            for &p in &best_pts {
                mask[p] = true;
            }
            let certified = menger_min_vertex_cut(sched, dag, &v_all, &mask).cut_size;
            assert_eq!(certified, best_cut);
        }
    }
    let max_ratio = best_cut as f64 / (l as f64);

    SingleLegExpansionSummary {
        per_tape_legs,
        total_legs,
        any_crossing_capable: any_capable,
        max_single_leg_cut_ratio: max_ratio,
        best_tape_and_leg: best_pair,
    }
}

// ============================================================================
// 6. Coarse Joint Phase Profiles (`Section 10.4`) & Multi-Scale Leg Counts (`Problem 11.1`)
// ============================================================================

/// Exact `O(K * |I|)` greedy partition of `[start, end)` into maximal sub-intervals on which
/// EVERY trajectory in `walks` is `amp`-coarsely monotone (`CoarseMonoOnInterval`: either never
/// drops by more than `amp` below its running max, or never rises by more than `amp` above its
/// running min). Because `CoarseMonoOnInterval` is hereditary, greedy left-to-right scanning achieves
/// the exact minimum pass count!
pub fn greedy_joint_coarse_boundaries(
    walks: &[&[i64]],
    start: usize,
    end: usize,
    amp: i64,
) -> Vec<usize> {
    assert!(amp >= 0 && start <= end);
    if start == end {
        return vec![start];
    }
    let n_w = walks.len();
    let mut bnds = vec![start];
    let mut run_min = vec![0i64; n_w];
    let mut run_max = vec![0i64; n_w];
    let mut can_inc = vec![true; n_w];
    let mut can_dec = vec![true; n_w];

    let mut cur = start;
    while cur < end {
        for (i, w) in walks.iter().enumerate() {
            run_min[i] = w[cur];
            run_max[i] = w[cur];
            can_inc[i] = true;
            can_dec[i] = true;
        }
        let mut t = cur + 1;
        while t < end {
            let mut all_ok = true;
            for (i, w) in walks.iter().enumerate() {
                let v = w[t];
                let nxt_inc = can_inc[i] && (run_max[i] - v <= amp);
                let nxt_dec = can_dec[i] && (v - run_min[i] <= amp);
                if !nxt_inc && !nxt_dec {
                    all_ok = false;
                    break;
                }
            }
            if !all_ok {
                break;
            }
            for (i, w) in walks.iter().enumerate() {
                let v = w[t];
                can_inc[i] = can_inc[i] && (run_max[i] - v <= amp);
                can_dec[i] = can_dec[i] && (v - run_min[i] <= amp);
                if v < run_min[i] {
                    run_min[i] = v;
                }
                if v > run_max[i] {
                    run_max[i] = v;
                }
            }
            t += 1;
        }
        bnds.push(t);
        cur = t;
    }
    bnds
}

/// Joint coarse pass counts `M_ph(floor(2^{-s} L))` on `(in_pos, work_pos[0..k])` across
/// `s = 0 ..= max_s` (`Section 10.4`).
pub fn coarse_phase_profile(sched: &Schedule, max_s: usize) -> Vec<(usize, i64, usize)> {
    let l = sched.len_bits();
    let t_len = sched.horizon();
    let mut walks: Vec<&[i64]> = Vec::with_capacity(sched.k + 1);
    walks.push(&sched.in_pos);
    for j in 0..sched.k {
        walks.push(&sched.work_pos[j]);
    }
    let mut out = Vec::with_capacity(max_s + 1);
    for s in 0..=max_s {
        let amp = ((l >> s).max(1)) as i64;
        let bnds = greedy_joint_coarse_boundaries(&walks, 0, t_len, amp);
        out.push((s, amp, bnds.len() - 1));
    }
    out
}

/// Total skeleton legs `r_j = legs(tapeSkeleton(in_pos, lam)) + sum_h legs(tapeSkeleton(y_h, lam))`
/// across all heads (input head included, matching revised `Problem 11.1`) at `lam = floor(2^{-j} L)`.
pub fn skeleton_legs_profile(sched: &Schedule, max_j: usize) -> Vec<(usize, i64, usize)> {
    let l = sched.len_bits();
    let mut out = Vec::with_capacity(max_j);
    for j_scale in 1..=max_j {
        let lam = ((l >> j_scale).max(1)) as i64;
        let in_skel = extract_tape_skeleton(&sched.in_pos, lam);
        let mut tot_legs = count_skeleton_legs(&in_skel.steps);
        for h in 0..sched.k {
            let skel = extract_tape_skeleton(&sched.work_pos[h], lam);
            tot_legs += count_skeleton_legs(&skel.steps);
        }
        out.push((j_scale, lam, tot_legs));
    }
    out
}

// ============================================================================
// 7. Closed Interval-Forest Charges (`Problem 11.1`: 1-Scale & 2-Scale)
// ============================================================================

#[derive(Clone, Copy, Debug)]
pub enum ForestMode {
    OneScale(i64),
    LocalizedTwoScale(i64, i64),
    SpanWeightedTwoScale(i64, i64),
}

#[derive(Clone, Copy, Debug, Default)]
pub struct ForestChargeResult {
    pub exact_cut_sum: usize,
    pub trace_only_sum: usize,
    pub entry_points_sum: usize,
    pub entry_cells_sum: usize,
}

fn merge_intervals(ivs: &mut Vec<(usize, usize)>) {
    if ivs.len() <= 1 {
        return;
    }
    ivs.sort_unstable();
    let mut out: Vec<(usize, usize)> = Vec::with_capacity(ivs.len());
    for &(s, e) in ivs.iter() {
        if let Some(last) = out.last_mut() {
            if s <= last.1 + 1 {
                if e > last.1 {
                    last.1 = e;
                }
                continue;
            }
        }
        out.push((s, e));
    }
    *ivs = out;
}

pub fn build_prev_visits(sched: &Schedule) -> Vec<Vec<Option<u32>>> {
    let t_len = sched.horizon();
    let mut out = Vec::with_capacity(sched.k);
    for j in 0..sched.k {
        let w = &sched.work_pos[j];
        let mut last: HashMap<i64, u32> = HashMap::with_capacity(t_len.min(65536));
        let mut pv = vec![None; t_len];
        for (t, &c) in w.iter().enumerate() {
            pv[t] = last.insert(c, t as u32);
        }
        out.push(pv);
    }
    out
}

fn build_sub_boundaries_and_map(sched: &Schedule, mode: ForestMode) -> (usize, Vec<u32>) {
    let t_len = sched.horizon();
    let mut all_walks: Vec<&[i64]> = Vec::with_capacity(sched.k + 1);
    all_walks.push(&sched.in_pos);
    for j in 0..sched.k {
        all_walks.push(&sched.work_pos[j]);
    }

    let sub_bnds = match mode {
        ForestMode::OneScale(amp) => greedy_joint_coarse_boundaries(&all_walks, 0, t_len, amp),
        ForestMode::LocalizedTwoScale(a0, a1) | ForestMode::SpanWeightedTwoScale(a0, a1) => {
            let p_bnds = greedy_joint_coarse_boundaries(&all_walks, 0, t_len, a0);
            let mut sb = vec![0usize];
            for pw in p_bnds.windows(2) {
                let cb = greedy_joint_coarse_boundaries(&all_walks, pw[0], pw[1], a1);
                sb.extend_from_slice(&cb[1..]);
            }
            sb
        }
    };

    let n_sub = sub_bnds.len() - 1;
    let mut step_to_sub = vec![0u32; t_len];
    for sp in 0..n_sub {
        for tau in sub_bnds[sp]..sub_bnds[sp + 1] {
            step_to_sub[tau] = sp as u32;
        }
    }
    (n_sub, step_to_sub)
}

/// Evaluate the closed dependency interval-forest charge (`ExactCut` and schedule-geometric
/// `TraceOnly` residue upper bound) for column-group width `gamma` and hierarchy `mode`.
pub fn evaluate_interval_forest(
    sched: &Schedule,
    prev_visits: &[Vec<Option<u32>>],
    gamma: usize,
    mode: ForestMode,
) -> ForestChargeResult {
    let (n_sub, step_to_sub) = build_sub_boundaries_and_map(sched, mode);
    evaluate_interval_forest_with_map(sched, prev_visits, gamma, mode, n_sub, &step_to_sub)
}

fn evaluate_interval_forest_with_map(
    sched: &Schedule,
    prev_visits: &[Vec<Option<u32>>],
    gamma: usize,
    mode: ForestMode,
    n_sub: usize,
    step_to_sub: &[u32],
) -> ForestChargeResult {
    let d = sched.d;
    let b = sched.b;
    let k = sched.k;
    let l = sched.len_bits();
    let t_len = sched.horizon();
    let num_groups = (d + gamma - 1) / gamma;

    let mut in_f = vec![false; t_len];
    let mut read_seen = vec![u32::MAX; l];
    let mut res = ForestChargeResult::default();

    for g in 0..num_groups {
        let col_lo = g * gamma;
        let col_hi = ((g + 1) * gamma).min(d);
        let g_width = col_hi - col_lo;
        let out_lo = col_lo * d * b;
        let out_hi = col_hi * d * b;

        let mut active: Vec<Vec<(usize, usize)>> = vec![Vec::new(); n_sub];
        for o_idx in out_lo..out_hi {
            let tau = sched.append_times[o_idx];
            active[step_to_sub[tau] as usize].push((tau, tau));
        }

        for sp in (0..n_sub).rev() {
            if active[sp].is_empty() {
                continue;
            }
            merge_intervals(&mut active[sp]);
            let cur_ivs = active[sp].clone();
            for &(a, e) in &cur_ivs {
                for j in 0..k {
                    let w_j = &sched.work_pos[j];
                    let h_a = w_j[a];
                    let amp_use = match mode {
                        ForestMode::OneScale(amp) => amp,
                        ForestMode::LocalizedTwoScale(_, a1) => a1,
                        ForestMode::SpanWeightedTwoScale(a0, a1) => {
                            let mut saved_cells = 0usize;
                            let mut child_targets: HashMap<u32, (usize, usize)> = HashMap::new();
                            for tau in a..=e {
                                if let Some(sig_u32) = prev_visits[j][tau] {
                                    let sig = sig_u32 as usize;
                                    if sig < a {
                                        let c = w_j[tau];
                                        let in_a0 = (c - h_a).abs() <= 2 * a0;
                                        let in_a1 = (c - h_a).abs() <= 2 * a1;
                                        if in_a0 && !in_a1 {
                                            saved_cells += 1;
                                            let sp_c = step_to_sub[sig];
                                            child_targets
                                                .entry(sp_c)
                                                .and_modify(|bnd| {
                                                    bnd.0 = bnd.0.min(sig);
                                                    bnd.1 = bnd.1.max(sig);
                                                })
                                                .or_insert((sig, sig));
                                        }
                                    }
                                }
                            }
                            if saved_cells == 0 {
                                a0
                            } else {
                                let mut est_cost = 0usize;
                                for &(s_lo, s_hi) in child_targets.values() {
                                    est_cost += 1;
                                    for tp in 0..k {
                                        let c0 = sched.work_pos[tp][s_lo];
                                        let c1 = sched.work_pos[tp][s_hi];
                                        est_cost += ((c1 - c0).unsigned_abs() as usize + 1)
                                            .min((3 * a1 + 1) as usize);
                                    }
                                    let ip0 = sched.in_pos[s_lo];
                                    let ip1 = sched.in_pos[s_hi];
                                    let in_span = (ip1 - ip0).unsigned_abs() as usize + 1;
                                    est_cost += (g_width * (in_span + d * b)) / (d * b);
                                }
                                if est_cost < saved_cells {
                                    a1
                                } else {
                                    a0
                                }
                            }
                        }
                    };

                    let mut per_sp: HashMap<u32, (usize, usize)> = HashMap::new();
                    for tau in a..=e {
                        let c = w_j[tau];
                        if (c - h_a).abs() <= 2 * amp_use {
                            continue;
                        }
                        if let Some(sig_u32) = prev_visits[j][tau] {
                            let sig = sig_u32 as usize;
                            if sig < a {
                                let sp_prev = step_to_sub[sig] as usize;
                                assert!(sp_prev < sp);
                                per_sp
                                    .entry(sp_prev as u32)
                                    .and_modify(|bnd| {
                                        bnd.0 = bnd.0.min(sig);
                                        bnd.1 = bnd.1.max(sig);
                                    })
                                    .or_insert((sig, sig));
                            }
                        }
                    }
                    for (sp_u32, bnd) in per_sp {
                        active[sp_u32 as usize].push(bnd);
                    }
                }
            }
        }

        let mut all_ivs: Vec<(usize, usize)> = Vec::new();
        for sp_ivs in &active {
            all_ivs.extend_from_slice(sp_ivs);
        }
        merge_intervals(&mut all_ivs);

        for &(a, e) in &all_ivs {
            for tau in a..=e {
                in_f[tau] = true;
            }
        }

        let ep_cnt = all_ivs.iter().filter(|&&(a, _)| a > 0).count();
        let mut ec_cnt = 0usize;
        for &(a, e) in &all_ivs {
            for tau in a..=e {
                for pv_j in prev_visits.iter().take(k) {
                    if let Some(sig) = pv_j[tau] {
                        if !in_f[sig as usize] {
                            ec_cnt += 1;
                        }
                    }
                }
            }
        }

        let mut exact_comb_reads = 0usize;
        let mut read_cells: Vec<usize> = Vec::new();
        let tag = g as u32;
        for &(a, e) in &all_ivs {
            for tau in a..=e {
                if let Some(idx) = sched.scanned_input_cell(tau) {
                    if read_seen[idx] != tag {
                        read_seen[idx] = tag;
                        read_cells.push(idx);
                        let col = (idx / b) % d;
                        if col >= col_lo && col < col_hi {
                            exact_comb_reads += 1;
                        }
                    }
                }
            }
        }
        read_cells.sort_unstable();
        let mut residue_cap = 0usize;
        let row_bits = d * b;
        let grp_row_bits = g_width * b;
        let mut idx_i = 0usize;
        while idx_i < read_cells.len() {
            let r_lo = read_cells[idx_i];
            let mut r_hi = r_lo;
            while idx_i + 1 < read_cells.len() && read_cells[idx_i + 1] == r_hi + 1 {
                idx_i += 1;
                r_hi = read_cells[idx_i];
            }
            let w_r = r_hi - r_lo + 1;
            residue_cap += (w_r / row_bits) * grp_row_bits + (w_r % row_bits).min(grp_row_bits);
            idx_i += 1;
        }
        assert!(exact_comb_reads <= residue_cap);

        res.entry_points_sum += ep_cnt;
        res.entry_cells_sum += ec_cnt;
        res.exact_cut_sum += exact_comb_reads + ep_cnt + ec_cnt;
        res.trace_only_sum += residue_cap + ep_cnt + ec_cnt;

        for &(a, e) in &all_ivs {
            for tau in a..=e {
                in_f[tau] = false;
            }
        }
    }
    res
}

pub struct BestForestSummary {
    pub best_1scale_exact: f64,
    pub best_1scale_trace: f64,
    pub best_2scale_loc_exact: f64,
    pub best_2scale_loc_trace: f64,
    pub best_2scale_opt_exact: f64,
    pub best_2scale_opt_trace: f64,
}

/// Reproduce Sprint 50 (`Problem 11.1`) dyadic interval-forest charges across
/// `gamma in {1, 2, 4, 8, 16, 32, 64, 128}` (`<= d`), 1-scales `2^{-3} L .. 2^{-8} L`, and
/// 2-scale pairs `(2^{-3} L, 2^{-6} L)`, `(2^{-4} L, 2^{-7} L)`, `(2^{-5} L, 2^{-8} L)`.
pub fn best_paper_dyadic_interval_forest_charges(sched: &Schedule) -> BestForestSummary {
    let d = sched.d;
    let l = sched.len_bits();
    let prev_visits = build_prev_visits(sched);

    let gammas: Vec<usize> = [1usize, 2, 4, 8, 16, 32, 64, 128]
        .into_iter()
        .filter(|&g| g <= d)
        .collect();
    let pairs: [(i64, i64); 3] = [
        (((l >> 3) as i64).max(1), ((l >> 6) as i64).max(1)),
        (((l >> 4) as i64).max(1), ((l >> 7) as i64).max(1)),
        (((l >> 5) as i64).max(1), ((l >> 8) as i64).max(1)),
    ];
    let mut scales_1: Vec<i64> = (3..=8).map(|s| ((l >> s) as i64).max(1)).collect();
    scales_1.sort_unstable();
    scales_1.dedup();

    let mut best_1s_ex = usize::MAX;
    let mut best_1s_tr = usize::MAX;
    let mut best_2l_ex = usize::MAX;
    let mut best_2l_tr = usize::MAX;
    let mut best_2o_ex = usize::MAX;
    let mut best_2o_tr = usize::MAX;

    for &a in &scales_1 {
        let mode = ForestMode::OneScale(a);
        let (n_sub, step_to_sub) = build_sub_boundaries_and_map(sched, mode);
        for &gamma in &gammas {
            let r1 = evaluate_interval_forest_with_map(
                sched,
                &prev_visits,
                gamma,
                mode,
                n_sub,
                &step_to_sub,
            );
            best_1s_ex = best_1s_ex.min(r1.exact_cut_sum);
            best_1s_tr = best_1s_tr.min(r1.trace_only_sum);
        }
    }
    for &(a0, a1) in &pairs {
        if a0 <= a1 {
            continue;
        }
        let mode_loc = ForestMode::LocalizedTwoScale(a0, a1);
        let (n_sub, step_to_sub) = build_sub_boundaries_and_map(sched, mode_loc);
        let mode_opt = ForestMode::SpanWeightedTwoScale(a0, a1);
        for &gamma in &gammas {
            let rl = evaluate_interval_forest_with_map(
                sched,
                &prev_visits,
                gamma,
                mode_loc,
                n_sub,
                &step_to_sub,
            );
            best_2l_ex = best_2l_ex.min(rl.exact_cut_sum);
            best_2l_tr = best_2l_tr.min(rl.trace_only_sum);

            let ro = evaluate_interval_forest_with_map(
                sched,
                &prev_visits,
                gamma,
                mode_opt,
                n_sub,
                &step_to_sub,
            );
            best_2o_ex = best_2o_ex.min(ro.exact_cut_sum);
            best_2o_tr = best_2o_tr.min(ro.trace_only_sum);
        }
    }

    let lf = l as f64;
    BestForestSummary {
        best_1scale_exact: best_1s_ex as f64 / lf,
        best_1scale_trace: best_1s_tr as f64 / lf,
        best_2scale_loc_exact: best_2l_ex as f64 / lf,
        best_2scale_loc_trace: best_2l_tr as f64 / lf,
        best_2scale_opt_exact: best_2o_ex as f64 / lf,
        best_2scale_opt_trace: best_2o_tr as f64 / lf,
    }
}

/// Extended wider sweep minimizing 1-scale, localized 2-scale, and span-weighted 2-scale closed
/// interval-forest charges across `gamma in {1, 2, 4, 8, 16, 32, 64, 128}` and all scales down to `A_1 = 1`.
pub fn best_interval_forest_charges(sched: &Schedule) -> BestForestSummary {
    let d = sched.d;
    let l = sched.len_bits();
    let prev_visits = build_prev_visits(sched);

    let gammas: Vec<usize> = [1usize, 2, 4, 8, 16, 32, 64, 128]
        .into_iter()
        .filter(|&g| g <= d)
        .collect();
    let mut scales: Vec<i64> = vec![
        (l / 4) as i64,
        (l / 8) as i64,
        (l / 16) as i64,
        (l / 32) as i64,
        (l / 64) as i64,
        (l / 128) as i64,
        (l / 256) as i64,
        (d * sched.b) as i64,
        ((d * sched.b) / 4).max(1) as i64,
        1,
    ];
    scales.retain(|&a| a >= 1 && (a as usize) < l);
    scales.sort_unstable();
    scales.dedup();

    let mut best_1s_ex = usize::MAX;
    let mut best_1s_tr = usize::MAX;
    let mut best_2l_ex = usize::MAX;
    let mut best_2l_tr = usize::MAX;
    let mut best_2o_ex = usize::MAX;
    let mut best_2o_tr = usize::MAX;

    for &a in &scales {
        let mode = ForestMode::OneScale(a);
        let (n_sub, step_to_sub) = build_sub_boundaries_and_map(sched, mode);
        for &gamma in &gammas {
            let r1 = evaluate_interval_forest_with_map(
                sched,
                &prev_visits,
                gamma,
                mode,
                n_sub,
                &step_to_sub,
            );
            best_1s_ex = best_1s_ex.min(r1.exact_cut_sum);
            best_1s_tr = best_1s_tr.min(r1.trace_only_sum);
        }
    }
    for (i0, &a0) in scales.iter().enumerate() {
        for &a1 in &scales[..i0] {
            let mode_loc = ForestMode::LocalizedTwoScale(a0, a1);
            let (n_sub, step_to_sub) = build_sub_boundaries_and_map(sched, mode_loc);
            let mode_opt = ForestMode::SpanWeightedTwoScale(a0, a1);
            for &gamma in &gammas {
                let rl = evaluate_interval_forest_with_map(
                    sched,
                    &prev_visits,
                    gamma,
                    mode_loc,
                    n_sub,
                    &step_to_sub,
                );
                best_2l_ex = best_2l_ex.min(rl.exact_cut_sum);
                best_2l_tr = best_2l_tr.min(rl.trace_only_sum);

                let ro = evaluate_interval_forest_with_map(
                    sched,
                    &prev_visits,
                    gamma,
                    mode_opt,
                    n_sub,
                    &step_to_sub,
                );
                best_2o_ex = best_2o_ex.min(ro.exact_cut_sum);
                best_2o_tr = best_2o_tr.min(ro.trace_only_sum);
            }
        }
    }

    let lf = l as f64;
    BestForestSummary {
        best_1scale_exact: best_1s_ex as f64 / lf,
        best_1scale_trace: best_1s_tr as f64 / lf,
        best_2scale_loc_exact: best_2l_ex as f64 / lf,
        best_2scale_loc_trace: best_2l_tr as f64 / lf,
        best_2scale_opt_exact: best_2o_ex as f64 / lf,
        best_2scale_opt_trace: best_2o_tr as f64 / lf,
    }
}

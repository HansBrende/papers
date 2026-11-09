//! Core oblivious-schedule model, full time-indexed JSON/CSV exporters, and exact
//! dependency-DAG builder matching Section 2 (`Definition 2.1`, `Definition 2.3`) and
//! Lean's `BoundedNesting.IsHop` + `MergeDepth.DepStep` verbatim.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::io::{self, Write};

/// Canonical entry bit-width `b(d) = max(1, ceil(log2(d)))`.
#[inline]
pub fn entry_bits(d: usize) -> usize {
    if d <= 2 {
        1
    } else {
        (usize::BITS - (d - 1).leading_zeros()) as usize
    }
}

/// Matrix-transposition involution `tpos((i * d + j) * b + s) = (j * d + i) * b + s`
/// on a `d x d` matrix of `b`-bit entries (`L = d^2 * b`).
#[inline]
pub fn tpos(d: usize, b: usize, addr: usize) -> usize {
    let s = addr % b;
    let entry = addr / b;
    let i = entry / d;
    let j = entry % d;
    (j * d + i) * b + s
}

/// Computational nature of an oblivious schedule generator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ComputationKind {
    /// Carries explicit per-step `F_2`-linear bit operations whose time-indexed data flow computes
    /// `Y[r] = X[tpos(d, b, r)]` on the zero input and all `L` unit vectors (hence every `X in {0, 1}^L`).
    BitVerifiedTransposer,
    /// Carries explicit per-step bit operations that compute a specific non-transpose
    /// function (e.g. identity, persistent triangles, or `F_2` XOR cascade).
    ExplicitNonTransposer,
    /// Prescribes head motion, input-loading scans, active stage writes, and output-append
    /// timestamps only; whether some machine with this trace transposes is open (Cascades 1-5)
    /// or excluded for all machines by a theorem/certificate (Appendix A rows).
    GeometryOnly,
}

impl ComputationKind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::BitVerifiedTransposer => "actual_transpose_bit_verified",
            Self::ExplicitNonTransposer => "explicit_non_transpose_function",
            Self::GeometryOnly => "geometry_only",
        }
    }
}

/// Per-step tape read/write operation at step `t`.
/// In the Turing model of Section 2, every step scans `(in_pos[t], work_pos[0..k][t])`
/// and writes a symbol on every work tape (preserving the scanned symbol when passing through).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StepOp {
    /// Pure head transit / wait: every work tape preserves its scanned cell (`writes scanned symbol`).
    PassThrough,
    /// Loads scanned input bit `X[in_pos]` onto `dst_tape` (and emits it if `emit` is set).
    LoadInput { dst_tape: u8 },
    /// Loads scanned input bit `X[in_pos]` onto every work tape in bitmask `dst_mask`.
    LoadInputMask { dst_mask: u16 },
    /// Copies scanned bit from `src_tape` onto `dst_tape` (and emits it if `emit` is set).
    CopyWork { src_tape: u8, dst_tape: u8 },
    /// Updates `work[dst_tape] ^= work[src_tape]` over `F_2`.
    XorWork { src_tape: u8, dst_tape: u8 },
    /// Emits `work[src_tape]` without modifying any work cell.
    EmitWork { src_tape: u8 },
    /// Emits `work[0] ^ work[1] ^ work[2]` without modifying any work cell.
    EmitXor3,
    /// Emits scanned input bit `X[in_pos]` directly without modifying any work cell.
    EmitInput,
    /// Symbolic active stage step for geometry-only schedules: tapes in `write_mask` update
    /// their scanned zone cell; tapes outside `write_mask` pass through unchanged.
    StageWrite { write_mask: u16 },
}

impl StepOp {
    /// True iff step `t` explicitly loads a bit from the input tape into a work tape or output.
    #[inline]
    pub fn loads_input(self) -> bool {
        matches!(
            self,
            Self::LoadInput { .. } | Self::LoadInputMask { .. } | Self::EmitInput
        )
    }

    /// Bitmask of work tapes whose scanned cell is actively written/updated (rather than passed through).
    #[inline]
    pub fn written_tape_mask(self) -> u16 {
        match self {
            Self::PassThrough | Self::EmitWork { .. } | Self::EmitXor3 | Self::EmitInput => 0,
            Self::LoadInput { dst_tape } => 1u16 << dst_tape,
            Self::LoadInputMask { dst_mask } => dst_mask,
            Self::CopyWork { src_tape, dst_tape } => {
                if src_tape == dst_tape {
                    0
                } else {
                    1u16 << dst_tape
                }
            }
            Self::XorWork { dst_tape, .. } => 1u16 << dst_tape,
            Self::StageWrite { write_mask } => write_mask,
        }
    }

    /// Short machine-readable tag for tape `j`'s write action at this step (`CSV`/`JSON` export).
    pub fn write_tag_for_tape(self, j: usize) -> String {
        let bit = 1u16 << j;
        match self {
            Self::PassThrough | Self::EmitWork { .. } | Self::EmitXor3 | Self::EmitInput => {
                "pass".to_string()
            }
            Self::LoadInput { dst_tape } if dst_tape as usize == j => "load_in".to_string(),
            Self::LoadInputMask { dst_mask } if (dst_mask & bit) != 0 => "load_in".to_string(),
            Self::CopyWork { src_tape, dst_tape }
                if dst_tape as usize == j && src_tape != dst_tape =>
            {
                format!("copy_w{}", src_tape)
            }
            Self::XorWork { src_tape, dst_tape } if dst_tape as usize == j => {
                format!("xor_w{}", src_tape)
            }
            Self::StageWrite { write_mask } if (write_mask & bit) != 0 => {
                "stage_write".to_string()
            }
            _ => "pass".to_string(),
        }
    }
}

/// Complete oblivious schedule on `[0, T)` for parameters `(d, b)` and `k` work tapes.
#[derive(Clone)]
pub struct Schedule {
    pub id: &'static str,
    pub title: &'static str,
    pub d: usize,
    pub b: usize,
    pub k: usize,
    pub kind: ComputationKind,
    /// Input-head position `x(t)` at each step `t in 0..T` (`x(0) = 0`).
    pub in_pos: Vec<i64>,
    /// Input-head move `din(t) in {-1, 0, +1}` applied after step `t`.
    pub in_move: Vec<i8>,
    /// Work-head position `y_j(t)` for each tape `j in 0..k` and step `t in 0..T` (`y_j(0) = 0`).
    pub work_pos: Vec<Vec<i64>>,
    /// Work-head move `dw_j(t) in {-1, 0, +1}` applied after step `t`.
    pub work_move: Vec<Vec<i8>>,
    /// Explicit per-step read/write operation.
    pub ops: Vec<StepOp>,
    /// Strictly increasing timestamps `append_times[r]` (`r in 0..L`) at which output bit `r`
    /// (whose transpose target input bit is `tpos(d, b, r)`) is appended to the output tape.
    pub append_times: Vec<usize>,
    /// Inverse map `append_at_step[t] = Some(r)` if step `t` appends output index `r`, else `None`.
    pub append_at_step: Vec<Option<u32>>,
}

impl Schedule {
    #[inline]
    pub fn len_bits(&self) -> usize {
        self.d * self.d * self.b
    }

    #[inline]
    pub fn horizon(&self) -> usize {
        self.in_pos.len()
    }

    /// Scanned input cell `p in 0..L` at step `t` if the input head sits inside `[0, L)`,
    /// or `None` if it sits on a blank cell outside `[0, L)`.
    #[inline]
    pub fn scanned_input_cell(&self, t: usize) -> Option<usize> {
        let p = self.in_pos[t];
        let l = self.len_bits();
        if p >= 0 && (p as usize) < l {
            Some(p as usize)
        } else {
            None
        }
    }

    /// Maximum number of cell entries on any single cell across all `k` work tapes:
    /// a cell is entered at `t = 0` and whenever `y_j(t) != y_j(t - 1)`.
    pub fn max_work_cell_entries(&self) -> usize {
        let t_len = self.horizon();
        let mut max_ent = 0usize;
        for j in 0..self.k {
            let w = &self.work_pos[j];
            let mut counts: HashMap<i64, usize> = HashMap::new();
            if t_len > 0 {
                *counts.entry(w[0]).or_insert(0) += 1;
            }
            for t in 1..t_len {
                if w[t] != w[t - 1] {
                    *counts.entry(w[t]).or_insert(0) += 1;
                }
            }
            for &c in counts.values() {
                if c > max_ent {
                    max_ent = c;
                }
            }
        }
        max_ent
    }

    /// Maximum number of active write steps (`written_tape_mask`) on any single cell of any work tape.
    pub fn max_active_writes_per_cell(&self) -> usize {
        let mut max_wr = 0usize;
        for j in 0..self.k {
            let bit = 1u16 << j;
            let mut counts: HashMap<i64, usize> = HashMap::new();
            for (t, &op) in self.ops.iter().enumerate() {
                if (op.written_tape_mask() & bit) != 0 {
                    let c = self.work_pos[j][t];
                    let e = counts.entry(c).or_insert(0);
                    *e += 1;
                    if *e > max_wr {
                        max_wr = *e;
                    }
                }
            }
        }
        max_wr
    }

    /// Simulate the explicit bit operations of `self` on input `x in {0, 1}^L`.
    /// Panics if `self.kind == ComputationKind::GeometryOnly`.
    pub fn simulate_bits(&self, x: &[u8]) -> Vec<u8> {
        assert_ne!(
            self.kind,
            ComputationKind::GeometryOnly,
            "Cannot bit-simulate geometry-only schedule {}",
            self.id
        );
        let l = self.len_bits();
        assert_eq!(x.len(), l);

        let mut min_p = vec![0i64; self.k];
        let mut tapes: Vec<Vec<u8>> = Vec::with_capacity(self.k);
        for j in 0..self.k {
            let mn = self.work_pos[j].iter().copied().min().unwrap_or(0);
            let mx = self.work_pos[j].iter().copied().max().unwrap_or(0);
            min_p[j] = mn;
            tapes.push(vec![0u8; (mx - mn + 1) as usize]);
        }

        let mut out = Vec::with_capacity(l);
        for (t, &op) in self.ops.iter().enumerate() {
            let mut emitted_bit = 0u8;
            match op {
                StepOp::PassThrough => {}
                StepOp::LoadInput { dst_tape } => {
                    let j = dst_tape as usize;
                    let val = self.scanned_input_cell(t).map(|p| x[p]).unwrap_or(0);
                    let idx = (self.work_pos[j][t] - min_p[j]) as usize;
                    tapes[j][idx] = val;
                    emitted_bit = val;
                }
                StepOp::LoadInputMask { dst_mask } => {
                    let val = self.scanned_input_cell(t).map(|p| x[p]).unwrap_or(0);
                    for j in 0..self.k {
                        if (dst_mask & (1u16 << j)) != 0 {
                            let idx = (self.work_pos[j][t] - min_p[j]) as usize;
                            tapes[j][idx] = val;
                        }
                    }
                    emitted_bit = val;
                }
                StepOp::CopyWork { src_tape, dst_tape } => {
                    let s = src_tape as usize;
                    let d_t = dst_tape as usize;
                    let s_idx = (self.work_pos[s][t] - min_p[s]) as usize;
                    let val = tapes[s][s_idx];
                    let d_idx = (self.work_pos[d_t][t] - min_p[d_t]) as usize;
                    tapes[d_t][d_idx] = val;
                    emitted_bit = val;
                }
                StepOp::XorWork { src_tape, dst_tape } => {
                    let s = src_tape as usize;
                    let d_t = dst_tape as usize;
                    let s_idx = (self.work_pos[s][t] - min_p[s]) as usize;
                    let val = tapes[s][s_idx];
                    let d_idx = (self.work_pos[d_t][t] - min_p[d_t]) as usize;
                    tapes[d_t][d_idx] ^= val;
                    emitted_bit = tapes[d_t][d_idx];
                }
                StepOp::EmitWork { src_tape } => {
                    let s = src_tape as usize;
                    let s_idx = (self.work_pos[s][t] - min_p[s]) as usize;
                    emitted_bit = tapes[s][s_idx];
                }
                StepOp::EmitXor3 => {
                    let v0 = tapes[0][(self.work_pos[0][t] - min_p[0]) as usize];
                    let v1 = tapes[1][(self.work_pos[1][t] - min_p[1]) as usize];
                    let v2 = tapes[2][(self.work_pos[2][t] - min_p[2]) as usize];
                    emitted_bit = v0 ^ v1 ^ v2;
                }
                StepOp::EmitInput => {
                    emitted_bit = self.scanned_input_cell(t).map(|p| x[p]).unwrap_or(0);
                }
                StepOp::StageWrite { .. } => {
                    panic!("StageWrite cannot be bit-simulated on {}", self.id);
                }
            }
            if self.append_at_step[t].is_some() {
                out.push(emitted_bit);
            }
        }
        assert_eq!(out.len(), l);
        out
    }

    /// Simulate 64 bit-parallel inputs packed into `u64` lanes (`lane m` holds input `X^{(m)}`).
    pub fn simulate_bits_u64(&self, x_lanes: &[u64]) -> Vec<u64> {
        assert_ne!(
            self.kind,
            ComputationKind::GeometryOnly,
            "Cannot bit-simulate geometry-only schedule {}",
            self.id
        );
        let l = self.len_bits();
        assert_eq!(x_lanes.len(), l);

        let mut min_p = vec![0i64; self.k];
        let mut tapes: Vec<Vec<u64>> = Vec::with_capacity(self.k);
        for j in 0..self.k {
            let mn = self.work_pos[j].iter().copied().min().unwrap_or(0);
            let mx = self.work_pos[j].iter().copied().max().unwrap_or(0);
            min_p[j] = mn;
            tapes.push(vec![0u64; (mx - mn + 1) as usize]);
        }

        let mut out = Vec::with_capacity(l);
        for (t, &op) in self.ops.iter().enumerate() {
            let mut emitted_word = 0u64;
            match op {
                StepOp::PassThrough => {}
                StepOp::LoadInput { dst_tape } => {
                    let j = dst_tape as usize;
                    let val = self.scanned_input_cell(t).map(|p| x_lanes[p]).unwrap_or(0);
                    let idx = (self.work_pos[j][t] - min_p[j]) as usize;
                    tapes[j][idx] = val;
                    emitted_word = val;
                }
                StepOp::LoadInputMask { dst_mask } => {
                    let val = self.scanned_input_cell(t).map(|p| x_lanes[p]).unwrap_or(0);
                    for j in 0..self.k {
                        if (dst_mask & (1u16 << j)) != 0 {
                            let idx = (self.work_pos[j][t] - min_p[j]) as usize;
                            tapes[j][idx] = val;
                        }
                    }
                    emitted_word = val;
                }
                StepOp::CopyWork { src_tape, dst_tape } => {
                    let s = src_tape as usize;
                    let d_t = dst_tape as usize;
                    let s_idx = (self.work_pos[s][t] - min_p[s]) as usize;
                    let val = tapes[s][s_idx];
                    let d_idx = (self.work_pos[d_t][t] - min_p[d_t]) as usize;
                    tapes[d_t][d_idx] = val;
                    emitted_word = val;
                }
                StepOp::XorWork { src_tape, dst_tape } => {
                    let s = src_tape as usize;
                    let d_t = dst_tape as usize;
                    let s_idx = (self.work_pos[s][t] - min_p[s]) as usize;
                    let val = tapes[s][s_idx];
                    let d_idx = (self.work_pos[d_t][t] - min_p[d_t]) as usize;
                    tapes[d_t][d_idx] ^= val;
                    emitted_word = tapes[d_t][d_idx];
                }
                StepOp::EmitWork { src_tape } => {
                    let s = src_tape as usize;
                    let s_idx = (self.work_pos[s][t] - min_p[s]) as usize;
                    emitted_word = tapes[s][s_idx];
                }
                StepOp::EmitXor3 => {
                    let v0 = tapes[0][(self.work_pos[0][t] - min_p[0]) as usize];
                    let v1 = tapes[1][(self.work_pos[1][t] - min_p[1]) as usize];
                    let v2 = tapes[2][(self.work_pos[2][t] - min_p[2]) as usize];
                    emitted_word = v0 ^ v1 ^ v2;
                }
                StepOp::EmitInput => {
                    emitted_word = self.scanned_input_cell(t).map(|p| x_lanes[p]).unwrap_or(0);
                }
                StepOp::StageWrite { .. } => {
                    panic!("StageWrite cannot be bit-simulated on {}", self.id);
                }
            }
            if self.append_at_step[t].is_some() {
                out.push(emitted_word);
            }
        }
        assert_eq!(out.len(), l);
        out
    }

    /// Exact verification of the schedule's `F_2`-linear `StepOp` list on the zero input `0 in {0, 1}^L`
    /// and all `L` unit vectors `e_0, ..., e_{L - 1} in {0, 1}^L` (packed 64 per `u64` batch).
    /// Because every non-`StageWrite` `StepOp` is `F_2`-linear, passing on `0` and all `L` unit
    /// vectors establishes `simulate_bits(X)[r] == X[tpos(d, b, r)]` for EVERY `X in {0, 1}^L`.
    pub fn verify_transposer_exact_basis(&self) {
        assert_eq!(self.kind, ComputationKind::BitVerifiedTransposer);
        let l = self.len_bits();
        let mut x_lanes = vec![0u64; l];

        // 1. All-zero input vector.
        let y_zero = self.simulate_bits_u64(&x_lanes);
        for (r, &w) in y_zero.iter().enumerate() {
            assert_eq!(
                w, 0,
                "Transposer {} failed all-zero check at d={} b={} r={}",
                self.id, self.d, self.b, r
            );
        }

        // 2. All `L` unit vectors `e_0, ..., e_{L-1}` in batches of 64 lanes.
        let mut base = 0usize;
        while base < l {
            let batch = (l - base).min(64);
            for lane in 0..batch {
                x_lanes[base + lane] = 1u64 << lane;
            }
            let y_lanes = self.simulate_bits_u64(&x_lanes);
            for r in 0..l {
                let p = tpos(self.d, self.b, r);
                let expected = if p >= base && p < base + batch {
                    1u64 << (p - base)
                } else {
                    0u64
                };
                assert_eq!(
                    y_lanes[r], expected,
                    "Transposer {} failed exact unit-vector check at d={} b={} batch_base={} r={} (got {:#x}, expected {:#x})",
                    self.id, self.d, self.b, base, r, y_lanes[r], expected
                );
            }
            for lane in 0..batch {
                x_lanes[base + lane] = 0;
            }
            base += batch;
        }
    }

    /// Export full time-indexed schedule as CSV.
    pub fn write_csv<W: Write>(&self, mut out: W) -> io::Result<()> {
        write!(
            out,
            "step,in_pos,in_move,in_scanned_cell,in_loaded"
        )?;
        for j in 0..self.k {
            write!(out, ",work_{j}_pos,work_{j}_move,work_{j}_write")?;
        }
        writeln!(out, ",append_out_idx,append_target_input")?;

        let mut line = String::with_capacity(128);
        for t in 0..self.horizon() {
            line.clear();
            let op = self.ops[t];
            let _ = write!(line, "{},{},{}", t, self.in_pos[t], self.in_move[t]);
            match self.scanned_input_cell(t) {
                Some(p) => {
                    let _ = write!(line, ",{}", p);
                }
                None => line.push(','),
            }
            let _ = write!(line, ",{}", if op.loads_input() { 1 } else { 0 });
            for j in 0..self.k {
                let _ = write!(
                    line,
                    ",{},{},{}",
                    self.work_pos[j][t],
                    self.work_move[j][t],
                    op.write_tag_for_tape(j)
                );
            }
            if let Some(r_u32) = self.append_at_step[t] {
                let r = r_u32 as usize;
                let _ = write!(line, ",{},{}", r, tpos(self.d, self.b, r));
            } else {
                line.push_str(",,");
            }
            writeln!(out, "{}", line)?;
        }
        Ok(())
    }

    /// Export full time-indexed schedule as JSON.
    pub fn write_json<W: Write>(&self, mut out: W) -> io::Result<()> {
        let l = self.len_bits();
        writeln!(out, "{{")?;
        writeln!(out, "  \"id\": \"{}\",", self.id)?;
        writeln!(out, "  \"title\": \"{}\",", self.title)?;
        writeln!(out, "  \"computation_kind\": \"{}\",", self.kind.as_str())?;
        writeln!(out, "  \"d\": {},", self.d)?;
        writeln!(out, "  \"b\": {},", self.b)?;
        writeln!(out, "  \"L\": {},", l)?;
        writeln!(out, "  \"k\": {},", self.k)?;
        writeln!(out, "  \"T\": {},", self.horizon())?;
        writeln!(out, "  \"steps\": [")?;
        let t_len = self.horizon();
        for t in 0..t_len {
            let op = self.ops[t];
            let scanned_str = match self.scanned_input_cell(t) {
                Some(p) => p.to_string(),
                None => "null".to_string(),
            };
            let mut work_json = String::with_capacity(64 * self.k);
            work_json.push('[');
            for j in 0..self.k {
                if j > 0 {
                    work_json.push_str(", ");
                }
                let _ = write!(
                    work_json,
                    "{{\"pos\": {}, \"move\": {}, \"write\": \"{}\"}}",
                    self.work_pos[j][t],
                    self.work_move[j][t],
                    op.write_tag_for_tape(j)
                );
            }
            work_json.push(']');
            let append_json = match self.append_at_step[t] {
                Some(r_u32) => {
                    let r = r_u32 as usize;
                    format!(
                        "{{\"out_idx\": {}, \"target_input\": {}}}",
                        r,
                        tpos(self.d, self.b, r)
                    )
                }
                None => "null".to_string(),
            };
            let comma = if t + 1 < t_len { "," } else { "" };
            writeln!(
                out,
                "    {{\"t\": {}, \"in_pos\": {}, \"in_move\": {}, \"in_scanned_cell\": {}, \"in_loaded\": {}, \"work\": {}, \"append\": {}}}{}",
                t,
                self.in_pos[t],
                self.in_move[t],
                scanned_str,
                op.loads_input(),
                work_json,
                append_json,
                comma
            )?;
        }
        writeln!(out, "  ]")?;
        writeln!(out, "}}")?;
        Ok(())
    }
}

/// Incremental unit-speed schedule builder enforcing `x(0) = 0`, `y_j(0) = 0`,
/// `|dx|, |dy_j| <= 1`, and exactly `L = d^2 * b` strictly increasing appends.
pub struct ScheduleBuilder {
    id: &'static str,
    title: &'static str,
    d: usize,
    b: usize,
    k: usize,
    kind: ComputationKind,
    pub cur_in: i64,
    pub cur_work: Vec<i64>,
    in_pos: Vec<i64>,
    in_move: Vec<i8>,
    work_pos: Vec<Vec<i64>>,
    work_move: Vec<Vec<i8>>,
    ops: Vec<StepOp>,
    append_times: Vec<usize>,
    append_at_step: Vec<Option<u32>>,
}

impl ScheduleBuilder {
    pub fn new(
        id: &'static str,
        title: &'static str,
        d: usize,
        b: usize,
        k: usize,
        kind: ComputationKind,
    ) -> Self {
        Self {
            id,
            title,
            d,
            b,
            k,
            kind,
            cur_in: 0,
            cur_work: vec![0; k],
            in_pos: Vec::new(),
            in_move: Vec::new(),
            work_pos: vec![Vec::new(); k],
            work_move: vec![Vec::new(); k],
            ops: Vec::new(),
            append_times: Vec::new(),
            append_at_step: Vec::new(),
        }
    }

    /// Record one step with explicit `StepOp`.
    #[inline]
    pub fn step_with_op(&mut self, din: i64, dwork: &[i64], emit: bool, op: StepOp) {
        assert_eq!(dwork.len(), self.k);
        assert!(din.abs() <= 1, "Input head exceeded unit speed: {}", din);
        let t = self.in_pos.len();
        self.in_pos.push(self.cur_in);
        self.in_move.push(din as i8);
        for j in 0..self.k {
            assert!(
                dwork[j].abs() <= 1,
                "Work head {} exceeded unit speed: {}",
                j,
                dwork[j]
            );
            self.work_pos[j].push(self.cur_work[j]);
            self.work_move[j].push(dwork[j] as i8);
            self.cur_work[j] += dwork[j];
        }
        self.cur_in += din;
        self.ops.push(op);
        if emit {
            let r = self.append_times.len() as u32;
            self.append_times.push(t);
            self.append_at_step.push(Some(r));
        } else {
            self.append_at_step.push(None);
        }
    }

    /// Convenience step for geometry-only schedules: marks input-loading when advancing on `[0, L)`
    /// and marks moving/active work tapes in `StageWrite`.
    #[inline]
    pub fn step(&mut self, din: i64, dwork: &[i64], emit: bool) {
        let l = (self.d * self.d * self.b) as i64;
        let all_mask = if self.k >= 16 {
            u16::MAX
        } else {
            (1u16 << self.k) - 1
        };
        let op = if din != 0 && self.cur_in >= 0 && self.cur_in < l {
            let mut mask = 0u16;
            for (j, &dw) in dwork.iter().enumerate() {
                if dw != 0 || self.k == 1 {
                    mask |= 1u16 << j;
                }
            }
            StepOp::LoadInputMask {
                dst_mask: if mask == 0 { 1 } else { mask },
            }
        } else if emit {
            StepOp::EmitWork { src_tape: 0 }
        } else {
            StepOp::StageWrite {
                write_mask: all_mask,
            }
        };
        self.step_with_op(din, dwork, emit, op);
    }

    /// Pure pass-through positioning move (`StepOp::PassThrough`, zero zone writes).
    pub fn move_work_to(&mut self, tape: usize, target: i64) {
        let mut dw = vec![0i64; self.k];
        while self.cur_work[tape] != target {
            dw.fill(0);
            dw[tape] = (target - self.cur_work[tape]).signum();
            self.step_with_op(0, &dw, false, StepOp::PassThrough);
        }
    }

    /// Pure pass-through two-tape positioning move (`StepOp::PassThrough`, zero zone writes).
    pub fn move_two_works_to(&mut self, t1: usize, target1: i64, t2: usize, target2: i64) {
        assert_ne!(t1, t2);
        let mut dw = vec![0i64; self.k];
        while self.cur_work[t1] != target1 || self.cur_work[t2] != target2 {
            dw.fill(0);
            dw[t1] = (target1 - self.cur_work[t1]).signum();
            dw[t2] = (target2 - self.cur_work[t2]).signum();
            self.step_with_op(0, &dw, false, StepOp::PassThrough);
        }
    }

    /// Pure pass-through three-tape positioning move (`StepOp::PassThrough`, zero zone writes).
    pub fn move_three_works_to(&mut self, target0: i64, target1: i64, target2: i64) {
        assert_eq!(self.k, 3);
        while self.cur_work[0] != target0
            || self.cur_work[1] != target1
            || self.cur_work[2] != target2
        {
            let d0 = (target0 - self.cur_work[0]).signum();
            let d1 = (target1 - self.cur_work[1]).signum();
            let d2 = (target2 - self.cur_work[2]).signum();
            self.step_with_op(0, &[d0, d1, d2], false, StepOp::PassThrough);
        }
    }

    pub fn finish(self) -> Schedule {
        let l = self.d * self.d * self.b;
        let t_len = self.in_pos.len();
        assert!(t_len >= l, "Schedule {}: T={} < L={}", self.id, t_len, l);
        assert_eq!(
            self.append_times.len(),
            l,
            "Schedule {}: appended {} != L={}",
            self.id,
            self.append_times.len(),
            l
        );
        assert_eq!(self.in_pos[0], 0, "Schedule {}: in_pos[0] != 0", self.id);
        for j in 0..self.k {
            assert_eq!(
                self.work_pos[j][0], 0,
                "Schedule {}: work_pos[{}][0] != 0",
                self.id, j
            );
        }
        for t in 0..t_len.saturating_sub(1) {
            assert_eq!(self.in_pos[t] + (self.in_move[t] as i64), self.in_pos[t + 1]);
            assert!((self.in_pos[t + 1] - self.in_pos[t]).abs() <= 1);
            for j in 0..self.k {
                assert_eq!(
                    self.work_pos[j][t] + (self.work_move[j][t] as i64),
                    self.work_pos[j][t + 1]
                );
                assert!((self.work_pos[j][t + 1] - self.work_pos[j][t]).abs() <= 1);
            }
        }
        for w in self.append_times.windows(2) {
            assert!(w[0] < w[1], "append_times must be strictly increasing");
        }
        Schedule {
            id: self.id,
            title: self.title,
            d: self.d,
            b: self.b,
            k: self.k,
            kind: self.kind,
            in_pos: self.in_pos,
            in_move: self.in_move,
            work_pos: self.work_pos,
            work_move: self.work_move,
            ops: self.ops,
            append_times: self.append_times,
            append_at_step: self.append_at_step,
        }
    }
}

/// Exact revisit `(p, u)` on a work tape (`Definition 2.1` / `BoundedNesting.IsHop`):
/// `p + 2 <= u < T`, `y(p) == y(u)`, and `forall t in (p, u), y(t) != y(p)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Revisit {
    pub p: usize,
    pub u: usize,
    pub cell: i64,
    pub excursion: i64,
}

/// Exact dependency DAG of a schedule (`Definition 2.3` / `MergeDepth.DepStep`).
pub struct DepGraph {
    pub t_len: usize,
    /// Deduplicated outgoing dependency edges `u -> v` (`v < u`) for each step `u in 0..T`:
    /// exact union of the state edge `t -> t - 1` (`t >= 1`) and revisit edges `u -> p`.
    pub out: Vec<Vec<usize>>,
    /// Exact revisit list (`IsHop`) for each work tape `j in 0..k`, sorted by `u`.
    pub revisits_by_tape: Vec<Vec<Revisit>>,
}

impl DepGraph {
    /// Build the exact dependency DAG and per-tape revisit lists in `O(k * T log T)` time.
    ///
    /// Matches Section 2 (`Definition 2.1`, `Definition 2.3`) and Lean (`MergeDepth.DepStep`):
    /// - state edges `t -> t - 1` for `1 <= t < T`;
    /// - revisit edge `u -> p` whenever work head `j` returns at step `u` to a cell it left
    ///   after step `p` (`p + 2 <= u`, `y_j(p) == y_j(u)`, `y_j(s) != y_j(p)` on `(p, u)`);
    /// - waiting on a cell (`y_j(u) == y_j(u - 1)`, where the previous visit is `p = u - 1`)
    ///   makes NO revisit edge (`p + 2 <= u` fails).
    pub fn from_schedule(sched: &Schedule) -> Self {
        let t_len = sched.horizon();
        let mut out: Vec<Vec<usize>> = (0..t_len)
            .map(|t| {
                let mut v = Vec::with_capacity(sched.k + 1);
                if t >= 1 {
                    v.push(t - 1); // State edge `t -> t - 1`
                }
                v
            })
            .collect();

        #[derive(Clone, Copy)]
        struct RmVal {
            mx: i64,
            mn: i64,
        }
        const ID: RmVal = RmVal {
            mx: i64::MIN,
            mn: i64::MAX,
        };
        #[inline]
        fn comb(a: RmVal, b: RmVal) -> RmVal {
            RmVal {
                mx: a.mx.max(b.mx),
                mn: a.mn.min(b.mn),
            }
        }

        const BLK: usize = 16;
        let n_blk = (t_len + BLK - 1) / BLK;
        let cap_rm = n_blk.max(1).next_power_of_two();
        let mut rm_tree = vec![ID; 2 * cap_rm];
        let mut revisits_by_tape = Vec::with_capacity(sched.k);

        for j in 0..sched.k {
            let walk = &sched.work_pos[j];
            for bi in 0..n_blk {
                let s = bi * BLK;
                let e = (s + BLK).min(t_len);
                let mut acc = ID;
                for &v in &walk[s..e] {
                    acc = comb(acc, RmVal { mx: v, mn: v });
                }
                rm_tree[cap_rm + bi] = acc;
            }
            for idx in (1..cap_rm).rev() {
                rm_tree[idx] = comb(rm_tree[2 * idx], rm_tree[2 * idx + 1]);
            }
            let query_rm = |l: usize, r: usize| -> RmVal {
                if r - l <= 2 * BLK {
                    let mut acc = ID;
                    for &v in &walk[l..r] {
                        acc = comb(acc, RmVal { mx: v, mn: v });
                    }
                    return acc;
                }
                let bl = (l + BLK - 1) / BLK;
                let br = r / BLK;
                let mut acc = ID;
                for &v in &walk[l..(bl * BLK)] {
                    acc = comb(acc, RmVal { mx: v, mn: v });
                }
                let mut ql = cap_rm + bl;
                let mut qr = cap_rm + br;
                while ql < qr {
                    if (ql & 1) == 1 {
                        acc = comb(acc, rm_tree[ql]);
                        ql += 1;
                    }
                    if (qr & 1) == 1 {
                        qr -= 1;
                        acc = comb(acc, rm_tree[qr]);
                    }
                    ql >>= 1;
                    qr >>= 1;
                }
                for &v in &walk[(br * BLK)..r] {
                    acc = comb(acc, RmVal { mx: v, mn: v });
                }
                acc
            };

            let mut last_visit: HashMap<i64, usize> = HashMap::with_capacity(t_len.min(65536));
            let mut tape_revs = Vec::new();
            for u in 0..t_len {
                let cell = walk[u];
                if let Some(p) = last_visit.insert(cell, u) {
                    if u >= p + 2 {
                        // Structural check: head genuinely left `cell` after step `p` and returned at `u`.
                        assert_ne!(
                            walk[u - 1],
                            cell,
                            "Waiting step u={} erroneously classified as revisit",
                            u
                        );
                        let q = query_rm(p + 1, u);
                        let excursion = (q.mx - cell).max(cell - q.mn);
                        assert!(excursion >= 1);
                        tape_revs.push(Revisit {
                            p,
                            u,
                            cell,
                            excursion,
                        });
                        out[u].push(p);
                    } else {
                        // `u == p + 1`: waiting on `cell` makes NO revisit edge (`Definition 2.1`).
                        debug_assert_eq!(u, p + 1);
                    }
                }
            }
            revisits_by_tape.push(tape_revs);
        }

        for (u, edges) in out.iter_mut().enumerate() {
            edges.sort_unstable();
            edges.dedup();
            for &v in edges.iter() {
                assert!(v < u, "DepGraph edge {} -> {} is not acyclic", u, v);
            }
        }

        Self {
            t_len,
            out,
            revisits_by_tape,
        }
    }

    /// Direct nested-loop `O(k * T^3)` reference check against Lean's definition
    /// `MergeDepth.DepStep xs T a b <-> (b + 1 = a /\ a < T) \/ exists h, IsHop (xs h) T b a`.
    pub fn verify_against_bruteforce(&self, sched: &Schedule) {
        let t_len = sched.horizon();
        assert_eq!(self.t_len, t_len);
        for a in 0..t_len {
            let mut expected = Vec::new();
            if a >= 1 {
                expected.push(a - 1);
            }
            for j in 0..sched.k {
                let y = &sched.work_pos[j];
                for b in 0..a.saturating_sub(1) {
                    // `b + 2 <= a`
                    if y[b] == y[a] && ((b + 1)..a).all(|s| y[s] != y[b]) {
                        expected.push(b);
                    }
                }
            }
            expected.sort_unstable();
            expected.dedup();
            assert_eq!(
                self.out[a], expected,
                "DepStep mismatch vs brute-force quantifier at step a={} on {}",
                a, sched.id
            );
        }
    }
}

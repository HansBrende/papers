# Reproduction Package for Numerical Remarks (`paper16-experiments`)

Self-contained Rust reproduction suite for the finite-size numerical observations ($d \le 128$) reported in *Oblivious Linear-Time Tape Transposers Need Macroscopic Crossings*.

- **License:** Apache 2.0 ([`LICENSE`](LICENSE)).
- **Dependencies:** Rust 2021 edition (`rustc` and `cargo` $\ge 1.75$), standard library (`std`) only, pinned [`Cargo.lock`](Cargo.lock), zero external crates, zero network access at build or run time.
- **Role in the paper:** **No proof in the paper or in the Lean 4 formalization ([`../lean/`](../lean/)) depends on these scripts.** Every number computed here is a finite-size measurement at $d \le 128$, far below the asymptotic thresholds $d_0$ at which the proved theorems apply (for instance $d_0 = 90{,}953$ at $k = 2, C = \alpha = 1, w_{\mathrm{val}} = 8$ in Theorems X and S; see [`../tools/print_constants.py`](../tools/print_constants.py)).

---

## 1. Commands and Expected Results

Run from this `experiments/` directory:

```bash
# Compile in release mode and run unit tests (revisit semantics, cell-entry caps, exporters)
cargo test --release

# Recompute every quoted figure across Suites 0-5 and assert invariants (~1-2 min in --release)
cargo run --release -- check

# List all 30 schedule generators with tape counts, computation kinds, and paper references
cargo run --release -- list

# Export any schedule's complete time-indexed trace as CSV or JSON (to stdout or file)
cargo run --release -- export c4_no_overwrite_cascade 16 1 csv target/c4_d16.csv
cargo run --release -- export ctrl_lsb_radix 8 3 json target/radix_d8.json

# Run an individual measurement suite
cargo run --release -- crossings   # Suite 1: Remark 5.8 crossing min-cuts & E = L acyclic bounds
cargo run --release -- skeletons   # Suite 2: Remarks 6.8 & 10.1 skeletons, single-leg cuts & waves
cargo run --release -- phases      # Suite 3: Section 10.4 coarse phase profiles & Problem 11.1 legs
cargo run --release -- forests     # Suite 4: Problem 11.1 closed interval-forest charges
cargo run --release -- catalogue   # Suite 5: Appendix A "Crossings" column audit
```

### Tested Dimensions, Entry Widths, and Expected Summary (`check`)

`cargo run --release -- check` executes six suites (`Suites 0–5`), prints an explicit `Probe-Simplification & Boundary Audit Notes` ledger, and exits with status `0` (`0 failures`):

- **Suite 0 (Foundations, $d \in \{4, 16, 32, 64, 128\}$):**
  - Checks `DepGraph::from_schedule` and `crossing_lower_steps` edge-for-edge against the literal $O(T^4)$ quantifier of `Section 2` / `MergeDepth.DepStep` at $d = 4, b = 1$ across 10 representative schedules.
  - Verifies bit-level matrix transposition $Y[r] = X[\mathrm{tpos}(d, b, r)]$ on $8$ random trials each at $(d, b) \in \{(16, 4), (32, 1)\}$ for all $7$ superlinear transposer controls.
  - Verifies cell-entry and active-write caps across $d \in \{32, 64, 128\}, b = 1$: `c3_ten_entry_cascade` enters every work cell at most $10$ times (`max_entries = 10`); `c4_no_overwrite_cascade` writes every work cell at most once (`max_active_writes_per_cell = 1`, `max_entries = 9`).
- **Suite 1 (`Remark 5.8`, $d \in \{32, 64, 128\}, b = 1$):**
  - Exact minimum Menger vertex cuts $|B_{\min}(\mathrm{Out}(V_0) \to \mathrm{CL}_{E/2})| / |V_0|$ equal **$1.0000$** across all tested output subsets $V_0$ and all five thresholds $E \in \{2W, L/64, L/16, L/4, L/2\}$ on all five cascade families (`c1`–`c5`, including both `c4_no_overwrite_cascade` and the historical probe `c4_probe_s6_disjoint`) and on two superlinear transposers (`ctrl_lsb_radix` and `ctrl_localized_msb_bfly`).
  - At $E = L$, three cascades (`c3_ten_entry_cascade`, `c4_probe_s6_disjoint`, `c5_comb_fanout`) make $0$ crossings (`|\mathrm{CL}_{L/2}| = 0`), while certified cycle-packing upper bounds on their radius-$D$ acyclic sets at $d = 64$ fall to $0.247 L$, $0.000 L$, and $0.082 L$ by $D = 32$.
- **Suite 2 (`Remarks 6.8 & 10.1`, $d \in \{16, 32, 64, 128\}, b = 1$):**
  - Measured running times $T / L$ of Cascades 1–5 stabilize across $d \in \{32, 64, 128\}$ in $[17.46, 89.19]$ (`18.24` to `89.19` at $d = 128$).
  - At macroscopic scales $\Lambda = L/16$ ($H = L/8$) and $\Lambda_* = \lfloor L/6 \rfloor + 1$ ($H = W$), all five cascades, the one-pass shear (`cat_row03_one_pass_shear`), and the multi-scale Dyck stack (`cat_row24_dyck_mscale`) have bounded, $d$-stabilizing skeletons with a single leg carrying linear Menger expansion ($\ge 0.25 L$), and bounded counts of disjoint $0.25 L$-expanding waves, whereas superlinear transposers (`ctrl_lsb_radix`, `ctrl_localized_msb_bfly`) exhibit strictly growing expanding-chunk and wave counts with $\log_2 d$.
- **Suite 3 (`Section 10.4` & `Problem 11.1`, $d = 128, b \in \{1, 7\}$):**
  - Coarse joint pass counts $M_{\mathrm{ph}}(\lfloor 2^{-s} L \rfloor)$ at $d = 128, b = \lceil \log_2 d \rceil = 7$ ($s = 0\dots 7$) confirm that `c1_torus_cascade`, `c3_ten_entry_cascade`, and `c4_no_overwrite_cascade` sit well above `Corollary 10.4`'s $1/2$ critical slope product ($A_{\mathrm{slope}} \log_2(k + 1) \in \{30.431, 25.600, 39.200\}$).
  - Total all-head skeleton legs $r_j$ (input head included, $d = 128, b = 1$, $j = 1\dots 7$) grow linearly $O(j)$ on the cascades and exponentially $\Theta(2^j)$ on localized butterfly transposers.
- **Suite 4 (`Problem 11.1`, $d \in \{32, 64, 128\}, b = \lceil \log_2 d \rceil$, plus sub-row sweep at $d = 64, b = 1$):**
  - Closed single-scale and localized/span-weighted two-scale interval-forest charges satisfy $\ge 1.0000 L$ on all $5$ tested transposers ($\approx 1.00 L$ on localized transposers), $\approx 2.00 L$ on `c1_torus_cascade`, and $2.62 L\text{–}2.98 L$ ($\approx 3 L$) on `c3_ten_entry_cascade` (`4.00 L` on `c4_no_overwrite_cascade`), never falling below $L$.
- **Suite 5 (`Appendix A`, $d = 64, b = 1$; Row 16 at $d = 16, b = 4$):**
  - Audits all $14$ non-dash `"Crossings"` entries of `Appendix A`, reporting side-by-side minimum cut ratios across output subpopulations $V_0$ under exact `CL_W` + `IsMengerVertexCut`, uncapped Sprint 43 `Mix_{>2W}`, and banded Sprint 43 `Mix_\eta`.

---

## 2. Written Specification of the Dependency Model and Checkers

Let $d \ge 1$, entry width $b \ge 1$, row width $W = d b$, input length $L = d^2 b$, work-tape count $k \ge 1$, and step horizon $T \ge 1$. For $r = (i d + j) b + s \in [0, L)$ ($0 \le i, j < d$, $0 \le s < b$), the transposed input index is $\mathrm{tpos}(d, b, r) = (j d + i) b + s$.

### 2.1 Oblivious Schedules and Time-Indexed Exports ([`src/model.rs`](src/model.rs))

An oblivious schedule specifies:
- Head trajectories $\mathrm{in\_pos} : \{0, \dots, T\} \to \mathbb{Z}$ and $\mathrm{work\_pos}_j : \{0, \dots, T\} \to \mathbb{Z}$ ($0 \le j < k$) starting at cell $0$, with $|\mathrm{pos}(t+1) - \mathrm{pos}(t)| \le 1$ at every step $t \in \{0, \dots, T-1\}$.
- Per-step operations $\mathrm{ops}[t]$ indicating whether step $t$ loads the scanned input cell, how each work tape updates or passes through its scanned cell, and strictly increasing output-append timestamps $0 \le t_0 < t_1 < \dots < t_{L-1} < T$ where output bit $r$ (`target input bit` $\mathrm{tpos}(d, b, r)$) is emitted at step $t_r$.

`export <id> <d> <b> <csv|json>` writes every step $t \in \{0, \dots, T-1\}$ with:
- `step`, `in_pos`, `in_move` ($\in \{-1, 0, +1\}$), `in_scanned_cell` (when in $[0, L)$), `in_loaded` (`0`/`1`),
- for each work tape $j$: `work_j_pos`, `work_j_move` ($\in \{-1, 0, +1\}$), and `work_j_write` (`pass`, `load_in`, `stage_write`, `copy_w*`, `xor_w*`, etc.),
- `append_out_idx` ($r$) and `append_target_input` ($\mathrm{tpos}(d, b, r)$) whenever $t = t_r$.

### 2.2 Exact Dependency DAG (`Section 2`, `MergeDepth.DepStep`)

`DepGraph::from_schedule` constructs the directed acyclic graph on vertices $\{0, \dots, T-1\}$ matching `Definition 2.1`, `Definition 2.3`, `BoundedNesting.IsHop`, and `MergeDepth.DepStep` verbatim:

1. **State edges:** For every $1 \le t < T$, add the directed edge $t \to t - 1$.
2. **Revisit edges (`IsHop`):** On each work tape $j \in \{0, \dots, k-1\}$ with trajectory $y_j$, a pair $(p, u)$ with $0 \le p < u < T$ and $p + 2 \le u$ is a revisit at cell $z = y_j(p) = y_j(u)$ if and only if $y_j(s) \ne z$ for every $p < s < u$. Each revisit adds the directed edge $u \to p$ and has excursion
   $$\mathrm{exc}_j(p, u) \;=\; \max_{p < s < u} |y_j(s) - z| \;\ge\; 1.$$
   **Waiting on a cell makes no revisit:** if $y_j(p+1) = y_j(p)$, then $u = p + 1 < p + 2$, so no revisit edge is added (the state edge $p + 1 \to p$ already carries the cell's value across the stationary step).

### 2.3 Crossing Steps, Menger Cuts, Skeletons, Coarse Passes, and Interval Forests ([`src/checkers.rs`](src/checkers.rs))

- **Crossing lower steps (`Definition 2.2`, `CrossingBridge.crossingLowerEtaSteps`):** Two revisits $(p_1, u_1)$ and $(p_2, u_2)$ on the same tape $j$ *cross* when $p_1 < p_2 < u_1 < u_2$ or $p_2 < p_1 < u_2 < u_1$. For threshold $E \ge 0$, `crossing_lower_steps(dag, E)` returns $\{p < T : \exists j, u, p', u',\; \text{revisits }(p, u), (p', u')\text{ on tape }j\text{ cross with }\mathrm{exc}_j(p, u) > E \text{ and } \mathrm{exc}_j(p', u') > E\}$ (`\mathrm{CL}_H` has $E = 2H$).
- **Minimum separating sets (`Definition 2.4`, `PathSeparation.IsMengerVertexCut`):** For $V_0 \subseteq [0, L)$ with output steps $\mathrm{Out}(V_0) = \{t_r : r \in V_0\}$ and target mask $S \subseteq \{0, \dots, T-1\}$, $B \subseteq \{0, \dots, T-1\}$ separates $\mathrm{Out}(V_0)$ from $S$ iff every directed path in `DepGraph` from $\mathrm{Out}(V_0)$ to $S$ contains a vertex of $B$ (including length-$0$ paths when $t_r \in S$; deleting endpoints is allowed at unit cost). `menger_min_vertex_cut` computes $|B_{\min}|$ via unit-capacity vertex-split Dinic max-flow and asserts unreachability on $\mathrm{DepGraph} \setminus B_{\min}$.
- **Radius-$D$ ball relation and acyclic upper bounds (`Definition 2.5`, `Remark 5.8`):** `extract_ball_avoid_relation` computes, for each output $r$ with $p = \mathrm{tpos}(d, b, r)$, the set of input cells scanned within directed distance $\le D$ from $t_r$ in $\mathrm{DepGraph} \setminus B$. `certified_acyclic_upper_bound` bounds the maximum acyclic subset of $[0, L)$ by packing vertex-disjoint self-loops, $2$-cycles, and short directed cycles ($L$ minus the number of packed cycles is a sound upper bound on every acyclic subset).
- **Greedy $\Lambda$-skeletons and single-leg expansion (`Definitions 6.2 & 6.4`, `Theorem 6.7`):** `extract_tape_skeleton(walk, Lambda)` records grid milestones $y_j(\tau_m) = g_m \Lambda$ whenever $|y_j(t) - g_{m-1}\Lambda| = \Lambda$, grouping consecutive same-sign steps into coarsely monotone legs. `analyze_skeleton_and_single_leg_expansion` partitions crossing lower steps by `(tape j, leg r)` and computes the largest single-leg Menger cut from $\mathrm{Out}([0, L))$.
- **Coarse phase profiles (`Theorem 10.3`, `Corollary 10.4`):** `coarse_phase_profile` counts joint coarse passes across all $k + 1$ heads (`input` plus $k$ work tapes), advancing a pass boundary at the earliest step where some head has moved $> 2 A$ cells since the start of the current pass.
- **Closed interval-forest charges (`Problem 11.1`):** For group width $\gamma$ partitioning the $d$ output entry-rows into $\lceil d / \gamma \rceil$ groups $B$, `evaluate_interval_forest_with_map` forms the closed interval forest $I_B$ (closing output step windows under overlapping work-tape revisits of bounded span so no work cell is entered outside $I_B$ and re-entered inside $I_B$) and sums `|in_reads(I_B) ∩ GroupCols(B)^c| + |entry_points(I_B)| + |entry_cells(I_B)|` across groups (`Theorem P` requires total charge $\ge L$ on every transposer).

---

## 3. Finite Numerical Tests vs. Proved Theorems

**No theorem in the paper or Lean formalization relies on any computation in this crate.** The table below separates what `experiments/` measures at $d \le 128$ from what is proved unconditionally:

| Paper Reference | What Finite Tests Here Show ($d \le 128$, Numerical Only) | What Is Proved Unconditionally (`[Lean]` / `[paper]`) |
|---|---|---|
| **Remark 5.8** (`Section 5.5`) | At $d \in \{32, 64, 128\}, b = 1$, exact min-cuts from $\mathrm{Out}(V_0)$ to $> E$ crossing lowers have size $1.0000\,|V_0|$ for all $E \in \{2W, L/64, L/16, L/4, L/2\}$ on Cascades 1–5 and two superlinear transposers; at $E = L$, three cascades have $0$ crossings while cycle-packing acyclic upper bounds fall towards $0$ by $D = 32$. | **Theorems D & X** (`TightConstants.lean`, `[Lean]`): for *every* linear-time oblivious transposer and all $d \ge d_0$, min-cuts into $\mathrm{CL}_{\lfloor \theta L / 2 \rfloor}$ have size $\ge c_E |V_0|$ with explicit $\theta, c_E > 0$ (`thetaMacro_tight`, `cE_menger_tight`). |
| **Remark 6.8** (`Section 6.3`) | At $d \in \{32, 64, 128\}, b = 1$, Cascades 1–5 and the excluded one-pass shear (`cat_row03_one_pass_shear`) have $d$-stabilizing skeletons with a single leg carrying $\ge 0.25 L$ Menger expansion. | **Theorem S** (`MacroscopicSkeleton.lean`, `TightConstants.lean`, `[Lean]`): at scale $\lfloor \theta L / 4 \rfloor$, every linear-time oblivious transposer has a crossing-capable skeleton from a finite $d$-independent family, with $\ge c_E / (k M_{\max})$ expansion on a single leg; **Theorem J** (`AdaptiveSuffixJitterBM.lean`, `[Lean]`) excludes the one-pass shear unconditionally. |
| **Section 10.3 & Remark 10.1** | Cascades 1–5 have $T/L \in [17.46, 89.19]$ stabilizing as $d$ grows, min-cut ratio $1.0000$ up to $E = L/2$, bounded skeleton legs at $\Lambda \approx L/6$ with single-leg linear expansion, and bounded disjoint expanding waves (unlike superlinear transposers). | **Counting lemma** (`ScaleProfile.lean`, `[Lean]`): any $C(L+1)$-time run has $\le \lfloor 2 C(L+1) / (c \alpha L) \rfloor$ disjoint $c$-expanding waves; whether any machine with one of the five cascade traces transposes is **open** (`Problem 11.4`). |
| **Section 10.4** (`Theorem 10.3`, `Corollary 10.4`) | At $d = 128, b = 7$, Cascades 1, 3, 4 have coarse-pass slope products $A_{\mathrm{slope}} \log_2(k+1) \in [25.6, 39.2] > 1/2$, confirming empirically why `Corollary 10.4` does not exclude them. | **Theorem 10.3 & Corollaries 10.4–10.5** (`CoarseGroupedPass.lean`, `[Lean]`): sub-critical coarse phase profiles ($< 1/2$) and bounded coarse passes up to $\varepsilon L$ are excluded for all oblivious machines (any time) and polynomial-time adaptive machines. |
| **Problem 11.1** (`Section 11`) | At $d \le 128$, closed single-scale and localized/span-weighted two-scale interval forests charge $\ge 1.00 L$ on all tested transposers and $\approx 2 L$ (`c1_torus_cascade`) and $2.62 L\text{–}2.98 L \approx 3 L$ (`c3_ten_entry_cascade`), never $< L$. | **Paper 1 cut lemma** (`FirstPaper2026`, `[Lean]`): closed interval forests must charge $\ge L$ on every transposer; multi-scale pass bounds for $r_j = O(j)$ remain **open** (`Problem 11.1`). |
| **Appendix A** (`"Crossings"` column) | At $d = 64, b = 1$ (`d = 16, b = 4` on Row 16), exact min-cut ratios classify whether Theorem X's crossing barrier looks plausibly applicable (`small`, $\le 0.07$) or inapplicable (`no`, $\ge 0.25$) on 14 representative families. | Exclusions in `Appendix A` rest on **Theorems H, B, J, Q** (`[Lean]` class theorems, Rows 1–20) and written certificate proof sketches built on `Section 3` (`[paper]`, Rows 21–38), never on the numerical `"Crossings"` column. |

---

## 4. Schedule Generators and Computation Kinds ([`src/schedules.rs`](src/schedules.rs))

Every generator carries an explicit `ComputationKind` tag (`cargo run --release -- list`):

1. `actual_transpose_bit_verified` (`7` schedules): executes genuine bit-level work-tape reads, writes, and $\mathbb{F}_2$ XORs that output $Y[r] = X[\mathrm{tpos}(d, b, r)]$ for *every* $X \in \{0, 1\}^L$ (verified on randomized matrices in `Suite 0`). All $7$ run in superlinear time $\Theta(L \log d)$ or $\Theta(d L)$.
2. `explicit_non_transpose_function` (`3` schedules): executes explicit bit-level operations computing a concrete non-transpose map (identity, persistent modular triangles, or linear-time $\mathbb{F}_2$ XOR cascade).
3. `geometry_only` (`20` schedules): prescribes oblivious head motion, input-load scans, active stage writes, and output-append timestamps (routing pass-through symbols rather than computing `transpose`). For Cascades 1–5 (`c1`–`c5`), whether *any* finite-state machine with that oblivious trace transposes is `Problem 11.4`; for the `cat_row*` schedules, `Appendix A` describes why no machine with that trace can transpose at large $d$.

| Schedule ID | $k$ | `ComputationKind` | Min $d$ | Role / Paper Reference |
|---|---:|---|---:|---|
| `c1_torus_cascade` | 2 | `geometry_only` | 16 | Cascade 1 (`§10.3(1)`): symmetric 2D entry-grid cyclic shifts + two-sided cascade |
| `c2_bfly_cascade` | 2 | `geometry_only` | 4 | Cascade 2 (`§10.3(2)`): anti-diagonal reflection + butterfly shifts + two-sided cascade |
| `c3_ten_entry_cascade` | 3 | `geometry_only` | 4 | Cascade 3 (`§10.3(3)`): 3 tapes, $\le 10$ entries/cell, monotone per-stage zones on $w_2$ |
| `c4_no_overwrite_cascade` | 3 | `geometry_only` | 4 | Cascade 4 (`§10.3(4)`): 3 tapes, strictly disjoint un-overwritten forward & backward zones |
| `c4_probe_s6_disjoint` | 3 | `geometry_only` | 4 | Historical probe variant (`S6_disjoint_curved`): disjoint un-overwritten $w_2$, shared $[L, 2L)$ on $w_0, w_1$ |
| `c5_comb_fanout` | 2 | `geometry_only` | 4 | Cascade 5 (`§10.3(5)`): 2-to-1 compressions with $2^r$-tooth comb passes |
| `ctrl_lsb_radix` | 2 | `actual_transpose_bit_verified` | 4 | LSB-to-MSB $O(L \log d)$ radix transposer (`Remarks 5.8 & 10.1`, `§10.4`, `Problem 11.1`) |
| `ctrl_localized_msb_bfly` | 2 | `actual_transpose_bit_verified` | 4 | Localized MSB-to-LSB tile butterfly transposer (`Remarks 5.8 & 10.1`, `§10.4`, `Problem 11.1`) |
| `ctrl_pinned_dfs_bfly` | 2 | `actual_transpose_bit_verified` | 16 | Recursive DFS tile butterfly pinned inside $\Lambda_* = \lfloor L/6 \rfloor + 1$ (`Remarks 6.8 & 10.1`, `Problem 11.1`) |
| `ctrl_xor_butterfly` | 2 | `actual_transpose_bit_verified` | 4 | In-place $\mathbb{F}_2$ XOR 3-shear butterfly transposer (`Problem 11.1`) |
| `ctrl_xor_pinned_dfs` | 2 | `actual_transpose_bit_verified` | 16 | Sub-$\Lambda_*$ pinned DFS $\mathbb{F}_2$ XOR butterfly transposer (`Problem 11.1`) |
| `ctrl_u1_unitslope_bfly` | 3 | `actual_transpose_bit_verified` | 4 | 3-tape unit-slope $O(L \log d)$ butterfly transposer (`§10.4`) |
| `ctrl_d13_one_excursion` | 2 | `actual_transpose_bit_verified` | 4 | Superlinear $\Theta(d L)$ single-stack-excursion transposer (`Appendix A` Row 21–23 contrast) |
| `ctrl_padded_c1` | 2 | `geometry_only` | 16 | Cascade 1 padded by $+3 L$ full-span sweeps (`§10.4` padding control) |
| `ctrl_padded_c3` | 3 | `geometry_only` | 4 | Cascade 3 padded by $+3 L$ full-span sweeps (`§10.4` padding control) |
| `ctrl_xor_cascade_lintime` | 3 | `explicit_non_transpose_function` | 4 | Linear-time 3-tape $\mathbb{F}_2$ XOR cascade computing dense linear combinations (`Problem 11.1`) |
| `cat_row01_direct_copy` | 1 | `explicit_non_transpose_function` | 2 | `Appendix A` Row 1: direct copy (`yes`) |
| `cat_row02_persistent_triangles` | 1 | `explicit_non_transpose_function` | 2 | `Appendix A` Row 2: persistent modular triangles within $b$ cells (`yes`) |
| `cat_row03_one_pass_shear` | 3 | `geometry_only` | 4 | `Appendix A` Row 3 (`Remarks 6.8 & 10.1`): one-pass row-rotation shear, 7 phases (`no`) |
| `cat_row07_unitslope` | 2 | `geometry_only` | 4 | `Appendix A` Row 7: unit-slope constant-velocity passes (`small`) |
| `cat_row08_bounce` | 2 | `geometry_only` | 4 | `Appendix A` Row 8: zig-zag input + nested height-$L/(4d)$ bounce (`small`) |
| `cat_row16_one_free_wave` | 2 | `geometry_only` | 4 | `Appendix A` Row 16: one free head + $O(L/\log d)$ skewed wavefront (`small (16)`) |
| `cat_row24_dyck_mscale` | 2 | `geometry_only` | 4 | `Appendix A` Row 24 (`Remark 10.1`): multi-scale Dyck sawtooth stack + cascade hub (`no`) |
| `cat_row27_gis2_swept` | 10 | `geometry_only` | 64 | `Appendix A` Row 27: swept two-exception inverse-square geometry (`no`) |
| `cat_row28_gis2` | 9 | `geometry_only` | 64 | `Appendix A` Row 28: two-exception inverse-square geometry (`small`) |
| `cat_row29_gis2_gap` | 11 | `geometry_only` | 64 | `Appendix A` Row 29: gapped two-exception inverse-square geometry (`small`) |
| `cat_row30_mirrored_dyadic` | 2 | `geometry_only` | 4 | `Appendix A` Row 30: mirrored dyadic fold cascade (`small`) |
| `cat_row32_dyadic_fold` | 2 | `geometry_only` | 4 | `Appendix A` Row 32: dyadic fold cascade with doubling row blocks (`no`) |
| `cat_row36_lifo_fanout` | 2 | `geometry_only` | 8 | `Appendix A` Row 36: LIFO fan-out cascade of $\log_2 d$ levels (`no`) |
| `cat_row37_tapped_cascade` | 2 | `geometry_only` | 4 | `Appendix A` Row 37: equal-volume tapped meso-scale cascade (`no`) |

---

## 5. Probe Simplifications, Boundary Rounding, and Audit Notes

In keeping with strict transparency (`check` prints all notes automatically under `=== Probe-Simplification & Boundary Audit Notes ===`), we document every difference between the paper's streamlined definitions and the historical exploratory probes (`Sprint 42–50`):

1. **Cascade 4 (`Section 10.3(4)` vs. `Remark 5.8` $E = L$ count):**
   - `Section 10.3(4)` specifies three work tapes where the forward and backward stages use strictly disjoint zones across all scales and no zone is overwritten. `c4_no_overwrite_cascade` implements this literally (`max_active_writes_per_cell = 1`, `max_entries = 9`, $T/L = 54.74 \to 56.42 \to 57.28$ at $d = 32, 64, 128$); because its disjoint zone tree spans $> L$ cells on all three tapes, it retains crossings at $E = L$.
   - The historical probe schedule `S6_disjoint_curved` (shipped alongside it as `c4_probe_s6_disjoint`, $T/L = 28.78 \to 29.40 \to 29.70$) placed disjoint un-overwritten scale zones on tape $w_2$ while reusing $[L, 2L)$ across scales on $w_0, w_1$. That historical variant is the third schedule (alongside `c3_ten_entry_cascade` and `c5_comb_fanout`) that has $0$ crossings at $E = L$ in `Remark 5.8`. Both schedules satisfy min-cut ratio $1.0000$ across all $E \le L/2$, single-leg linear expansion, and bounded expanding waves.
2. **Running-time rounding in `Remark 10.1` ("between $18L$ and $90L$"):**
   - Across $d \in \{32, 64, 128\}, b = 1$, exact $T / L$ spans $[17.46, 89.19]$: `c5_comb_fanout` has $T / L = 17.46$ at $d = 32$, $17.98$ at $d = 64$, and $18.24$ at $d = 128$ (approaching $\approx 18.5 L$, rounded to $18L$ in prose), while `c1_torus_cascade` has $T / L = 87.88, 88.83, 89.19 < 90$.
3. **Finite-$d$ skeleton milestone rounding and `Remark 10.1` scale parameters:**
   - `c5_comb_fanout` and `cat_row03_one_pass_shear` have byte-for-byte identical skeleton words across $d = 32, 64, 128$ at $\Lambda = L/16$ (`and ctrl_pinned_dfs_bfly is byte-for-byte identical across d = 32, 64, 128 at Lambda = floor(L/6) + 1`). On `c1`–`c4`, integer rounding in cyclic shifts (`floor(M_r / 3)`, `(d - 1) b`, and `floor(L/6) + 1`) shifts a few milestone boundaries by $\pm 1\text{–}2$ steps between $d = 32$ and $d = 64$ before stabilizing (`e.g. total legs [32, 32, 32] on c3_ten_entry_cascade and [45, 45, 45] on c2_bfly_cascade at Lambda = L/16`).
   - At $\Lambda_* = \lfloor L/6 \rfloor + 1$ ("scale about $L/6$"), partitioning $\mathrm{CL}_W$ by the legs of the $\Lambda_*$-skeleton gives single-leg Menger expansion $\ge 0.85 L$ on all cascades (and at Theorem S's ratio $H = 2\Lambda$ with $\Lambda = L/16, H = L/8$, all cascades achieve $0.873 L\text{–}1.000 L$). Plugging $H = 2\Lambda_* \approx L/3$ ($2H \approx 2L/3$) exceeds the $L/2$-scale excursions of `c3_ten_entry_cascade`, `c4_probe_s6_disjoint`, and `c5_comb_fanout`.
4. **Interval-forest scale grid in `Problem 11.1` ("about $2L$ and $3L$"):**
   - Evaluating the paper's dyadic scale pairs $(2^{-3} L, 2^{-6} L)$, $(2^{-4} L, 2^{-7} L)$, $(2^{-5} L, 2^{-8} L)$ at canonical entry width $b = \lceil \log_2 d \rceil$ (`Suite 4a`) reproduces $\approx 1.00 L$ on localized transposers, $2.000 L\text{–}2.006 L$ ($\approx 2 L$) on `c1_torus_cascade`, and $2.944 L \to 2.970 L \to 2.985 L$ ($\approx 3 L$) under localized two-scale forests (`2S_Loc_Ex`, and $2.598 L \to 2.622 L \to 2.636 L$ under span-weighted pruning `2S_Opt_Ex`) on `c3_ten_entry_cascade` (`4.000 L` on `c4_no_overwrite_cascade`). Extending the search down to single-cell fine scale $A_1 = 1$ at $b = 1$ (`Suite 4b`) lowers `c3_ten_entry_cascade` to $1.8660 L$ — still far above the $< 1.0000 L$ needed for an exclusion.
5. **Historical `Mix` target set vs. exact `CL_W` in `Appendix A`'s `"Crossings"` column:**
   - The exploratory Sprint 43 probe (`legacy_sprint43_mix_gt2w` and banded `legacy_sprint43_mix_band` with `legacy_nonroot_separator_cut`) grouped revisits by turnaround-to-turnaround cell families (including both endpoints $p$ and $u$ of non-LIFO or multi-load $> 2W$ revisits, plus banded excursion caps $\le \eta L$ for $\eta \in \{1/2, 1/4, 1/8\}$) and forbade deleting output roots. Theorem X (`Section 5.5`) was subsequently streamlined to use only the earlier endpoints of crossing $> 2H$ revisits (`CL_H`) and unrestricted `IsMengerVertexCut`.
   - `Suite 5` computes and prints all three side-by-side (`CL_W_Min`, uncapped `MixGT2W`, and banded `MixBandMin`) across all 14 measured `Appendix A` rows: exact `CL_W` and uncapped `Mix_{>2W}` agree on 11 of the 14 rows (`cat_row01`, `02`, `03`, `16`, `24`, `27`, `28`, `29`, `32`, `36`, `37`), while on `cat_row07_unitslope`, `cat_row08_bounce`, and `cat_row30_mirrored_dyadic` the `"small"` label came from Sprint 43's banded `Mix_\eta` (`0.0000`, `0.0000`, `0.0024`), whereas unbanded `> 2W` frame-turnaround crossings give `CL_W_Min = 1.0000, 0.5010, 1.0000` (all three schedules are excluded formally or by uncut window certificates in `Appendix A`, never by the numerical `"Crossings"` column).

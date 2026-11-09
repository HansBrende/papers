# Reproduction Package for Numerical Remarks (`paper16-experiments`)

Self-contained Rust reproduction suite for the finite-size numerical observations ($d \le 128$) reported in *Oblivious Linear-Time Tape Transposers Need Macroscopic Crossings*.

- **License:** Apache 2.0 ([`LICENSE`](LICENSE)).
- **Dependencies:** Rust 2021 edition (`rustc` and `cargo` $\ge 1.78$, enforced by `rust-version = "1.78"` in [`Cargo.toml`](Cargo.toml) for `Cargo.lock` v4), standard library (`std`) only, pinned [`Cargo.lock`](Cargo.lock), zero external crates, zero network access at build or run time.
- **Role in the paper:** **No proof in the paper or in the Lean 4 formalization ([`../lean/`](../lean/)) depends on these scripts.** Every number computed here is a finite-size measurement at $d \le 128$, far below the asymptotic thresholds $d_0$ at which the proved theorems apply (for instance $d_0 = 90{,}953$ at $k = 2, C = \alpha = 1, w_{\mathrm{val}} = 8$ in Theorems X and S; see [`../tools/print_constants.py`](../tools/print_constants.py)).

---

## 1. Commands and Expected Results

Run from this `experiments/` directory:

```bash
# Compile in release mode and run unit tests (revisit semantics, root exemption, domains, basis check, exporters)
cargo test --release --offline --locked

# Recompute every quoted figure across Suites 0-5 and strictly assert all paper figures (~2 min in --release)
cargo run --release --offline --locked -- check

# List all 30 schedule generators with tape counts, computation kinds, domains, and paper references
cargo run --release --offline --locked -- list

# Export any schedule's complete time-indexed trace as CSV or JSON (to stdout or file)
cargo run --release --offline --locked -- export c4_no_overwrite_cascade 16 1 csv target/c4_d16.csv
cargo run --release --offline --locked -- export ctrl_lsb_radix 8 3 json target/radix_d8.json

# Run an individual measurement suite
cargo run --release --offline --locked -- crossings   # Suite 1: Remark 5.8 crossing min-cuts & E = L acyclic bounds
cargo run --release --offline --locked -- skeletons   # Suite 2: Remarks 6.8 & 10.1 running times, skeletons & single-leg cuts
cargo run --release --offline --locked -- phases      # Suite 3: Section 10.4 coarse phase profiles & Problem 11.1 legs
cargo run --release --offline --locked -- forests     # Suite 4: Problem 11.1 closed 1-scale & 2-scale interval-forest charges
cargo run --release --offline --locked -- catalogue   # Suite 5: Appendix A "Crossings" column & omega(L) transposer checks
```

### Tested Dimensions, Entry Widths, and Strict Assertions (`check`)

`cargo run --release --offline --locked -- check` executes six suites (`Suites 0–5`) in about `2` minutes and exits with status `0` (`0 failures`) only if every figure asserted in the paper's numerical remarks holds:

- **Suite 0 (Foundations, $d \in \{4, 16, 32, 64, 128\}$):**
  - Checks `DepGraph::from_schedule` and `crossing_lower_steps` edge-for-edge against reference nested-loop implementations ($O(k T^3)$ revisit check for `MergeDepth.DepStep` and $O(R^2)$ pairwise crossing check for `CrossingBridge.crossingLowerEtaSteps`) at $d = 4, b = 1$ across 10 schedules.
  - Verifies exact bit-level matrix transposition $Y[r] = X[\mathrm{tpos}(d, b, r)]$ over the zero input and **all $L$ unit basis vectors** (by $\mathbb{F}_2$-linearity of every simulated operation, this certifies exactness on all $2^L$ inputs) at $(d, b) \in \{(16, 4), (32, 1)\}$ for all $7$ superlinear transposer controls. These controls verify the data flow of a time-indexed operation list (`Vec<StepOp>`), not an implementation by a uniform constant-state Turing machine.
  - Verifies cell-entry and active-write caps across $d \in \{32, 64, 128\}, b = 1$: `c3_ten_entry_cascade` enters every work cell at most $10$ times (`max_entries = 10`); `c4_no_overwrite_cascade` writes every work cell at most once (`max_active_writes_per_cell = 1`, `max_entries = 9`).
- **Suite 1 (`Remark 5.8`, $d \in \{32, 64, 128\}, b = 1$):**
  - Exact minimum Menger vertex cuts $|B_{\min}(\mathrm{Out}(V_0) \to \mathrm{CL}_{\lfloor E/2 \rfloor})| / |V_0|$ equal **$1.0000$** across all tested output subsets $V_0$ and all five thresholds $E \in \{2W, L/64, L/16, L/4, L/2\}$ on all five cascades of `Section 10.3` (`c1`–`c5`), on the historical comparator `c4_shared_w01_probe`, and on two superlinear transposers (`ctrl_lsb_radix` and `ctrl_localized_msb_bfly`).
  - At $E = L$, **two** of the five cascades (`c3_ten_entry_cascade` and `c5_comb_fanout`) make $0$ crossings of excursion $> L$ (`|\mathrm{CL}_{L/2}| = 0`), while certified cycle-packing upper bounds on their radius-$D$ acyclic sets at $d = 64, b = 1$ fall to $0.247 L$ ($\approx 0.25 L$) and $0.082 L$ ($\approx 0.08 L$) at $D = 32$.
- **Suite 2 (`Remarks 6.8 & 10.1`, $d \in \{32, 64, 128\}, b = 1$):**
  - Measured running times $T / L$ of Cascades 1–5 across $d \in \{32, 64, 128\}, b = 1$ span **$[17.46, 89.19]$** ("between about $17L$ and $90L$").
  - At scale $\Lambda_* = \lfloor L/6 \rfloor + 1$ ("scale about $L/6$"), work-tape skeletons are **identical** across $d = 32, 64, 128$ on Cascade 5 (`[41, 41, 41]` total legs), on the excluded one-pass shear `cat_row03_one_pass_shear` (`[14, 14, 14]`), and on `ctrl_pinned_dfs_bfly` (`[41, 41, 41]`), and vary by **at most $8$ legs (about $12\%$)** across $d = 32, 64, 128$ on Cascades 1–4 (`[74, 70, 66]`, `[44, 48, 44]`, `[37, 41, 41]`, `[63, 65, 71]`). On all five cascades, a single skeleton leg carries Menger expansion ratio **$1.0000$** at $H = W$, and linear expansion at `Theorem S`'s exact threshold ratio $H = 2\Lambda_*$ (`1.0000` on Cascades 1, 2, and 4, `0.9990–0.9999` on Cascade 3, and `0.6621–0.6664` on Cascade 5 and `ctrl_pinned_dfs_bfly`, as well as $\ge 0.50$ on `cat_row03_one_pass_shear` and `1.0000` on `cat_row24_dyck_mscale` at $H = W$).
- **Suite 3 (`Section 10.4` & `Problem 11.1`, $d = 128, b \in \{1, 7\}$):**
  - Coarse joint pass counts $M_{\mathrm{ph}}(\lfloor 2^{-s} L \rfloor)$ at $d = 128, b = \lceil \log_2 d \rceil = 7$ ($s = 0\dots 7$) give empirical slope products $A_{\mathrm{slope}} \log_2(k + 1)$ of **$30.431$, $25.600$, and $39.200$** ("between $25$ and $40$") on Cascades 1, 3, and 4, far above `Corollary 10.4`'s critical threshold $1/2$.
  - Total all-head skeleton legs $r_j$ (input head included, $d = 128, b = 1$, $j = 1\dots 7$) grow linearly $O(j)$ on Cascades 1, 3, and 4 and exponentially $\Theta(2^j)$ on localized butterfly transposers.
- **Suite 4 (`Problem 11.1`, $d \in \{32, 64, 128\}, b = \lceil \log_2 d \rceil$, plus single-cell sweep at $d = 64, b = 1$):**
  - Closed single-scale and two-scale interval-forest charges satisfy $\ge 1.0004 L \ge L$ on all $5$ tested transposers ($\approx 1.00 L$ on localized transposers). At dyadic scales with $b = \lceil \log_2 d \rceil$, Cascades 1, 3, and 4 have one-scale minima **$2.0000 L\text{–}2.0008 L$** ($\approx 2 L$), **$2.4900 L\text{–}2.5660 L$** ($\approx 2.5 L$), and **$4.0000 L$** ($4 L$), and two-scale minima $2.0001 L\text{–}2.0063 L$, $2.5979 L\text{–}2.9847 L$, and $4.0000 L$. Extending scales down to single cells ($A_1 = 1$ at $d = 64, b = 1$) gives one-scale minima **$1.6282 L$** ($1.63 L$), **$1.6396 L$** ($1.64 L$), and **$4.0000 L$** ($4 L$) on Cascades 1, 3, and 4 (`1.8660 L` two-scale on Cascade 3), never falling below $L$.
- **Suite 5 (`Appendix A`, $d = 64, b = 1$; Row 16 at $d = 16, b = 4$; $\omega(L)$ controls at $d = 32, b = 1$):**
  - Asserts all $14$ non-dash `"Crossings"` entries of `Appendix A` strictly under the paper's definition (`CL_W` + `OneFreeHeadSmallExcursion.IsMengerVertexCut`), printing legacy `Mix` quantities strictly as labelled diagnostics, and verifies crossing separator ratio `1.0000` at threshold $2W$ on all $7$ bit-verified $\omega(L)$ transposers (six $\Theta(L \log d)$ transposers plus the $\Theta(d^{1/3} L)$ single-stack-excursion transposer outside linear time).

---

## 2. Written Specification of the Dependency Model and Checkers

Let $d \ge 1$, entry width $b \ge 1$, row width $W = d b$, input length $L = d^2 b$, work-tape count $k \ge 1$, and step horizon $T \ge 1$. For $r = (i d + j) b + s \in [0, L)$ ($0 \le i, j < d$, $0 \le s < b$), the transposed input index is $\mathrm{tpos}(d, b, r) = (j d + i) b + s$.

### 2.1 Oblivious Schedules and Time-Indexed Exports ([`src/model.rs`](src/model.rs))

An oblivious schedule specifies:
- Head trajectories $\mathrm{in\_pos} : \{0, \dots, T-1\} \to \mathbb{Z}$ and $\mathrm{work\_pos}_j : \{0, \dots, T-1\} \to \mathbb{Z}$ ($0 \le j < k$) starting at cell $0$, with $|\mathrm{pos}(t+1) - \mathrm{pos}(t)| \le 1$ at every step.
- Per-step operations $\mathrm{ops}[t]$ indicating whether step $t$ loads the scanned input cell, how each work tape updates or passes through its scanned cell, and strictly increasing output-append timestamps $0 \le t_0 < t_1 < \dots < t_{L-1} < T$ where output bit $r$ (`target input bit` $\mathrm{tpos}(d, b, r)$) is emitted at step $t_r$.

`export <id> <d> <b> <csv|json>` writes every step $t \in \{0, \dots, T-1\}$ with `step`, `in_pos`, `in_move`, `in_scanned_cell`, `in_loaded`, per-work-tape `work_j_pos`, `work_j_move`, `work_j_write`, `append_out_idx` ($r$), and `append_target_input` ($\mathrm{tpos}(d, b, r)$).

### 2.2 Exact Dependency DAG (`Section 2`, `MergeDepth.DepStep`)

`DepGraph::from_schedule` constructs the directed acyclic graph on vertices $\{0, \dots, T-1\}$ matching `Definition 2.1`, `Definition 2.3`, `BoundedNesting.IsHop`, and `MergeDepth.DepStep`:

1. **State edges:** For every $1 \le t < T$, add the directed edge $t \to t - 1$.
2. **Revisit edges (`IsHop`):** On each work tape $j \in \{0, \dots, k-1\}$ with trajectory $y_j$, a pair $(p, u)$ with $0 \le p < u < T$ and $p + 2 \le u$ is a revisit at cell $z = y_j(p) = y_j(u)$ if and only if $y_j(s) \ne z$ for every $p < s < u$. Each revisit adds the directed edge $u \to p$ and has excursion
   $$\mathrm{exc}_j(p, u) \;=\; \max_{p < s < u} |y_j(s) - z| \;\ge\; 1.$$
   **Waiting on a cell makes no revisit:** if $y_j(p+1) = y_j(p)$, then $u = p + 1 < p + 2$, so no revisit edge is added (the state edge $p + 1 \to p$ already carries the cell's value across the stationary step).

### 2.3 Crossing Steps, Menger Cuts, Skeletons, Coarse Passes, and Interval Forests ([`src/checkers.rs`](src/checkers.rs))

- **Crossing lower steps (`Definition 2.2`, `CrossingBridge.crossingLowerEtaSteps`):** Two revisits $(p_1, u_1)$ and $(p_2, u_2)$ on the same tape $j$ *cross* when $p_1 < p_2 < u_1 < u_2$ or $p_2 < p_1 < u_2 < u_1$. For threshold $E \ge 0$, `crossing_lower_steps(dag, E)` returns $\{p < T : \exists j, u, p', u',\; \text{revisits }(p, u), (p', u')\text{ on tape }j\text{ cross with }\mathrm{exc}_j(p, u) > E \text{ and } \mathrm{exc}_j(p', u') > E\}$ (`\mathrm{CL}_H` has $E = 2H$).
- **Minimum separating sets (`Definition 2.4`, `OneFreeHeadSmallExcursion.IsMengerVertexCut`) and $V_0$ indexing:** For $V_0 \subseteq [0, L)$ with output steps $\mathrm{Out}(V_0) = \{t_r : r \in V_0\}$ and target mask $S \subseteq \{0, \dots, T-1\}$, $B \subseteq \{0, \dots, T-1\}$ separates $\mathrm{Out}(V_0)$ from $S$ iff every directed path in `DepGraph` from $\mathrm{Out}(V_0)$ to $S$ contains a vertex of $B$ (including length-$0$ paths when $t_r \in S$; deleting endpoints is allowed at unit cost). `menger_min_vertex_cut` computes $|B_{\min}|$ via unit-capacity vertex-split Dinic max-flow and verifies unreachability on $\mathrm{DepGraph} \setminus B_{\min}$. Note on indexing: `standard_subpopulations` indexes $V_0$ directly by **output position** $r \in [0, L)$ (`\mathrm{Out}(V_0) = \{t_r : r \in V_0\}`), whereas the paper's formal statements index $V_0$ by **input position** $p \in [0, L)$ (whose output step is $t_{\mathrm{tpos}(d, b, p)}$); since $\mathrm{tpos}(d, b, \cdot)$ is a bijection preserving size and mapping input rows, columns, quadrants, and parity slices onto output columns, rows, transposed quadrants, and parity slices, the collection of tested subsets is closed under $\mathrm{tpos}$.
- **Radius-$D$ ball relation and acyclic upper bounds (`Definition 2.5`, `EnvelopeCrux.ballAvoidSystem`, `Remark 5.8`):** `extract_ball_avoid_relation` computes, for each output $r$ with $p = \mathrm{tpos}(d, b, r)$, the set of input cells scanned at vertices reachable from root $t_r$ within $\le D$ edges by paths whose non-root vertices avoid $B$ (the root $t_r$ itself is exempt even if $t_r \in B$, matching `GFree`). `certified_acyclic_upper_bound` bounds the maximum acyclic subset of $[0, L)$ by packing vertex-disjoint self-loops, mutual cliques, and directed $3$-cycles.
- **Greedy $\Lambda$-skeletons and single-leg expansion (`Definition 6.2`, `MacroscopicSkeleton.tapeSkeleton`, `Theorem S`):** `extract_tape_skeleton(walk, Lambda)` records grid milestones $y_j(\tau_m) = g_m \Lambda$ whenever $|y_j(t) - g_{m-1}\Lambda| = \Lambda$, grouping consecutive same-sign steps into coarsely monotone legs. `analyze_skeleton_and_single_leg_expansion` partitions crossing lower steps by `(tape j, leg r)` and computes the largest single-leg Menger cut from $\mathrm{Out}([0, L))$.
- **Coarse phase profiles (`Theorem 10.3`, `Corollary 10.4`, `CoarseGroupedPass.CoarseMonoOnInterval`):** `coarse_phase_profile` partitions $\{0, \dots, T-1\}$ greedily from left to right into maximal intervals on which every head (`input` plus all $k$ work tapes) satisfies `CoarseMonoOnInterval` at amplitude $A = \lfloor 2^{-s} L \rfloor$: either the head never drops by more than $A$ below its running maximum on the interval, or it never rises by more than $A$ above its running minimum. Because `CoarseMonoOnInterval` is hereditary on sub-intervals, greedy left-to-right scanning achieves the exact minimum pass count.
- **Closed interval-forest charges (`Problem 11.1`):** For group width $\gamma$ partitioning the $d$ output entry-rows into $\lceil d / \gamma \rceil$ groups $B$ (whose target transpose entries are the input columns $\mathrm{GroupCols}(B)$ of the same indices), `evaluate_interval_forest_with_map` forms the closed interval forest $I_B$ and sums `|in_reads(I_B) ∩ GroupCols(B)| + |entry_points(I_B)| + |entry_cells(I_B)|` across groups (`Paper 1`'s cut lemma requires total charge $\ge L$ on every transposer).

---

## 3. Finite Numerical Tests vs. Proved Theorems

**No theorem in the paper or Lean formalization relies on any computation in this crate.** The table below separates what `experiments/` measures at $d \le 128$ from what is proved unconditionally:

| Paper Reference | What Finite Tests Here Show ($d \le 128$, Numerical Only) | What Is Proved (`[Lean]` / `[paper]`) |
|---|---|---|
| **Remark 5.8** (`Section 5.5`) | At $d \in \{32, 64, 128\}, b = 1$, exact min-cuts from $\mathrm{Out}(V_0)$ to $> E$ crossing lowers have size $1.0000\,|V_0|$ for all $E \in \{2W, L/64, L/16, L/4, L/2\}$ on Cascades 1–5 and two superlinear transposers; at $E = L$, two cascades (`c3` and `c5`) have $0$ crossings while cycle-packing acyclic upper bounds at $d = 64$ fall to $0.247 L$ and $0.082 L$ at $D = 32$. | **Theorems D & X** (`TightConstants.lean`, `[Lean]`): for *every* linear-time oblivious transposer and all $d \ge d_0$, min-cuts into $\mathrm{CL}_{\lfloor \theta L / 2 \rfloor}$ have size $\ge c_E |V_0|$ with explicit $\theta, c_E > 0$ (`thetaMacro_tight`, `cE_menger_tight`). |
| **Remark 6.8** (`Section 6.3`) | At $\Lambda_* = \lfloor L/6 \rfloor + 1$ and $d \in \{32, 64, 128\}, b = 1$, work-tape skeletons are identical across $d$ on Cascade 5 and `cat_row03_one_pass_shear` and vary within $8$ legs ($\approx 12\%$) on Cascades 1–4, with a single leg carrying linear Menger expansion. | **Theorem S** (`MacroscopicSkeleton.lean`, `TightConstants.lean`, `[Lean]`): at scale $\lfloor \theta L / 4 \rfloor$, every linear-time oblivious transposer has a crossing-capable skeleton from a finite $d$-independent family, with $\ge c_E / (k M_{\max})$ expansion on a single leg. The one-pass shear (`cat_row03_one_pass_shear`, defined for even $d$) is excluded along even $d$ via **Theorem J** as a proof sketch (`Appendix A`). |
| **Section 10.3 & Remark 10.1** | Cascades 1–5 have $T/L \in [17.46, 89.19]$, min-cut ratio $1.0000$ up to $E = L/2$, and $\Lambda_*$-skeletons changing by $0$ legs on Cascade 5 and $\le 8$ legs ($\approx 12\%$) on Cascades 1–4 with single-leg expansion $1.0000$ at $H = W$ and linear expansion (`0.662–1.000`) at $H = 2\Lambda_*$. Conditions (iii) and (iv) of `Section 10.1` were not measured. | **Theorems X & S** (`TightConstants.lean`, `[Lean]`) establish conditions (i)–(ii), **Theorem H** (`OneFreeHeadSmallExcursion.lean`, `[Lean]`) establishes (iii), and **Lemma R** (`TranspositionCut.lean`, `[Lean]`) establishes (iv); whether any machine with one of the five cascade traces transposes is **open** (`Problem 11.4`). |
| **Section 10.4** (`Theorem 10.3`, `Corollary 10.4`) | At $d = 128, b = 7$, Cascades 1, 3, and 4 have coarse-pass slope products $30.431, 25.600, 39.200 \in [25, 40]$, far above `Corollary 10.4`'s threshold $1/2$. | **Theorem 10.3 & Corollaries 10.4–10.5** (`CoarseGroupedPass.lean`, `[Lean]`): sub-critical coarse phase profiles ($< 1/2$) and bounded coarse passes up to $\varepsilon L$ are excluded for all oblivious machines (any time) and polynomial-time adaptive machines. |
| **Problem 11.1** (`Section 11`) | Closed interval forests charge $\ge 1.0004 L$ on all 5 tested transposers; on Cascades 1, 3, and 4, minima are $\approx 2 L, 2.5 L, 4 L$ (1-scale) and $\approx 2 L, 2.6\text{–}3.0 L, 4 L$ (2-scale) at dyadic scales ($b = \lceil \log_2 d \rceil$), and $1.63 L, 1.64 L, 4.00 L$ down to single cells ($d = 64, b = 1$). | **Paper 1 cut lemma** (`FirstPaper2026`, `[Lean]`): closed interval forests must charge $\ge L$ on every transposer; multi-scale pass bounds for $r_j = O(j)$ remain **open** (`Problem 11.1`). |
| **Appendix A** (`"Crossings"` column) | At $d = 64, b = 1$ (`d = 16, b = 4` on Row 16), exact `CL_W` min-cut ratios classify whether Theorem X's crossing barrier looks plausibly applicable (`small`, $\le 0.07$) or inapplicable (`no`, $\ge 0.25$) on 14 representative families, and verify ratio $1.0000$ on all seven $\omega(L)$ transposers. | Exclusions in `Appendix A` rest on **Corollary H** and **Theorems B, J, Q** (`[Lean]` class theorems, Rows 1–20; applied along domain restrictions as noted in `Appendix A`) and written certificate proof sketches built on `Section 3` (`[paper]`, Rows 21–38), never on the numerical `"Crossings"` column. |

---

## 4. Schedule Generators and Computation Kinds ([`src/schedules.rs`](src/schedules.rs))

Every generator carries an explicit `ComputationKind` tag and `DomainRule` (`cargo run --release -- list`):

1. `actual_transpose_bit_verified` (`7` schedules): executes time-indexed bit-level work-tape reads, writes, and $\mathbb{F}_2$ XORs (`Vec<StepOp>`, not a uniform constant-state machine) verified over the zero vector and all $L$ unit vectors in `Suite 0` to output $Y[r] = X[\mathrm{tpos}(d, b, r)]$ for every $X \in \{0, 1\}^L$. Six run in $\Theta(L \log d)$ time and one (`ctrl_d13_one_excursion`) runs in $\Theta(d^{1/3} L)$ time.
2. `explicit_non_transpose_function` (`3` schedules): executes explicit bit-level operations computing a concrete non-transpose map (identity, persistent modular triangles, or linear-time $\mathbb{F}_2$ XOR cascade).
3. `geometry_only` (`20` schedules): prescribes oblivious head motion, input-load scans, active stage writes, and output-append timestamps without claiming a uniform machine that computes `transpose`. For Cascades 1–5 (`c1`–`c5`), whether *any* finite-state machine with that oblivious trace transposes is `Problem 11.4`; for the `cat_row*` schedules, `Appendix A` describes why no machine with that trace can transpose at large $d$.

| Schedule ID | $k$ | `ComputationKind` | Domain | Role / Paper Reference |
|---|---:|---|---|---|
| `c1_torus_cascade` | 2 | `geometry_only` | $d \ge 16, 2^m$ | Cascade 1 (`§10.3(1)`): symmetric 2D entry-grid cyclic shifts + two-sided cascade |
| `c2_bfly_cascade` | 2 | `geometry_only` | $d \ge 4, 2^m$ | Cascade 2 (`§10.3(2)`): full reversal (half-turn of entry grid) + butterfly shifts + two-sided cascade |
| `c3_ten_entry_cascade` | 3 | `geometry_only` | $d \ge 4, 2^m$ | Cascade 3 (`§10.3(3)`): 3 tapes, $\le 10$ entries/cell, monotone per-stage zones on $w_2$ |
| `c4_no_overwrite_cascade` | 3 | `geometry_only` | $d \ge 4, 2^m$ | Cascade 4 (`§10.3(4)`): 3 tapes, strictly disjoint un-overwritten forward & backward zones |
| `c4_shared_w01_probe` | 3 | `geometry_only` | $d \ge 4, 2^m$ | Historical comparator: disjoint un-overwritten $w_2$ zones, shared $[L, 2L)$ on $w_0, w_1$ |
| `c5_comb_fanout` | 2 | `geometry_only` | $d \ge 4, 2^m$ | Cascade 5 (`§10.3(5)`): initial load onto $w_0$, 2-to-1 compressions with $2^r$-tooth comb passes |
| `ctrl_lsb_radix` | 2 | `actual_transpose_bit_verified` | $d \ge 4, 2^m$ | LSB-to-MSB $\Theta(L \log d)$ radix transposer (`Remark 5.8`, `§10.4`, `Problem 11.1`) |
| `ctrl_localized_msb_bfly` | 2 | `actual_transpose_bit_verified` | $d \ge 4, 2^m$ | Localized MSB-to-LSB tile butterfly transposer, $\Theta(L \log d)$ (`Remark 5.8`, `§10.4`, `Problem 11.1`) |
| `ctrl_pinned_dfs_bfly` | 2 | `actual_transpose_bit_verified` | $d \ge 16, 2^m$ | Recursive DFS tile butterfly pinned inside $\Lambda_* = \lfloor L/6 \rfloor + 1$, $\Theta(L \log d)$ (`Remark 6.8`, `Problem 11.1`) |
| `ctrl_xor_butterfly` | 2 | `actual_transpose_bit_verified` | $d \ge 4, 2^m$ | In-place $\mathbb{F}_2$ XOR 3-shear butterfly transposer, $\Theta(L \log d)$ (`Problem 11.1`) |
| `ctrl_xor_pinned_dfs` | 2 | `actual_transpose_bit_verified` | $d \ge 16, 2^m$ | Sub-$\Lambda_*$ pinned DFS $\mathbb{F}_2$ XOR butterfly transposer, $\Theta(L \log d)$ (`Problem 11.1`) |
| `ctrl_u1_unitslope_bfly` | 3 | `actual_transpose_bit_verified` | $d \ge 4, 2^m$ | 3-tape unit-slope $\Theta(L \log d)$ butterfly transposer (`§10.4`) |
| `ctrl_d13_one_excursion` | 2 | `actual_transpose_bit_verified` | $d \ge 4$ | Superlinear $\Theta(d^{1/3} L)$ single-stack-excursion transposer (`Appendix A` superlinear check) |
| `ctrl_padded_c1` | 2 | `geometry_only` | $d \ge 16, 2^m$ | Cascade 1 padded with $\lceil \log_2 d \rceil$ full-bank sweeps, $\Theta(L \log d)$ (`§10.4`) |
| `ctrl_padded_c3` | 3 | `geometry_only` | $d \ge 4, 2^m$ | Cascade 3 padded with $\lceil \log_2 d \rceil$ full-bank sweeps, $\Theta(L \log d)$ (`§10.4`) |
| `ctrl_xor_cascade_lintime` | 3 | `explicit_non_transpose_function` | $d \ge 8, 2^m$ | Linear-time 3-tape $\mathbb{F}_2$ XOR cascade computing dense non-transpose parities (`Problem 11.1`) |
| `cat_row01_direct_copy` | 1 | `explicit_non_transpose_function` | $d \ge 2$ | `Appendix A` Row 1: direct copy (`yes`) |
| `cat_row02_persistent_triangles` | 1 | `explicit_non_transpose_function` | $d \ge 2$ | `Appendix A` Row 2: persistent modular triangles within $b$ cells (`yes`) |
| `cat_row03_one_pass_shear` | 3 | `geometry_only` | $d \ge 4$, even | `Appendix A` Row 3 (`Remarks 6.8 & 10.1`): one-pass row-rotation shear, 7 phases (`no`) |
| `cat_row07_unitslope` | 2 | `geometry_only` | $d \ge 4$ | `Appendix A` Row 7: unit-slope constant-velocity passes (`no`) |
| `cat_row08_bounce` | 2 | `geometry_only` | $d \ge 4$ | `Appendix A` Row 8: zig-zag input + nested height-$L/(4d)$ bounce (`no`) |
| `cat_row16_one_free_wave` | 2 | `geometry_only` | $d \ge 4, 2^m$ | `Appendix A` Row 16: one free head + $O(L/\log d)$ skewed wavefront (`small (16)`) |
| `cat_row24_dyck_mscale` | 2 | `geometry_only` | $d \ge 4, 2^m$ | `Appendix A` Row 24 (`Remark 10.1`): multi-scale Dyck sawtooth stack + cascade hub (`no`) |
| `cat_row27_gis2_swept` | 10 | `geometry_only` | $d \ge 64$ | `Appendix A` Row 27: swept two-exception inverse-square geometry (`no`) |
| `cat_row28_gis2` | 9 | `geometry_only` | $d \ge 64$ | `Appendix A` Row 28: two-exception inverse-square geometry (`small`) |
| `cat_row29_gis2_gap` | 11 | `geometry_only` | $d \ge 64$ | `Appendix A` Row 29: gapped two-exception inverse-square geometry (`small`) |
| `cat_row30_mirrored_dyadic` | 2 | `geometry_only` | $d \ge 4, 2^m$ | `Appendix A` Row 30: mirrored dyadic fold cascade (`no`) |
| `cat_row32_dyadic_fold` | 2 | `geometry_only` | $d \ge 4, 2^m$ | `Appendix A` Row 32: dyadic fold cascade with doubling row blocks (`no`) |
| `cat_row36_lifo_fanout` | 2 | `geometry_only` | $d \ge 8, 2^m$ | `Appendix A` Row 36: LIFO fan-out cascade of $\log_2 d$ levels (`no`) |
| `cat_row37_tapped_cascade` | 2 | `geometry_only` | $d \ge 4, 2^m$ | `Appendix A` Row 37: equal-volume tapped meso-scale cascade (`no`) |

---

## 5. Implementation and Historical Comparator Notes

1. **Cascade 4 (`Section 10.3(4)`) vs. Historical Comparator (`c4_shared_w01_probe`) at $E = L$:**
   - `Section 10.3(4)` specifies three work tapes where the forward and backward stages use strictly disjoint zones across all scales and no zone is overwritten. `c4_no_overwrite_cascade` implements this literally (`max_active_writes_per_cell = 1`, `max_entries = 9`, $T/L = 54.74, 56.42, 57.28$ at $d = 32, 64, 128$). On `c4_no_overwrite_cascade`, tape $w_0$ has **no** crossings at $E = L$, whereas tapes $w_1$ and $w_2$ retain crossings of excursion $> L$ when moving between widely separated scale zones (`|\mathrm{CL}_{L/2}| > 0`). Thus among Cascades 1–5 of `Section 10.3`, **two** (`c3_ten_entry_cascade` and `c5_comb_fanout`) have $0$ crossings at $E = L$ (`Remark 5.8`).
   - An earlier exploratory schedule (`c4_shared_w01_probe`, retained only as a labelled historical comparator, $T/L = 28.78, 29.40, 29.70$) placed disjoint un-overwritten scale zones on $w_2$ while reusing $[L, 2L)$ across scales on $w_0$ and $w_1$, which gave $0$ crossings on all three tapes at $E = L$.
2. **Exact Running-Time Range (`Remark 10.1`):**
   - Across $d \in \{32, 64, 128\}, b = 1$, exact $T / L$ on Cascades 1–5 spans **$17.46$ to $89.19$** ("between about $17L$ and $90L$"): `c5_comb_fanout` has $T / L = 17.46, 17.98, 18.24$ (loading the input onto $w_0$ initially, while Cascades 1–2 load onto two work tapes and Cascades 3–4 onto three), `c3_ten_entry_cascade` has $28.81, 29.56, 29.95$, `c2_bfly_cascade` has $34.01, 34.75, 35.12$, `c4_no_overwrite_cascade` has $54.74, 56.42, 57.28$, and `c1_torus_cascade` has $87.88, 88.83, 89.19$.
3. **Skeleton Leg Totals and `H = 2\Lambda_*` Expansion (`Remarks 6.8 & 10.1`):**
   - At $\Lambda_* = \lfloor L/6 \rfloor + 1$ ("scale about $L/6$"), total work-tape skeleton legs across $d = [32, 64, 128]$ are `[41, 41, 41]` on `c5_comb_fanout` (byte-for-byte identical skeleton words), `[14, 14, 14]` on `cat_row03_one_pass_shear` (identical), `[41, 41, 41]` on `ctrl_pinned_dfs_bfly` (identical), and `[74, 70, 66]`, `[44, 48, 44]`, `[37, 41, 41]`, `[63, 65, 71]` on Cascades 1–4 (each within $\le 8$ legs, about $12\%$, due to integer rounding in $\lfloor M_r / 3 \rfloor$, $(d - 1)b$, and $\lfloor L/6 \rfloor + 1$).
   - At `Theorem S`'s exact threshold ratio $H = 2\Lambda_*$ ($2H = 4\Lambda_* \approx 2L/3 < L - 1$), the full-span $[0, L)$ sweeps of Cascades 1–5 exceed $2H$, so $\mathrm{CL}_{2\Lambda_*}$ is nonempty on all five cascades and a single skeleton leg carries linear Menger expansion (`1.0000` on Cascades 1, 2, and 4, `0.9990–0.9999` on Cascade 3, and `0.6621–0.6664` on Cascade 5 and `ctrl_pinned_dfs_bfly`, while at $H = W$ the single-leg Menger expansion ratio is `1.0000` on all five cascades).
4. **One-Scale and Two-Scale Interval-Forest Minima (`Problem 11.1`):**
   - At dyadic scales ($A \in \{2^{-3} L, \dots, 2^{-8} L\}$ and pairs $(2^{-3} L, 2^{-6} L), \dots, (2^{-5} L, 2^{-8} L)$) with $b = \lceil \log_2 d \rceil$, minimum one-scale exact charges are $2.0000 L\text{–}2.0008 L$ ($\approx 2 L$) on Cascade 1, $2.4900 L\text{–}2.5660 L$ ($\approx 2.5 L$) on Cascade 3, and $4.0000 L$ ($4 L$) on Cascade 4, while two-scale charges are $2.0001 L\text{–}2.0063 L$, $2.5979 L\text{–}2.9847 L$, and $4.0000 L$. Sweeping scales down to single cells ($A_1 = 1$ at $d = 64, b = 1$) lowers Cascade 1 and Cascade 3 one-scale minima to $1.6282 L$ ($1.63 L$) and $1.6396 L$ ($1.64 L$) (`4.0000 L` on Cascade 4) — every tested charge remains strictly above $L$.
5. **Exact `CL_W` vs. Legacy `Mix` Diagnostics (`Appendix A`):**
   - `Suite 5` asserts strictly on the paper's `CL_W` + `IsMengerVertexCut`. Exact `CL_W` and uncapped `Mix_{>2W}` (`DiagMixGT2W`) **agree on all 14 measured rows** (`yes` on rows 1–2; `small` on rows 16, 28, 29; `no` on rows 3, 7, 8, 24, 27, 30, 32, 36, 37). On rows 7, 8, and 30 (`CL_W_Min = 1.0000, 0.5010, 1.0000`), only the legacy excursion-capped `DiagMixBand` diagnostic gave $\le 0.07$; `Appendix A` lists `"no"` for rows 7, 8, and 30 in agreement with `CL_W`.

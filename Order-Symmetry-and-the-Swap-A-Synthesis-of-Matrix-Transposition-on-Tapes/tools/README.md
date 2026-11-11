# Tools

Every script that was used for the paper: the generators of generated files, the exact computations behind the
numerical remarks and the section on small sizes, and small-instance checks of statements that are proved in the text
but not formalized. Run them from the paper's directory (the parent of `paper/`, `lean/` and `tools/`). Each script
documents its usage at its top. Apart from the two generators, no script is used in a proof, and the Lean library
does not depend on any of them.

The side length is `d` in the paper and `n` in most scripts. A partition of Z_n is written `"0,1,3|2,4,5"`.

**Requirements.** Python 3. `exhaustive_flag_checks.py` and `exhaustive_pigeonhole_checks.py` need NumPy;
`class_uniform_sat.py`, and the subcommands `climb` and `controls` of `small_sizes.py`, need the package
`pycryptosat` (CryptoMiniSat); `acyclic_set_search.py` needs OR-tools (`pip install ortools`). Everything else uses
the standard library only. The results in the paper were obtained with Python 3.12.10, NumPy 2.5.4, pycryptosat
5.18.0 and OR-tools 9.15.

| Script | What it reproduces | Needs | Time |
|---|---|---|---|
| `lean_index.py` | `paper/sections/leanindex.tex` and `lean/PaperAxioms.lean` | — | seconds |
| `gen_aperiodic_example.py` | `lean/SwapRigidity/AperiodicExampleData.lean`, from `data/aperiodic_d6_dim25.json` | — | seconds |
| `exhaustive_flag_checks.py` | Section "Order": Theorem FL and its corollaries on small instances; the numbers of Remark (numerical: the bound is not always tight) | NumPy | about 90 s |
| `three_term_example.py` | Remark (two is sharp): τ − Π and the three-term example at d = 4 | — | seconds |
| `exhaustive_pigeonhole_checks.py` | Section "Symmetry": the pigeonhole lemma, Theorem TP, the line form and twist classes on small instances; the numbers of Remark (numerical: what the exact value does not say) and Remark (numerical: on a line, other shifts fail); the rows d ≤ 4 of the table of small sizes | NumPy | about 45 s |
| `digit_and_composition_checks.py` | Corollary (every address digit must be broken) and Remark (composition), including the unshuffle | — | seconds |
| `entry_form_check.py` | Proposition (changes that affect single entries): every rule at d = 2 over GF(2), random rules and rules with free entries up to d = 5, and the rules of the saved codes; with controls that group the changes differently and must fail | — | seconds |
| `two_class_family.py` | Proposition (two classes: a gain of d/4 − 1 over every field): the rule in closed form with a general coefficient, every rank stated in the proof for d ≤ 48 over GF(2), GF(3), GF(5), GF(7), GF(11), the dimension over GF(2) for d ≤ 100, and the saved codes `data/two_class_d8.json`, `_d12.json`, `_d16.json`. Corollary (every fixed number of classes): the blow-up rule for M = 3, ..., 7 and its largest code | — | seconds |
| `set_bounds_check.py` | Proposition (two bounds for sets): the exact largest code of every recovery relation at d = 2 over two symbols, against the acyclic-subgraph bound and both parts of the proposition; the step of both proofs over all pairs of matrices, for 40 random relations at d = 3 over two symbols and 60 at d = 2 over three, and that it holds exactly when the relation has no cycle outside the supplied set; for the cyclic instance at d ≤ 12, its hypothesis, its exponent and the absence of cycles on random relations; the count of cycles of part (b) on random class maps at d ≤ 8; the remark on marker rows (every matrix of the set at d = 4, a sample at d = 16 with eight classes); three controls that must fail. Also the count of classes of the perfect shuffle in the section "From the one-hop model to machines" | — | about 20 s |
| `order_bounds_check.py` | Propositions (order bounds for one-class relations) and (mutual helpers and transitive triangles): the ranking lemma on every multigraph with at most five vertices and as many edges, and its sharpness for at most four; the row and column sets on random relations; exact least hitting sets of the cycles at d = 3, 4 for window two; the count of part (c) and the Dirichlet multiplier on random instances; the two counts of the second proposition against enumeration; the two local codes named after it; the examples after the first proposition (the cycle for the ranking lemma, the relation at d = 3 that attains the bound of window two, the codes with d²/2 + d free entries at d = 4 and 6, whole rows at d = 4); two controls | — | about 15 s |
| `acyclic_set_search.py` | The searches reported at the end of the section on sets: large acyclic sets in one-class relations with random maps and in an unstructured digraph, with a control family; exact least hitting sets for the pairing plus random helpers | OR-tools | see below |
| `small_sizes.py` | Section "Small sizes": the table with its bounds, the list of partitions, the solver runs and the controls | pycryptosat for `climb`, `controls` | see below |
| `class_uniform_sat.py` | One solver run: is there a class-uniform rule over GF(2) with a code of dimension ≥ D? | pycryptosat | see below |
| `verify_class_uniform_code.py` | Checks a saved code in `data/` against the definition; shares no code with the search | — | seconds |
| `analyse_code.py` | The properties of the code of dimension 25 quoted after Proposition (two classes with no almost-period beat every interval rule) | — | seconds |

## Generated files

```sh
python3 tools/lean_index.py                     # regenerate the index and PaperAxioms.lean
python3 tools/lean_index.py --check             # fail if a cited name is missing or a generated file is stale
python3 tools/gen_aperiodic_example.py          # regenerate AperiodicExampleData.lean
python3 tools/gen_aperiodic_example.py --check  # fail if it is stale
```

## Checks of the two theorems on small instances

```sh
python3 tools/exhaustive_flag_checks.py
python3 tools/three_term_example.py
python3 tools/exhaustive_pigeonhole_checks.py
python3 tools/digit_and_composition_checks.py
python3 tools/entry_form_check.py
python3 tools/two_class_family.py
python3 tools/set_bounds_check.py
python3 tools/order_bounds_check.py
```

Each ends with a summary line and stops, or exits with a nonzero status, if a statement of the paper fails on an
instance. The two `exhaustive_*` scripts accept section names as arguments (listed at their tops); for example
`python3 tools/exhaustive_pigeonhole_checks.py n3 n4` produces the rows d ≤ 4 of the table of small sizes.

## The section on small sizes

```sh
python3 tools/small_sizes.py table                  # the paper's table; re-verifies every saved code
python3 tools/small_sizes.py partitions 6           # the partitions of Z_6 up to affine maps, with the bounds
python3 tools/small_sizes.py shifts 6 "0,1,3|2,4,5" # components per shift: no almost-period
python3 tools/verify_class_uniform_code.py tools/data/*.json
python3 tools/analyse_code.py                       # the code of dimension 25 and its translates
python3 tools/small_sizes.py controls               # the solver answers quoted in the paper (about three minutes)
python3 tools/small_sizes.py controls --long        # also the codes of dimension 25 and 28 at d = 6 (about three more minutes)
```

`data/` holds one saved code for every row of the table with d ≥ 5 (22 files): the rule and a basis of its code over
GF(2), in the format described at the top of `verify_class_uniform_code.py`. It also holds the three codes of the
two-class rule over GF(2) at d = 8, 12 and 16 (`two_class_d*.json`), which `two_class_family.py --write-data` writes
from the closed form and which no search produced. `aperiodic_d6_dim25.json` is the
certificate of the Lean-verified proposition.

### How the saved codes were found

Every code of the table was found by `class_uniform_sat.py`, driven by the `climb` subcommand of `small_sizes.py`: for one
partition, raise the target dimension D while the solver answers "satisfiable" within a time cap, and stop at the
first "unsatisfiable", at the first time-out, or at the bound of Theorem TP. All runs used `--rref`, one thread unless
stated, and no random seed other than the solver's default. Three points matter when reading the record below.

- **"Satisfiable"** is checked without the solver: the script rebuilds the matrix of τ − K from the rule, recomputes
  its kernel, and `verify_class_uniform_code.py` checks the saved code from the definition.
- **"Unsatisfiable"** rests on the solver. The paper quotes two such answers and says so.
- **A time-out means nothing.** The solver also times out on instances that are known to be satisfiable (first line
  of the table below). CryptoMiniSat's time limit counts CPU seconds summed over its threads, so `--threads 4
  --time 3600` stops after about fifteen minutes.

`--hankel` restricts the search to codes that contain the space H* of matrices with x_c′ = σ^(c′−c) x_c for all
c, c′ in one class. That is a subfamily: the restriction makes the search faster and can only lower the result. With
`--hankel` and `--rref` the target must be at least M·n = dim H*, and the script refuses smaller targets.

To repeat a climb (the codes are written to a new directory `small_sizes_out`, not to `data/`):

```sh
python3 tools/small_sizes.py climb 900 5 "0|1,2,3,4" 5 "0,1|2,3,4" 5 "0|1|2,3,4" 5 "0|1,2|3,4" 5 "0|1,4|2,3" 5 "0|1|2|3,4" --hankel
python3 tools/small_sizes.py climb 600 6 "0|1,2,3,4,5" 6 "0,1|2,3,4,5" 6 "0,1,2|3,4,5" 6 "0,2,4|1,3,5" 6 "0,2|1,3,4,5" 6 "0,3|1,2,4,5" --hankel
python3 tools/small_sizes.py climb 600 6 "0,1,3|2,4,5"
python3 tools/small_sizes.py climb 300 6 "0,1|2,4|3,5" 6 "0,1|2,5|3,4" 6 "0,2|1,4|3,5" 6 "0|1,5|2,3,4" 6 "0|1,2,4|3,5" 6 "0|1,2,5|3,4" 6 "0|1,3,4|2,5" 6 "0|4|1,2,3,5" 6 "0|3|1,2,4,5" --hankel
```

### Record of the solver runs

Outcomes of the runs behind the table, with the time of the decisive run. Times are from single runs on one laptop
and vary between runs and machines. "TP" is the best bound of Theorem TP over shift sets of at most four elements.

| d | classes | largest code found | next target | TP | notes |
|---|---|---|---|---|---|
| 5 | `0\|1,2,3,4` | 17 (`--hankel`, 2 s; also without, 15 s) | — | 17 | bound reached |
| 5 | `0,1\|2,3,4` | 17 (`--hankel`, 2 s; also without, 2 s) | — | 17 | bound reached |
| 5 | `0\|1,2\|3,4` | 20 (`--hankel`, < 1 s) | — | 20 | bound reached |
| 5 | `0\|1\|2,3,4` | 19 (`--hankel`, < 1 s) | 20: unsatisfiable with `--hankel` (37 s); time-out without (900 s, and again with four threads) | 20 | a code of dimension 20 would contain H* (Lemma on extremal codes), so 19 is the maximum on the word of the solver |
| 5 | `0\|1,4\|2,3` | 20 (`--hankel`, < 1 s) | 21: unsatisfiable without `--hankel` (113 s; 104 s when repeated) and with it (15 s) | 21 | maximum 20 on the word of the solver |
| 5 | `0\|1\|2\|3,4` | 22 (< 1 s, with and without `--hankel`) | — | 22 | bound reached |
| 6 | `0\|1,2,3,4,5` | 24 (`--hankel`, 17 s) | — | 24 | bound reached |
| 6 | `0,1\|2,3,4,5` | 24 (`--hankel`, 51 s) | — | 24 | bound reached |
| 6 | `0,1,2\|3,4,5` | 24 (`--hankel`, about 100 s) | — | 24 | bound reached; without `--hankel` the same target timed out at 600 s, although the block-symmetric matrices are a code of this dimension |
| 6 | `0,2,4\|1,3,5` | 24 (`--hankel`, 11 s) | — | 24 | bound reached |
| 6 | `0,2\|1,3,4,5` | 24 (`--hankel`) | 25: time-out (600 s, `--hankel`) | 27 | lower bound only |
| 6 | `0,3\|1,2,4,5` | 23 (`--hankel`) | 24: time-out (600 s, `--hankel`) | 27 | lower bound only |
| 6 | `0,1,3\|2,4,5` | 25 (no `--hankel`, about 190 s; with `--hankel`, 112 s) | 26: time-out without `--hankel` (1800 s) and with it (600 s; 900 s of CPU time on four threads); 27: time-out with `--hankel` (600 s) | 28 | lower bound only; the saved code is from the run without `--hankel` |
| 6 | `0,1\|2,4\|3,5` | 28 (`--hankel`) | 29: time-out (300 s) | 30 | lower bound only |
| 6 | `0,1\|2,5\|3,4` | 28 (`--hankel`) | 29: time-out (300 s) | 30 | lower bound only |
| 6 | `0,2\|1,4\|3,5` | 28 (`--hankel`) | 29: time-out (300 s) | 30 | lower bound only |
| 6 | `0\|1,2,4\|3,5` | 28 (`--hankel`) | 29: time-out (300 s) | 30 | lower bound only |
| 6 | `0\|1,5\|2,3,4` | 27 (`--hankel`) | 28: time-out (300 s) | 30 | lower bound only |
| 6 | `0\|1,2,5\|3,4` | 27 (`--hankel`) | 28: time-out (300 s) | 30 | lower bound only |
| 6 | `0\|1,3,4\|2,5` | 27 (`--hankel`) | 28: time-out (300 s) | 30 | lower bound only |
| 6 | `0\|4\|1,2,3,5` | 27 (`--hankel`) | 28: time-out (300 s) | 30 | lower bound only |
| 6 | `0\|3\|1,2,4,5` | 26 (`--hankel`) | 27: time-out (300 s) | 30 | lower bound only |

Runs that the paper does not report: at d = 7 the same method is out of reach. For the intervals `0,1,2|3,4,5,6`
it found a code of dimension 29 and timed out at 30 (900 s, `--hankel`), where the bound of Theorem TP is 31; for
`0,1,2,4|3,5,6` it timed out at 29, one above the pairing value 28. Neither says anything about the true values.

## Searches for acyclic sets (end of the section on sets)

```sh
python3 tools/acyclic_set_search.py large 60 13 12 17 12 17 24
python3 tools/acyclic_set_search.py large 120 23 12 29 12
python3 tools/acyclic_set_search.py pairing 60 9 2 9 3 9 5 11 2 11 3 11 5 13 2 13 3 13 5 17 3 17 5
python3 tools/acyclic_set_search.py calibrate 120 17 12 23 12 29 12
python3 tools/acyclic_set_search.py lower 200 13 12
```

`large` reports the size of the largest acyclic set that the solver finds within the time limit (seconds, first
argument) for each pair (d, window). The sizes are results of a search: they are lower bounds on the largest
acyclic set, and say nothing certain about its true size. A rerun can give slightly different numbers, because the
solver runs four workers under a time limit. The output that the paper quotes:

| d | window | zero offsets (control) | permutations and offsets | affine | random | unstructured digraph | d(d−1)/2 |
|---|---|---|---|---|---|---|---|
| 13 | 12 | 99 | 69 | 64 | 70 | 72 | 78 |
| 17 | 12 | 176 | 118 | 111 | 118 | 121 | 136 |
| 23 | 12 | 327 | 211 | 202 | 223 | 219 | 253 |
| 29 | 12 | 515 | 339 | 323 | 353 | 349 | 406 |
| 17 | 24 | 160 | 92 | 74 | 73 | 77 | 136 |

In the control family an acyclic set of d(d−1)/2 positions exists by the order of the columns (Proposition (two
bounds for sets), part (a)), and the search exceeds that size. On a second control (`calibrate`), the pairing with eleven zero-offset permutations, where the
largest acyclic set has exactly d(d−1)/2 positions, the same search returned 136, 253 and 406 at d = 17, 23, 29.

`lower` gives proved lower bounds on the least number of positions that meets every cycle, for the three spread
families at the first pair of the first `large` run. With 200 seconds for each it printed 99 for permutations and
offsets at d = 13, window 12 (above d(d+1)/2 = 91; the largest acyclic set there has 69 or 70 positions), and
88 and 84 for the affine and the random family, which are below 91 and decide nothing. These are the solver's bounds
after 200 seconds; a slower machine may print smaller numbers, which are still valid lower bounds.

`pairing` reports a lower and an upper bound on the least number of positions that meets every cycle. In the eleven
runs listed above the two bounds were equal, and equal to d(d+1)/2 (45, 66, 91, 153 for d = 9, 11, 13, 17), within
60 seconds each.


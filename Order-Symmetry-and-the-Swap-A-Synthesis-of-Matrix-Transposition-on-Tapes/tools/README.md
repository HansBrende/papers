# Tools

Every script that was used for the paper: the generators of generated files, the exact computations behind the
numerical remarks and the section on small sizes, and small-instance checks of statements that are proved in the text
but not formalized. Run them from the paper's directory (the parent of `paper/`, `lean/` and `tools/`). Each script
documents its usage at its top. Apart from the two generators, no script is used in a proof, and the Lean library
does not depend on any of them.

The side length is `d` in the paper and `n` in most scripts. A partition of Z_n is written `"0,1,3|2,4,5"`.

**Requirements.** Python 3. `exhaustive_flag_checks.py` and `exhaustive_pigeonhole_checks.py` need NumPy;
`class_uniform_sat.py`, and the subcommands `climb` and `controls` of `small_sizes.py`, need the package
`pycryptosat` (CryptoMiniSat). Everything else uses the standard library only. The results in the paper were obtained
with Python 3.12.10, NumPy 2.5.4 and pycryptosat 5.18.0.

| Script | What it reproduces | Needs | Time |
|---|---|---|---|
| `lean_index.py` | `paper/sections/leanindex.tex` and `lean/PaperAxioms.lean` | — | seconds |
| `gen_aperiodic_example.py` | `lean/SwapRigidity/AperiodicExampleData.lean`, from `data/aperiodic_d6_dim25.json` | — | seconds |
| `exhaustive_flag_checks.py` | Section "Order": Theorem FL and its corollaries on small instances; the numbers of Remark (numerical: the bound is not always tight) | NumPy | about 90 s |
| `three_term_example.py` | Remark (two is sharp): τ − Π and the three-term example at d = 4 | — | seconds |
| `exhaustive_pigeonhole_checks.py` | Section "Symmetry": the pigeonhole lemma, Theorem TP, the line form and twist classes on small instances; the numbers of Remark (numerical: what the exact value does not say) and Remark (numerical: on a line, other shifts fail); the rows d ≤ 4 of the table of small sizes | NumPy | about 45 s |
| `digit_and_composition_checks.py` | Corollary (every address digit must be broken) and Remark (composition), including the unshuffle | — | seconds |
| `entry_form_check.py` | Proposition (changes that affect single entries): every rule at d = 2 over GF(2), random rules and rules with free entries up to d = 5, and the rules of the saved codes; with controls that group the changes differently and must fail | — | seconds |
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
GF(2), in the format described at the top of `verify_class_uniform_code.py`. `aperiodic_d6_dim25.json` is the
certificate of the Lean-verified proposition.

### How the saved codes were found

Every code was found by `class_uniform_sat.py`, driven by the `climb` subcommand of `small_sizes.py`: for one
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

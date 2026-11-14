# Simplex-code certificates

These tools support the [calibration note](../../notes/simplex-code-calibration.md).
They verify finite constructions and the scalar Fano optimum over
$\mathbb F_2$ and $\mathbb F_3$. They do not determine nonlinear capacity,
prove the random asymptotic theorem, or perform Lean verification.

The separate [Fano Shannon certificate](../fano-shannon/README.md) now gives
the matching unrestricted upper bound 119/3 for the three-lane construction,
strictly below order 41. Its small independent checker is separate from
the scalar rank certificates in this directory.

Run the following commands from this directory with ordinary Python 3;
do not disable assertions with `-O`.

```sh
python3 combinatorial_controls.py
python3 plane_controls.py --verify fano-packing.json
python3 gf2_cnf.py replay fano-packing.json fano-r9.cnf fano-r9.lrat.zip
```

These checks use only the standard library. The first independently checks
the Fano eight-triangle/two-pair code, the 39-triangle partition for
$\operatorname{PG}(2,3)$, the projector obstruction, and the Fano
119-dimensional binary code with three-bit entries. Its expanded witness
is `packing-receipt.json`. The second reconstructs the Fano incidence and
checks the fitting matrix and eight-cell acyclic witness.

The final command reconstructs the complete rank-nine Boolean formula,
compares it exactly with `fano-r9.cnf`, checks a rank-ten control assignment,
and replays the stored LRAT contradiction. The checker accepts only
positive-hint reverse-unit-propagation steps; it does not trust a solver's
reported answer. The written lossless factorization argument is in Section 5
of the note. The binary proof checks 13,964 additions and derives the empty
clause.

## Regenerating the solver proofs

The recorded solver is CaDiCaL 2.1.2. With `cadical` on `PATH`:

```sh
mkdir -p generated
python3 gf2_cnf.py build --rank 9 --control fano-packing.json --output generated/fano-r9.cnf
cadical --plain --lrat --no-binary -t 60 generated/fano-r9.cnf generated/fano-r9.lrat
python3 gf2_cnf.py replay fano-packing.json generated/fano-r9.cnf generated/fano-r9.lrat
```

CaDiCaL exits with code 20 for UNSAT. A timeout or a missing completed
certificate proves nothing. The exact binary CNF SHA-256 is
`83e548f5d5cc433d2bfc4b7f02999e1387e599e18b234abd3da17e97644a64e8`.

For scalar ternary codes on the **same Fano incidence relation**:

```sh
python3 gf3_cnf.py --rank 9 --control fano-packing.json --output generated/fano-r9-gf3.cnf
cadical --plain --lrat --no-binary -t 60 generated/fano-r9-gf3.cnf generated/fano-r9-gf3.lrat
python3 gf2_cnf.py check generated/fano-r9-gf3.cnf generated/fano-r9-gf3.lrat
```

The ternary generator checks all scalar arithmetic cases and a complete
rank-ten control assignment before producing the decision formula. It has
48,278 variables and 143,610 clauses. Its completed proof replay checked
567,518 additions and 561,099 deletions and derived the empty clause.
The generated text trace is about 559 MiB and is not stored here. The
streaming checker handles it without loading the whole proof at once.

The ternary CNF SHA-256 is
`fdae45df0686f9504dbf4ae6a0c4e5f81b9e5f0036fbb3d78354a32c938c146b`;
the recorded uncompressed LRAT SHA-256 is
`4fe0a6eb3ae420ea76962ec80e95b9bfd4cef5d3e2633d00ffea37bbd2e6ae4f`.

Both field results certify scalar-linear dimension 39, with unrestricted
recovery coefficients. Neither rules out the three-bit vector code of
normalized dimension $119/3$, or nonlinear codes.

`plane_controls.py` also contains an optional packing search using SciPy.
That search is unnecessary for every verification command above; the
reported mathematical bounds never rely on a floating-point solver bound.

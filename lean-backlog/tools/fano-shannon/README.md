# Fano Shannon certificate

The [proof note](../../notes/fano-shannon-certificate.md) proves full Shannon
value **119/3**, strictly below order value **41**, for the Fano whole-row
host. The existing three-lane code attains the bound over every finite
base alphabet. The upper proof applies to arbitrary sources and recovery
functions. Its paid 28-cell upper inequality and residual 56/3 corollary
are now **Lean-verified** in [FanoCertificate.lean](../../FanoCertificate.lean).
The full 49-cell adapter, exact residual and full Shannon attainment by
explicit polymatroids, and order value 41 are also Lean-verified in the
companion modules. Code realization over cube alphabets, the general
order/acyclic-set identification and the separate joint-column-error
coefficient 41/84 remain written proofs with exact checks. The
[consolidation index](../../notes/consolidation-status.md) gives the precise
scope and Lean build command.

All reproduction scripts below require **Python 3.10 or later**. Check that
the generated semantic Lean proof still matches the saved certificate with:

```sh
python3 lean-backlog/tools/fano-shannon/generate_lean.py --check
```

Omit `--check` to regenerate it. The generator is not part of the trusted
proof: Lean checks the graph incidences, automorphisms, semantic inequalities
and their exact integer combination. No LP solver is needed for this step.
Generic purchases, paid recovery and averaging are shared with the grid certificate
in [ShannonCertificate.lean](../../ShannonCertificate.lean); the Fano endpoints are unchanged.

Run from the repository root, without disabling assertions:

```sh
python3 lean-backlog/tools/fano-shannon/verify_certificate.py
```

This standard-library checker reads `certificate.json`, reconstructs all
33 semantic inequalities independently of the discovery code, and checks
their integer-weighted sum `264 h(W) <= 4928`. It also verifies the
matching triangle entropy and the exact order cost. No solver is needed.
The proof uses only 34 set orbits; the 2,668-variable search is unnecessary
for proof replay.

The [geometric dictionary](orbit-dictionary.md) describes all 34 orbits
as labelled row closures, intersections or a closed union, and displays
all 33 weighted inequalities using those orbit names. Regenerate and
check every expression with:

```sh
python3 lean-backlog/tools/fano-shannon/describe_certificate.py
```

The [paid-recovery note](../../notes/fano-soft-recovery.md) removes the
exact-recovery premise and charges conditional recovery errors. Its
fixed closure paths and the uniform charges 2/3, 1/3 and 41/84 are
checked, without any solver, by:

```sh
python3 lean-backlog/tools/fano-shannon/closure_charge.py
```

The [thirteen-row calibration](../../notes/projective-plane-order-calibration.md)
has exact order 140 and a known triangle-code lower bound 130; its
Shannon value is not determined here. Recompute the two integer subset
recurrences and the saved receipt with:

```sh
python3 lean-backlog/tools/fano-shannon/pg3_order.py
```

The Python receipts also cover statements outside the Lean scope listed
above; a successful Python run is not itself a Lean proof. The separate
[finite-gap amplification theorem](../../notes/finite-shannon-gap-amplification.md)
has a written probabilistic proof and needs no new search or numerical
certificate. It gives a growing fixed-window gap, not a new native
transposition lower bound.

For a full replay of the saved discovery relaxation, still without SciPy:

```sh
python3 lean-backlog/tools/fano-shannon/closure_relaxation.py \
  --verify lean-backlog/tools/fano-shannon/search-receipt.json
```

To regenerate the one LP, install SciPy and run:

```sh
python3 lean-backlog/tools/fano-shannon/closure_relaxation.py \
  --solve --output fano-reproduction.json
```

The recorded run used SciPy 1.18.1 and NumPy 2.5.4. It took about two
seconds; the solver is limited to 1,800 seconds. The script accepts a
candidate only after exact rational primal feasibility, dual signs and
the full coefficient identity are checked. A timeout or failed exact
reconstruction establishes no result. The inequalities and orbit
representatives have a deterministic digest in `search-receipt.json`.

The finite family is precisely specified in the proof note. It includes
two-fold row-closure intersections and the named triangle intersections,
then one round of auxiliary meets and closed joins. It is **not** the full
meet/join closure or the full Shannon LP. Its upper bound proves the full
value only because the explicit triangle construction matches it.

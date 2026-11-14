# Exact diagonal-code controls

These reproduce the finite claims in
[Diagonal codes and window-dependent excess](../../notes/diagonal-code-calibration.md).
They use exact binary arithmetic, not numerical ranks. The general folded-
cube formula is proved in the note; checking five instances does not replace
that proof. Paper 4 Corollary H4 supplies the Clebsch diagonal upper bound.

From the repository root, with Python 3.10 or later:

```sh
python3 lean-backlog/tools/diagonal-calibration/controls.py
python3 lean-backlog/tools/diagonal-calibration/pair_controls.py
```

The first command regenerates `receipt.json`. It checks complete binary
fitting matrices, helper support, diagonal independent sets, row-order DAG
witnesses and the exact row-order subset dynamic program. It also checks
folded-cube ranks at odd lengths 1 through 9. Expected whole-array bounds:

| Relation | Binary construction | All-alphabet upper bound |
|---|---:|---:|
| Basis, $d=4$ | 12 | 12 |
| Basis, $d=8$ | 46 | 46 |
| Basis, $d=16$ | 176 | 176 |
| Clebsch, $d=16$ | 210 | 211 |

For the basis relations the constructions also attain the bound over every
finite alphabet. For Clebsch, binary attainment is all that is asserted.

To enumerate all covariant binary couplings of two nonloop Clebsch sectors,
compile with a C++17 compiler:

```sh
pair_exe=$(mktemp)
c++ -O3 -std=c++17 lean-backlog/tools/diagonal-calibration/two_sector.cpp -o "$pair_exe"
"$pair_exe"
rm "$pair_exe"
```

Each of three symmetry types checks exactly 1,048,576 matrices. Expected
minimum ranks are 10, 8, 8, with no gain over independent sectors. The
Python pair control independently checks the coordinate interpretation,
support and baseline ranks. Review also cross-checked 1,545 deterministic
matrices using a separate highest-pivot rank implementation.

This finite enumeration excludes only two-sector, covariant, scalar binary
improvements. It does not settle the remaining 210–211 gap, general
covariant decoders, larger coupled sector sets, or vector/nonlinear codes.

## Shannon certificates

The [conditional-recovery audit](../../notes/row-spread-of-cones.md#19-conditional-row-recovery-and-the-full-shannon-question)
spells out why the saved basis-host optima are also exact full Shannon
bounds. To check the integral dual identities and their attaining codes:

```sh
python3 lean-backlog/tools/diagonal-calibration/shannon_certificates.py
```

This standard-library-only command reads the existing `receipt.json`,
checks every helper inclusion, symbolically telescopes the Shannon dual,
and checks the disjoint loop/pair/K₄ constructions over any finite alphabet.
Expected basis values are 12, 46 and 176 at d=4, 8 and 16. It does not
rerun the subset dynamic program or solve an entropy LP.

The same command checks the separate **coarse** row/column-union control:
at d=3 and d=4 it has values 7 and 12, whereas the corresponding window-one
full-host bounds are 6 and 10. Only 50 and 226 retained subsets, respectively,
are checked. This is an incomplete-relaxation example, not a non-Shannon gap
on the full cell polymatroid cone. The written proof covers every d and
realizes the coarse data linearly over finite fields of size at least d;
these finite certificate checks are not Lean formalizations.

## Cyclic four-row host

The single additional test in
[row spread §20.5](../../notes/row-spread-of-cones.md#20-cell-budgets-token-closures-and-the-shannonorder-test)
uses d=4 and ρ(r)={r,r+1 mod 4}. Its capacity, full Shannon bound and
acyclic/order bound are all **13**. Eight loop cells are free; the other
eight form four pairs whose sums equal one free shared symbol. This works
over every finite alphabet and gives a token matroid beyond disjoint
clique-parity codes. It does not give a fixed-window asymptotic gain.

Replay the saved rational primal/dual certificate without an optimizer:

```sh
python3 lean-backlog/tools/diagonal-calibration/verify_cyclic4_certificate.py
```

The standard-library verifier checks all 256 residual subset entropies,
2,824 Shannon inequalities, normalization and recovery equalities, and
the exact 43-term dual identity with value five. It also checks the
explicit binary rank function and the mate/complete-pair recovery rule
that works over any ℤ/qℤ. Adding the eight loops gives 13. The order
argument in the note is a shorter independent proof of the upper bound.

To regenerate the receipt, with SciPy installed:

```sh
python3 lean-backlog/tools/diagonal-calibration/cyclic4_shannon.py
```

SciPy proposes a solution; exact rational verification must pass before
the generator writes `cyclic4-shannon-receipt.json`. The saved receipt was
generated with SciPy 1.13.1; another solver version may choose a different
optimal certificate. The tools test only this host. These are written
proofs and exact finite checks, not Lean verification.

## Fundamental token blocks

The written proofs in [row spread §21](../../notes/row-spread-of-cones.md#21-token-blocks-accounting-and-bounds-for-fundamental-presentations)
give a two-thirds bound for fundamental transversal designs on codegree-one
hosts, and a half-plus-near-cell bound on the same class. They also cover
paid token deletion and row/column groups with arbitrary scalar masses.

```sh
python3 lean-backlog/tools/diagonal-calibration/token_blocks.py
```

This standard-library command checks the canonical blocks, exact slack
identity, rational edge payments and far-token accounting on five explicit
controls: window-one pairing (rank 10 of 16), a triangle with free loops
(8 of 9, attaining the two-thirds bound including its loop term), the
cyclic-four control after revealing z (12 of 16), grouped twin coordinates
(12 of 16), and a one-symbol example with nonzero edge payment 3/4.
It performs no host search, writes no files and uses no optimizer. These
checks supplement the general written proofs; they are not Lean proofs or
evidence for the unrestricted token conjecture.

## Two-token presentations

The reviewed written proof in [row spread §22](../../notes/row-spread-of-cones.md#22-alignment-bicircular-presentations-and-a-uniform-constant-deficit)
gives 6K≤5N+6L+N₃ for every whole-row matching-matroid presentation with
at most two tokens per scalar coordinate. Deleting tokens touched by
high-reverse rows gives rate at most 5/6+O_w(d^(−1/2)) at any fixed
forward window, uniformly in lanes. No alignment, codegree or symmetry
assumption is used. The two-token matching-matroid premise remains.
The same Hall-matching proof extends to maximum support size a and total
incidence I: 6K≤2I+N+(2a+2)L+(a−1)N₃. For fixed a,w and I/N≤μ<5/2,
it gives asymptotic rate at most (1+2μ)/6. The matching-matroid recovery
condition remains essential; sparsity of an arbitrary coefficient matrix
does not imply it.

```sh
python3 lean-backlog/tools/diagonal-calibration/bicircular_controls.py
```

This standard-library-only command reuses the matching and distance tools
from `token_blocks.py`. It checks graph rank against maximum matching on
all subsets of the small active examples, including the 256 subsets of
the cyclic-four doubled-star component. Six recovery controls check the
loop/near charge and the high-reverse trimming step (rank 7 becomes 3
after four tokens are deleted). Two further weak-alignment controls
verify the same-row gap in the earlier proof, including one whose
nonconstant coordinates are all nonloops. They refute the edge inference,
not its claimed numerical capacity bound. Two support-three controls check
the general Hall charge, including a far coordinate with three degree-two
tokens; graph-rank formulas are not used on those presentations.
No optimizer or design search
is run, and no files are written. These are finite checks, not Lean proofs.

## Block-core controls

[Row spread §23](../../notes/row-spread-of-cones.md#23-block-cores-and-a-paid-reduction-to-minimum-occurrence-three)
proves a paid reduction to a masked core of minimum token occurrence three.
After removing tokens touched by exceptional coordinates, degree-two tokens
peel with exact rank cost half the removed coordinate count. Its direct
consequence improves the two-token asymptotic rate cap to 2/3 at fixed
forward window. All statements here are written proofs, not Lean proofs.

```sh
python3 lean-backlog/tools/diagonal-calibration/core_controls.py
```

The standard-library checker reuses the existing matching and distance
functions. Five fixed controls verify raw core-deletion failures (including
a far target with no active host loops), the paid repair, two successive
clean peeling rounds with ranks 3→2→1, and ordinary pairs peeling to rank
zero. The four-pair residual separately refutes the uncharged global rank
inequality: rank five exceeds half its eight noncore coordinates. Exact
defect identities and recovery are checked with maximum matching throughout.
Constants and removed-coordinate masks are counted explicitly. No optimizer,
host search or output-file write is used.

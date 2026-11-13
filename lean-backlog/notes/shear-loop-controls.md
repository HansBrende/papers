# Loop-adjusted controls for sheared helper relations

Hans Brende and GPT-6 Astra, 13 November 2026.

**Status:** written arguments and seven independently checked finite
certificates; not Lean-verified. This records the first experiment proposed
in [C4](../../chat/fable-astra.md) and the [pass-calculus note](pass-calculus.md).
Its only gain over the pairing bound is explained by self-loops. No
asymptotic improvement or novelty claim is made.

## The elementary baseline

Let a directed helper graph on the $d^2$ positions $(c,r)$ contain every
transpose edge $(c,r)\to(r,c)$. Each position has its own recovery function;
using a self-loop as a helper is permitted. Let $B$ count the unordered
off-diagonal transposed pairs whose two positions both have self-loops.
Write $\tau(G)$ for the minimum size of a set meeting every directed cycle.
Then

$$
\tau(G)\ge d(d+1)/2+B,
$$

and, for every finite alphabet of size $q$, there is a storage code of size
$q^{d(d+1)/2+B}$ on this relation.

**Proof.** Take the $d$ diagonal loops, one transpose 2-cycle from each
off-diagonal pair without two loops, and the two singleton loops from every
pair with two loops. These are vertex-disjoint cycles, numbering

$$
d+\bigl(d(d-1)/2-B\bigr)+2B=d(d+1)/2+B.
$$

A cycle-hitting set must meet each one. For the code, choose a free symbol
on each diagonal position, a common free symbol on each ordinary pair, and
two independent symbols on each double-loop pair. Recover each coordinate
by copying its transpose or its own loop, respectively. Over every field
this is a linear code of the same dimension, using coefficients only 0 and 1.
The chosen helper can depend on position; this does not impose a single
shared recovery function independent of $c$. ∎

If an induced acyclic set has $d^2-d(d+1)/2-B$ vertices, both bounds are
exact. Given the coordinates outside that set, recover its coordinates in
reverse topological order. This injects every storage code into the
assignments on the complement, giving the matching upper bound.

For a one-class relation of window $w$ with the exact transpose as one helper,

$$
B\le\left\lfloor\frac{(w-1)d}{2}\right\rfloor.
$$

Indeed, a further helper $(c,r)\mapsto(i(r),c+j(r))$ has at most one
self-loop for each $r$: a loop requires $c=i(r)$ and $i(r)+j(r)=r$ modulo
$d$. The other $w-1$ helpers therefore supply at most $(w-1)d$
off-diagonal loop positions, and each counted pair uses two. This mechanism
adds only $O(d)$ symbols at fixed window.

## The matched experiment

The planned dimensions were $d=7,11,13$, with windows $w=3,4,5$ and a
ten-second solver budget per instance. Every instance includes the unshifted
transpose. The two affine families use helpers

$$
(c,r)\mapsto(ar+u,c+br+v)\pmod d,
$$

with the following $(a,b)$ lists, truncated to the requested window:

- P: $(1,0),(-1,2),(-1,-2),(-1,4),(-1,-4)$.
- N: $(1,0),(-1,2),(-1,-1),(-1,1),(-1,3)$.

The translations agree by list position. In particular the same translated
$ST^2$ occurs in both, and at window three only $ST^{-2}$ is replaced by
$ST^{-1}$. A control uses the transpose plus random permutation row maps
and random offset functions. The saved seed is 20261113, with generator
seed $20261113+1000d$; the script records every map explicitly.

P has the integral character used in the pass-calculus argument; N contains
the affine order-three map. This distinction does not assert a bipartition
of the finite helper graphs or predict an exact finite capacity. The parity
argument is an asymptotic statement about complex linear codes with bounded
coefficients.

The first strict difference from the predicted value $d(d+1)/2$ triggered
the agreed stopping condition:

| Dimension | Window | Family | $B$ | Acyclic set size | Exact $\tau(G)$ and capacity exponent |
|---:|---:|---|---:|---:|---:|
| 7 | 3 | P | 0 | 21 | 28 |
| 7 | 3 | N | 0 | 21 | 28 |
| 7 | 3 | control | 0 | 21 | 28 |
| 7 | 4 | P | 0 | 21 | 28 |
| 7 | 4 | N | 0 | 21 | 28 |
| 7 | 4 | control | 1 | 20 | 29 |

A zero-offset calibration at $d=7,w=5$ also has exact value 28.
The remaining cases were not run. The values are certified by explicit
acyclic sets and disjoint cycle packings, independently of the solver's
optimality report. The elementary codes above attain every exponent.

In the exceptional control, helper 4 has

```
i = [5, 4, 6, 1, 3, 0, 2]
j = [5, 1, 3, 1, 3, 0, 4]
```

Both $(2,6)$ and $(6,2)$ are self-loops. Replacing their transpose 2-cycle
by these two loops gives 29 disjoint cycles. The saved 20-vertex DAG gives
the opposite inequality, so $\tau(G)=29$ and the maximum code size is
exactly $q^{29}$. This is a different instance from Paper 17's reported
random controls at dimensions 9 through 17.

## Reproduction and consequence

The [script](../tools/shear_acyclic.py) cross-checks its helper graph against
[Paper 17's implementation](../../Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/tools/acyclic_set_search.py).
The repository sources were checked at `e5150eb`; the receipt also records
the source file's SHA-256. Search used OR-Tools 9.15.6755 with one worker.
Replay uses only the Python standard library:

```sh
python3 lean-backlog/tools/shear_acyclic.py verify lean-backlog/certificates/shear-loop-controls.json
```

To repeat the bounded search with OR-Tools installed:

```sh
python3 lean-backlog/tools/shear_acyclic.py search --repo . --output shear-search.json
```

Solver timing and chosen witnesses may vary; the saved certificates are the
fixed record. Replay checks every edge in each supplied topological order
and constructs the disjoint cycles directly. No optimizer assertion is
needed for the seven exact results.

The experiment has not detected an advantage for the odd-relation family.
Before searching for a new coding mechanism, compare the order bound with
$d(d+1)/2+B$, not just $d(d+1)/2$. A strict gap beyond that baseline would
leave room unexplained by these elementary codes; it would still require
an actual code or another upper bound to decide capacity. The infinite
families and the main transposition question remain open.

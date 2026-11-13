# Row-spread controls and a global row-word obstruction

Hans Brende and GPT-6 Astra, 13 November 2026. Companion to
[Fable's row-spread argument and its audit](row-spread-of-cones.md).

The finite tests check conventions; they do not prove the infinite-family
row-spread theorem. The block-reversal obstruction below has a separate
written proof. No control here is a construction of a correct transposer.

## Reproduction and scope

From the repository root, with Python 3 and no additional packages:

```sh
python3 lean-backlog/tools/row_spread_controls.py --random-cases 1000
```

The fixed seed is `20261113`. Optional `--output receipt.json` saves the
complete receipt at a caller-chosen path. The default exhaustive horizon is
nine steps; increasing it grows the workload exponentially.

The run checks:

- 58,867 path/window cases, enumerating all unit moves and pauses through
  nine steps, with window widths up to six: labels, interval potentials and
  the sum of predecessor-window counts.
- 1,000 seeded multitape cone cases: exact last **visits**, state edges,
  revealed roots, cut enlargement, bad-window trapping, depth counted in
  edges, and the bound with **two** input rows per time window.
- Duplicate-archive/parked-input and bursty-output geometries. These are
  independent geometric controls inspired by Paper 18, not executions of a
  parsed transition table or replicas of all its published constructions.
- Negative controls that omit either the preceding state guard or an
  external work predecessor; both produce a witnessed escape from a bad
  window. Those guards are necessary for this trapping proof.
- Eight block-reversal skeletons ($s=2,3,5,8$, $b=1,2$), including every
  positioning tick and every direct-read incidence.
- 100 finite banded row words, with arbitrary domain gaps, both monotonicity
  signs, length zero through three, and band radii zero through two. Fixing
  offsets yields 3,292 checked monotone branches and exactly the same relation.

Any actual unit-speed trace realizing the source-cover/serial-return
geometries of Paper 9 is covered by the written interval argument, which
does not restrict its reuse or complete-cover complexity. No claim is made
that a Paper 9 native program
was re-executed by this script. Many historical dates or complete source
paths do not imply many distinct predecessor windows per time window on
average; these are different counts.

## Block reversal and global row words

Set $d=s^2$, $h=db$, $L=dh$, and

$$f(sa+t)=sa+s-1-t\qquad(0\le a,t<s).$$

For successive output rows $r$, position the raw input head at row $f(r)$
and copy its $h$ bits left to right. After copying, the head is one cell
past that row. Initial positioning costs $(s-1)h$. Within each block, move
left by $2h$ between rows. Between blocks move right by $2(s-1)h$. Thus

$$T=L+(s-1)h+2(d-s)h+2(s-1)^2h
  =(5s^2-5s+1)h<5L\quad(s>1).$$

This is a unit-speed, ordered-output skeleton. At the root of physical
output position $(r,c,\lambda)$ the input read is
$p=(f(r),c,\lambda)$; its transposition-demand coordinate is
$q=(c,r,\lambda)$. These $L$ pairs form a perfect matching between input
and output ports. Every root read belongs to its full cone under **every**
genie, because the zero-edge path is free even when its root is revealed.
Additional work or state dependencies can only add incidences.

Now use the exact row-word definition of [Paper 5, §6][rowwords]. A word of
length at most $\ell$ consists of monotone partial injections separated
and flanked by bands of radius $a$. Fix the integer displacement in each
band. Each band is then a partial translation, and the composition is a
monotone partial injection. Arbitrary gaps only restrict its domain.
Consequently $K$ such words are covered by at most

$$H=K(2a+1)^{\ell+1}$$

globally monotone partial graphs. The maps and domains may depend on $d$;
only $K,a,\ell$ are fixed.

In increasing output-row order, $f$ has $s$ successively increasing blocks,
each decreasing internally. An increasing graph agrees with $f$ at most
once per block; a decreasing graph agrees in at most one block. Each
therefore covers at most $s$ row pairs. The $H$ branches cover at most
$Hs$ output rows, leaving at least $(d-Hs)h$ direct-read incidences.

If a coordinate exception set $Z$ deletes both its ports, each coordinate
removes at most two edges of this matching. Thus any such row-word cover
outside $Z$ must satisfy

$$\#Z\ge\frac{(d-Hs)h}{2}=\frac{1-H/s}{2}L.$$

For fixed $K,a,\ell$, the required deletion is not $o(L)$. Allowing an
additional $o(d)$ exceptional raw or output rows does not help: they
remove only $o(L)$ coordinates.

This disproves the inference from bounded whole-row spread to a globally
bounded row-word cover. It does not contradict the row-spread theorem.
In particular, one helper row per output row in the direct-read
subrelation says nothing about the number of global monotone pieces.

### Native implementation status

The script certifies the literal time-indexed skeleton, not a fixed native
transition table. A uniform implementation has the following written
cost argument. On canonical valid lengths, count $L$ with a binary counter
during one raw scan; returning to the counter's low end after carries has
total $O(L)$ cost. Compute $d$, $b(d)$ and whether $d=s^2$ with
polynomial-in-$\log L$ arithmetic, and return the raw head to zero.
On other lengths choose any fixed terminating behavior.

Prepare a unary timer of length $h$ and a fixed number of counters of length
$s$, costing $O(h+s)$. Shuttling the timer counts each $h$-step copying or
positioning scan. Row/block counters cost $O(d)$ total movement, including
resets; repeated timer traversals count the block jumps. Fixed modes and
end markers distinguish copying from positioning. Control pauses preserve
the same direct root reads. All preparation and execution therefore cost
$O(L)$ with fixed finite control, alphabet and tape count.

This implementation argument is written, not Lean-verified or mechanically
compiled. Its purpose is to show that the control need not use uncharged
nonuniform schedules. It copies a row permutation on every input; it is
**not** correct matrix transposition on all inputs. It can refute a universal
schedule/cone inference, but not an extraction theorem whose hypotheses
include a near-full-rate transposition-correct source that this control lacks.

[rowwords]: ../../Directed-Recovery-Structures-in-Tape-Computations/paper/sections/row-words.tex

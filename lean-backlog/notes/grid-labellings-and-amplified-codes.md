# Grid labellings and amplified storage codes

Hans Brende and GPT-6 Astra, 13 November 2026. Fronts D1/D4/D7/D9.

This tests Fable's grid proposal in [the row-spread note, §8][grid] against
Paper 15. All results below are **written proofs, not Lean-verified**.
They reuse Paper 5's Lean-verified separated-components lemma. No new
native-machine exclusion or above-half whole-row construction is claimed.

The conclusions have different scopes:

- At canonical entry width, the displayed decoder in Paper 15's all-length construction has window
  proportional to $d$ under either contiguous row or contiguous column
  placement. Arbitrary internal permutations do not help this layout.
- Every fixed-window grid code whose coordinate components have size
  $o(\log d)$ has rate at most $1/2+o(1)$. The bound is uniform in the
  entry width and alphabet.
- For Cartesian-product codes with blocks of that size, the obstruction
  applies to **every** recovery rule and balanced grid labelling. A slowly
  padded version of Paper 15 therefore fails all fixed windows, despite
  retaining its abstract high-rate and separation properties.
- For the growing majority tower, a column label that ignores a tensor
  factor cannot present the displayed support at canonical width. For the
  full field-linear kernel, a separate shortened-code bound excludes the
  natural tensor-cylinder columns for every decoder, even nonlinear ones.

The original growing majority blocks and the original maximal-square-root
padding are not excluded under arbitrary grid labellings.

## 1. Definitions and the paid normalization

Let $V$ have $L=d^2b$ coordinates, $d,b\ge1$, and let a storage code
$C\subseteq A^V$ use an alphabet of size $q\ge2$. Its helper sets are
$N(p)\subseteq V$: agreement on $N(p)$ implies agreement at $p$.
No linearity is required. A balanced grid has row and column maps
$f,g:V\to[d]$ with $|\{p:f(p)=i,g(p)=j\}|=b$ for every $i,j$.
The row helper graph is bipartite, with edges $g(p)\to f(u)$ for
$u\in N(p)$. Its maximum column degree is the forward window $w$.

A forward-window grid gives a whole-row code over entry alphabet $A^b$.
It need not have bounded reverse row degree or bounded vertex indegree.
[Proposition 8.0][grid] supplies either cap by conditioning, keeping the
full balanced grid: reverse row threshold $R$ costs at most $wL/(R+1)$
coordinates; vertex indegree threshold $V_0$ costs at most $BL/(V_0+1)$
when vertex outdegree is at most $B$. Native exceptional columns cost
an additional amount of at most $\varepsilon L$ bits before these trims.
These costs are not implicit in the grid definition.

The next result does not need a vertex-degree cap. We use the reverse-row
trim in its proof, and then delete fixed coordinates only for the coding
calculation. Surviving row-column intersections still have size at most $b$.

## 2. A quantitative small-component bound

**Proposition.** Suppose every connected component of the undirected
coordinate graph of the helper relation has at most $s$ vertices, where
$s\ge1$ is an integer.
For every integer $R\ge0$, set

$$
 K=\max(2,w,R),\qquad Q_s(K)=\sum_{j=0}^{2s-1}K^j.
$$

Every nonempty storage code on this relation satisfies

$$
 \frac{\log_q|C|}{L}
 \le \frac12+\frac{w}{2(R+1)}+\frac{Q_s(K)}{2d}. \tag{1}
$$

*Proof.* The row helper graph has at most $wd$ edges. Freeze all coordinates
in rows of reverse degree greater than $R$. Their set $Z$ has size
$z\le wL/(R+1)$. On each fibre use the induced relation on $V\setminus Z$;
removed helper arguments are constants. The surviving row helper graph
has maximum undirected degree at most $K$.

The coordinate incidence graph has two ports per coordinate: its raw port
maps to row $f(p)$, its demand port to column $g(p)$, and recovery edges
join a helper's raw port to its target's demand port. Each component of
this incidence graph has at most $2s$ ports, since it lies above one
coordinate component. Let $U$ consist of the surviving coordinates whose two
ports are connected. A shortest connecting path has length at most
$2s-1$ and projects to a walk in the row helper graph. For each column,
at most $Q_s(K)$ rows are reachable within that radius. Each row-column
pair contains at most $b$ surviving coordinates. Thus

$$
 u:=|U|\le dbQ_s(K).
$$

Condition also on $U$. The remaining paired ports are in distinct
components: deleting vertices cannot reconnect them. [Paper 5,
Lemma 4.1 (Separated components)][P5] bounds each such conditional code by
$q^{\lfloor(L-z-u)/2\rfloor}$. There are at most $q^{z+u}$ assignments
to the frozen coordinates, so

$$
 \log_q|C|\le z+u+\left\lfloor\frac{L-z-u}{2}\right\rfloor
 \le\frac{L+z+u}{2}.
$$

Substitution gives (1). No separated-distance premise or coefficient
bound is used. ∎

**Corollary.** For fixed forward window $w$ and component size
$s=o(\log d)$, the upper limiting rate is at most $1/2$, uniformly in
$b\ge1$ and $q\ge2$, even when both vary with $d$.

*Proof.* Fix $R$ first. Then $K$ is constant and
$Q_s(K)=d^{o(1)}=o(d)$. Equation (1) gives upper limiting rate at most
$1/2+w/[2(R+1)]$. Let $R$ tend to infinity. ∎

In particular, a fixed positive excess above half at fixed $w$ requires
coordinate components at least on a logarithmic scale. This is a
quantitative extension of the bounded-component obstruction, derived from
the existing separated-components lemma; it is not a bound on general
expanding whole-row relations.

## 3. Product codes cannot escape by changing their decoders

**Proposition.** Suppose $V$ is partitioned into blocks $V_i$ of size at
most $s$, and $C=\prod_i C_i$ with each $C_i\subseteq A^{V_i}$ nonempty.
If $C$ has any recovery relation with a balanced grid of forward window
$w$, then (1) holds for that same code and labelling.

*Proof.* Replace the helpers of $p\in V_i$ by $N(p)\cap V_i$.
If two words in $C_i$ agree on these internal helpers, extend them by the
same fixed reference word in every other factor. The two full words lie
in $C$, agree on all original helpers of $p$, and therefore agree at $p$.
The internal helpers consequently recover $p$ throughout $C_i$, and hence
throughout $C$. This is a subrelation of the old relation, so the original
labels and all degree bounds persist. Every coordinate component now lies
in a single block. Apply the preceding proposition. ∎

Thus high-rate product codes with blocks $o(\log d)$ cannot have a
fixed-window whole-row presentation, even after arbitrary interleaving,
balanced grid relabelling, or replacement by nonlinear recovery rules.
The coordinate system is unchanged: this does not rule out a global
invertible recoding that mixes stored coordinates across blocks.

## 4. The actual syndrome support under contiguous placement

[Paper 15, Theorems 5.3 and 5.5][P15amp] use a check matrix $H=I-B$ of
size $n$ with diagonal one and rank $r\le e^{-\lambda m}n$, where $m$
is fixed and odd and $\lambda>0$. The displayed recovery relation is the
actual nonzero support of $B$, whose diagonal is zero. We do not assume
that every edge of the containing odd-coordinate-change graph survives:
majority coefficients can cancel in the field.

**Proposition.** Put $L=cn+a=d^2b$ with $0\le a<n$. Place $c$ copies of
this decoder consecutively in a linear order, with the $a$ isolated
leftover coordinates at the end. Divide that order into $d$ strips of
length $db$. Allow arbitrary permutations inside each copy. If the strips
are the raw rows, or instead the demand columns, then

$$
 w\ge\frac{\max(0,c-d+1)(n-r)}{db}. \tag{2}
$$

*Proof.* Rank subadditivity gives
$\operatorname{rank}B\ge n-r$. Thus $B$ has at least $n-r$ nonzero
rows (active targets), and at least $n-r$ nonzero columns (active helpers).
At most $d-1$ copy intervals cross strip boundaries: assign to each such
copy a boundary strictly inside it; disjoint copies cannot share one.

In the row-strip orientation, every active target $p$ in a contained copy
has a helper in the same raw row, giving an edge $g(p)\to f(p)$. At most
$b$ such targets give the same edge. In the column-strip orientation,
every active helper $u$ in a contained copy is used by a target in the
same column, giving an edge $g(u)\to f(u)$, again counted at most $b$
times. There are at least $\max(0,c-d+1)(n-r)$ active coordinates in
contained copies. Divide the resulting edge count by the $d$ columns. ∎

More exactly, if $t$ copies cross boundaries, the numerator in (2) can be
replaced by $(c-t)(n-r)$. A convenient weaker form, with $\theta=r/n$, is

$$
 \frac wd\ge(1-\theta)(1-a/L)-(d-1)n/L. \tag{3}
$$

[Paper 15, Theorem 6.1][P15all] chooses $n\le\sqrt L$. Therefore the last
loss is at most $1/\sqrt b$ and $a/L<1/(d\sqrt b)$. For canonical
$b(d)=\max(1,\lceil\log_2d\rceil)$, both contiguous orientations satisfy

$$
 w\ge\bigl(1-e^{-\lambda m}-o(1)\bigr)d.
$$

This excludes these layouts of the displayed decoder. It says nothing
about another recovery relation for the same code or arbitrary interleaving
of the growing blocks. The estimate alone gives no asymptotic exclusion
at $b=1$, since $n\le d$ then permits a linear fraction of crossing copies.

## 5. Slowly padded high-rate codes fail every fixed window

The all-length construction in Paper 15 repeats a tower block of size
$n_{j(L)}\le\sqrt L$ and reveals the leftover bits. The proof only needs
a cutoff tending to infinity and a sublinear leftover. Replace its cutoff
by any positive integer function $h(L)\to\infty$ with $h(L)=o(\log L)$,
for example

$$
 h(L)=\max\{1,\lfloor\log\log(L+e^e)\rfloor\},\qquad
 j(L)=\max\{j\le L:n_j\le h(L)\}.
$$

For all large $L$ this set is nonempty, and every fixed $j$ is eventually
eligible, so $j(L)\to\infty$. No growth-rate assumption on the tower is
needed. Repeat its encoder $c$ times and reveal $a$ leftover bits, where
$L=cn_{j(L)}+a$ and $0\le a<n_{j(L)}\le h(L)$. If the tower's fixed
rate deficit parameter is $\varepsilon$, the number of labels is at most

$$
 (2^{\varepsilon n_{j(L)}})^c2^a
 \le2^{\varepsilon L+h(L)}.
$$

All abstract degree, diverging paired-distance, and source-uniform common
partition conclusions of Theorem 6.1 remain valid. Every large $L$ has
a binary full-cube fibre of rate at least
$1-\varepsilon-h(L)/L$. Each attained full-cube fibre is a Cartesian
product of the block-syndrome fibres and singleton leftover-bit factors.

At canonical $L=d^2b(d)$, $\log L\sim2\log d$, so these blocks have size
$o(\log d)$. Choose a fixed degree cap with $\varepsilon<1/2$.
For each fixed window $w$, all sufficiently large canonical dimensions
therefore have high-rate fibres admitting **no** whole-row presentation
of that window, by §3, even with different recovery functions and
arbitrary balanced grid labellings. A fibre of a restricted source need not be a
product; the arbitrary-decoder conclusion here concerns full-cube fibres.

This is a useful calibration: abstract high rate, bounded degree,
separation, and all-length source-uniform partitions together do not
ensure whole-row compatibility. It is a deliberately slower assembly of
Paper 15's blocks. It does not exclude the original maximal-square-root
assembly or the unpadded majority tower.

## 6. The growing tower: support and intrinsic gates

Fix an odd $m=2a+1$ before the seed size $N$ grows. Over the fixed finite
field $F$ of odd characteristic, let $U\le F^V$, $|V|=N$, have dimension
$h\ge\rho N$ for fixed $\rho>1/2$. Paper 15 supplies a zero-diagonal
matrix $A$ with $A|_U=I$, supported on its seed graph. It does not specify
one numerical matrix family, nor require every graph edge to have a
nonzero coefficient. In particular, $\operatorname{rank}A\ge h$.

The majority operator and its full field-linear code are

$$B=2^{-m}\sum_{\sigma\in\{-1,1\}^m}
 \operatorname{Maj}(\sigma)\bigotimes_{i=1}^m(I+\sigma_iA),
 \qquad C=\ker(I-B).$$

Paper 15 proves $\dim C\ge(1-e^{-\lambda m})N^m$. The binary
syndrome fibres are intersections of affine translates of $C$ with the
binary cube; their guaranteed bit rate is
$1-(\log_2|F|)e^{-\lambda m}$. They need not retain the subspaces used
in the intrinsic argument below.

### Exact support

For $S\subseteq[m]$ put
$\gamma_S=2^{-m}\sum_\sigma\operatorname{Maj}(\sigma)
\prod_{i\in S}\sigma_i$. This depends only on $|S|$; call it
$\gamma_{|S|}$. For $u,v\in V^m$ set $S(u,v)=\{i:u_i\ne v_i\}$.
Then

$$B[u,v]=\gamma_{|S(u,v)|}
             \prod_{i\in S(u,v)}A[u_i,v_i]. \tag{4}$$

*Proof.* An equal coordinate contributes only the identity entry because
$A$ has zero diagonal; an unequal coordinate contributes only
$\sigma_i A[u_i,v_i]$. This gives (4). Sign reversal makes every
even $\gamma_k$ zero. At least one odd coefficient survives, since the
majority polynomial at the all-one input equals one. Different changed
coordinate sets therefore cannot cancel at a fixed matrix entry. Some
odd coefficients can vanish in the field; no argument below assumes
$\gamma_1\ne0$. ∎

### A displayed-support labelling must mix every factor

**Proposition.** Suppose $N^m=d^2b$ and a balanced grid of the displayed
support has forward window $w$. If its column map factors through a set
$J\subsetneq[m]$ of $j$ tensor coordinates, then

$$wb\ge h^{m-j}. \tag{5}$$

The row labelling is arbitrary; the column map may be any function of the
coordinates in $J$.

*Proof.* Choose a surviving $\gamma_{|S|}$. In each factor of $J$ fix a
valid pair $(u_i,v_i)$: a nonzero entry of $A$ when $i\in S$, and an
equal pair otherwise. This fixes one target column and one helper column.
For $i\notin J\cup S$, vary $v_i=u_i$ freely. For $i\in S\setminus J$,
vary $v_i$ over nonzero columns of $A$ and choose a matching $u_i$.
There are at least $h$ such columns, since $\operatorname{rank}A\ge h$.
Equation (4) therefore gives at least
$N^{m-j-|S\setminus J|}h^{|S\setminus J|}\ge h^{m-j}$ distinct
helpers in one helper column, used by the one target column. Its at
most $w$ helper rows meet that helper column in at most $wb$ coordinates.
This proves (5). ∎

At canonical width $b=O(\log d)=O(\log N)$, fixed $m$ and fixed $w$,
this is impossible as $N$ grows. It rules out column labels that omit
even one tensor factor, not arbitrary labels depending on every factor.
It applies to the displayed support for both field kernels and binary
fibres, but does not exclude alternative recovery rules for those codes.

### A decoder-independent gate for column partitions

For a linear code $C\le F^V$ and a column $P$, define its shortened code
$C[P]=\{x\in C:\operatorname{supp}x\subseteq P\}$.

**Proposition.** Every whole-row presentation of $C$ on a balanced
$d\times d$ grid with $b$ coordinates per cell satisfies

$$\dim C[P]\le wb\quad\hbox{for every column }P. \tag{6}$$

The recovery functions need not be linear.

*Proof.* Let $S$ be the helper rows for $P$. Projection of $C[P]$ onto
$S\cap P$ is injective: two words agreeing there agree outside $P$
(both vanish), hence on all of $S$, hence on the demanded column $P$.
The projection is linear and $|S\cap P|\le wb$. ∎

**Corollary (tensor cylinders).** For the full majority kernel above,
choose columns $P_z=\{v:v|_J=z\}$ with $|J|=k\le a$. Thus
$d=N^k$ and $b=N^{m-2k}$. Under every balanced row labelling, every
whole-row decoder for this code must satisfy

$$w\ge(h/N)^{a+1}d\ge\rho^{a+1}d. \tag{7}$$

*Proof.* Choose $a+1$ factors outside $J$ and put $U$ in those factors,
the one-dimensional span of $e_{z_i}$ in factors of $J$, and $F^V$ in
the remaining factors. The resulting tensor subspace has dimension
$h^{a+1}N^{m-k-a-1}$ and is supported in $P_z$. Every spanning pure
tensor has a strict majority of its factors in $U$, so Paper 15's
majority-fixed-tensor argument puts this subspace inside $C[P_z]$.
Substitute this dimension and $b=N^{m-2k}$ in (6). ∎

The same argument covers affine field translates by translating the
recovery rules. It does not cover arbitrary high-rate subcodes or binary
restrictions, which may lose these shortened subspaces. These natural
grids also have large lanes ($b\ge N$); they are not canonical-width
grids. Equations (5) and (7) exclude different classes, with these
different hypotheses.

### What a positive tower result would need

The lengths $N^m$ need not be squares. One precise sufficient target is
to append fixed-zero coordinates to reach $d^2$, where
$d=\lceil\sqrt{N^m}\rceil$, and present the padded full field kernel
on a scalar grid at a window $w(m)$ independent of $N$. Padding costs
$o(1)$ in rate. If this presentation exists, recovery on the linear
kernel is linearizable: a recovered coordinate factors linearly through
the helper projection and that functional extends to all helper values.
The resulting checks belong to the kernel's dual, so every affine
syndrome fibre of $H'=\operatorname{diag}(I-B,I_{d^2-N^m})$ has the
same helper relation, with syndrome-dependent
constants. Restrict the inputs to the binary cube and choose a largest
fibre. Its bit rate is at least
$1-(\log_2|F|)e^{-\lambda m}-o(1)$.
Taking $b(d)$ independent copies supplies the canonical bit-vector
entries at the same window and rate. Thus such presentations for
arbitrarily large fixed odd $m$ would refute a common positive whole-row
deficit. They would not by themselves give a tape algorithm.

The current negative results leave arbitrary fully mixed partitions
open. For a proposed field-kernel partition, (6) is an intrinsic early
test; passing it is not sufficient. For a proposed displayed-support
partition, (4) and the helper intersections give a separate test.
Neither proves that all partitions fail, nor rules out alternative
decoders for the binary fibres.

## 7. What remains worth testing

The open construction question is whether a growing amplified seed, or
an assembly with sufficiently large coupled blocks, admits a balanced
grid with one fixed forward window and rate at least $1/2+c$ for some
fixed $c>0$. A successful
family must specify the recovery functions, entry width and order of
quantifiers; a finite labelled block is not an asymptotic counterexample.
Even then, native tape realization is a separate obligation.

The coset index test and helper-sharing counterexamples are proved in
[§8 of the row-spread note][grid]. Their small exact incidence controls run
from the repository root with:

```sh
python3 lean-backlog/tools/grid_labelling_controls.py
```

These controls are not searches of the enormous concrete majority seed.
Equations (1)–(3) and the slow-padding consequence above are proved by
counting and the cited coding lemma, not numerical evidence.

[grid]: row-spread-of-cones.md#8-grid-labellings-and-their-scope
[P5]: ../../Directed-Recovery-Structures-in-Tape-Computations/paper/sections/directed-coding.tex
[P15amp]: ../../High-Rate-Separated-Storage-Codes-and-Tape-Transposition/paper/sections/amplification.tex
[P15all]: ../../High-Rate-Separated-Storage-Codes-and-Tape-Transposition/paper/sections/partitions.tex

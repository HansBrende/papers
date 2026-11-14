# Bounded sector coupling in group-based whole-row codes

Claude Fable 5.2 and GPT-6 Astra, 13 November 2026. Front D1.

Fable's odd-walk reduction gives a quantitative square-root bound. The
argument below strengthens it and proves the all-group theorem directly
from the previous mutual-diagonal theorem: no structure theorem for
finite groups is needed for that result. A separate near-abelian result
does use Neumann's theorem and covers every whole-row decoder on those
relations. All capacity arguments here have reviewed written proofs;
only the elementary group identities are Lean-verified. The native
transposition question remains open.

## 1. Setting and results

Let \(G\) be a finite group of order \(d\), with helper rows
\(\rho(c)=cT\), where \(\varnothing\ne T\subseteq G\) and
\(|T|\le w\). The sector of cell \((r,c)\) is \(g=r^{-1}c\).
Each of the \(d\) sectors has \(d\) cells. Fix a recovery support valid
on the entire code: each coordinate is determined by its specified
helpers, and every specified edge is mutually available in the original
whole-row relation. Symmetrize these edges to obtain the recovery
components. Assume each component meets at most \(m\ge1\) sectors.
Components may split sectors, and different components may meet the same
sector. Arbitrary nonlinear recovery and correlations are allowed. A
partition of whole sectors into blocks of size at most \(m\) is a special
case. An uncharged partition chosen separately for each codeword is not
covered.

**All-group bounded-coupling theorem (written proof).** For fixed \(w,m\),
uniformly over these groups, recovery supports and finite alphabets of size
\(q\ge2\), every such nonempty code satisfies

\[
 \log_q|C|\le \frac{d^2}{2}
       +O_{w,m}\!\left(\frac{d^2}{\log d}\right).
\]

Thus bounded coupling cannot give a positive limiting excess over half.
This strictly extends the own-sector recovery architecture. More
generally, let \(B_m\) be the number of cells in recovery components
meeting more than \(m\) sectors. The same proof gives

\[
 \log_q|C|\le\frac{d^2+B_m}{2}
       +O_{w,m}\!\left(\frac{d^2}{\log d}\right).
\]

A fixed rate gain \(\varepsilon>0\) therefore requires at least
\((2\varepsilon-o(1))d^2\) cells in such components, for every fixed
\(m\). This is a positive-density requirement on recovery support, not
a computation-time lower bound. One-way helpers and native machines are
not excluded by this theorem.

There is also an explicit bound. Write
\(r_2(z)=|\{h:h^2=z\}|\), \(R_2=\max_z r_2(z)\), and

\[
 X=T(T^{-1}T)^{m-1},\qquad
 E_X=\{g:gXg\cap X^{-1}\ne\varnothing\},\qquad s=|X|.
\]

**Finite bound (written proof, when every recovery component meets at most
\(m\) sectors).**

\[
 \log_q|C|\le\frac{d^2+d|E_X|}{2},\qquad
 |E_X|\le\min\!\left(d,\frac{s(s+1)}2R_2\right),\qquad
 s\le w^{2m-1}.
\]

In particular the excess is at most
\(\tfrac d2\min(d,w^{4m-2}R_2)\), improving the previous
\(w^{6m}R_2d\) bound. Odd-order groups have \(R_2=1\), hence additive
\(O_{w,m}(d)\) excess. The constants are not estimates of finite capacity.

## 2. Sector walks and the finite bound

A mutual move has the form

\[
 (r,rg)\longmapsto(rgt,ru^{-1}),\quad t,u\in T,
 \qquad g\longmapsto t^{-1}g^{-1}u^{-1}.
\]

Two steps multiply \(g\) on the left by a member of \(T^{-1}T\)
and on the right by a member of \(TT^{-1}\), independently. Thus a
sector has an odd closed walk of length \(2j+1\) exactly when

\[
 gxg=y\quad\text{for some }x\in T(T^{-1}T)^j,
 \ y\in T^{-1}(TT^{-1})^j=[T(T^{-1}T)^j]^{-1}.
\]

Indeed the last step after \(agb\) closes precisely when
\(g(ua)g=t^{-1}b^{-1}\). This is equivalent to
\((gx)^2=yx\). Multiplication by \(x\) is bijective, so each pair
\((x,y)\) allows at most \(R_2\) sectors.

For a sharper count write \(y=z^{-1}\), \(x,z\in X\). The equations
\(gxgz=1\) and \(gzgx=1\) are equivalent, so unordered pairs with
repetition suffice: there are \(s(s+1)/2\) of them.

In any nonbipartite graph on at most \(m\) vertices, a vertex reaches a
simple odd cycle of length \(a\) along a path of length at most \(m-a\).
The resulting odd closed walk has length at most \(2m-a\le2m-1\).
Loops count as cycles of length one. Backtracking pads the walk to
exactly \(2m-1\). A nonbipartite cell component projects to a connected nonbipartite
sector graph on at most \(m\) vertices. Every sector containing one of its cells
therefore belongs to \(E_X\).

Project a storage code onto its cell components. Each projection is a
storage code, since helpers stay inside the component; multiplying
projection cardinalities is an upper bound even with correlations.
A bipartite component contributes at most half its size to \(\log_q|C|\).
Allow all cells in the remaining sectors to be free. Their number is at
most \(d|E_X|\), proving the finite bound.

## 3. Direct proof for all finite groups

We retain **parallel** sector edges: different helper pairs can give the
same sector endpoints but different row movements. Label an oriented
edge from \(g\) by its **row multiplier** \(b=gt\); its lift sends
\(r\) to \(rb\). Its reverse has multiplier \(b^{-1}\). This label
is also called its voltage. Labels multiply in traversal order.

For a nonbipartite recovery component meeting at most \(m\) sectors,
temporarily complete its graph to the full available mutual relation on
those sectors. This contains the original odd cell walk and is an
equivariant cover; the original component need not be. Fix a root sector
\(g\) in its connected sector component and choose a spanning tree. For each vertex \(v\), let \(a_v\) be the row multiplier
of its tree path from \(g\), and \(\ell_v\) its length. An edge
\(v\to u\) with multiplier \(b\) gives a rooted closed walk with

\[
 \text{multiplier }a_vba_u^{-1},\qquad
 \text{parity }\ell_v+1+\ell_u\pmod2.
\]

These walks have length at most \(2m-1\). Their multiplier/parity pairs
generate exactly the subgroup \(\Lambda\le G\times\mathbb Z/2\)
obtained from all rooted closed sector walks: multiplying the displayed
labels along any closed walk cancels intermediate tree multipliers,
and the tree-path lengths occur twice in its parity sum.

If a lifted cell component is nonbipartite, an odd closed cell walk
returns to its starting row, so \((1,1)\in\Lambda\). Hence at least one
fundamental generator is odd. Choose one, with multiplier \(a\). Keep
every odd fundamental generator. Replace each even one with multiplier
\(b\) by the odd closed walk with multiplier \(ba\), and include the
reverses of all these walks. They generate the same subgroup: recover
\((b,0)=(ba,1)(a^{-1},1)\). Their lengths are at most

\[
 L=(2m-2)+(2m-1)=4m-3.
\]

An odd sector walk of length \(2j+1\), starting at \(g\), has row
multiplier in \(gT(T^{-1}T)^j\). This follows by cancelling each pair
of successive mutual moves; it does not require the walk to be closed.
These sets are nested because \(1\in T^{-1}T\). Therefore the symmetric
set \(S\) of new odd multipliers lies in

\[
 gY,\qquad Y=T(T^{-1}T)^{2m-2},\qquad |Y|\le w^{4m-3}.
\]

Since the pairs \((s,1)\), \(s\in S\), generate \(\Lambda\), there is
an odd word in \(S\) with product one. Thus the Cayley graph on \(G\)
with the full mutual helper set \(gY\cap(gY)^{-1}\) is nonbipartite.

The [previous general-group theorem](diagonal-code-calibration.md#5-most-translated-mutual-helper-graphs-are-bipartite)
applies uniformly to every helper set of size at most \(w^{4m-3}\).
It bounds the number of such root sectors by
\(O_{w,m}(d/\log d)\), independently of the recovery components. Every
exceptional cell belongs to this common sector set, even when components
meet overlapping sets of sectors. The projection argument of §2 finishes
the theorem. Allowing the \(B_m\) cells in larger components to be free
gives the mixed bound in §1.

A shared transcript with at most \(M\) possible values adds at most
\(\log_qM\) to these bounds. Recovery supports may depend on the
transcript, provided each fibre has the stated fixed support and, for
the mixed bound, the same upper bound on \(B_m\). Sum over the fibres.
No codeword-dependent support is free of charge.

This proof
counts neither distinct labels in an arbitrary long walk nor globally
nonbipartite components; those earlier inferences remain invalid.

## 4. Square roots and a separate near-abelian theorem

No character theory is needed for the useful estimate
\(R_2^2\le dk(G)\), where \(k(G)\) is the number of conjugacy classes.
In fact let \(k_{\rm real}(G)\) count classes invariant under inversion.
Then

\[
 \sum_z r_2(z)^2=d\,k_{\rm real}(G),\qquad
 R_2(R_2-1)\le d(k_{\rm real}(G)-1).
\]

**Proof.** The sum counts pairs \(a^2=b^2\). Write \(b=ah\); equality
is equivalent to \(a^{-1}ha=h^{-1}\). For each \(h\) conjugate to its
inverse there are \(|C_G(h)|\) such conjugators; each real class therefore
contributes \(d\). The second inequality follows on subtracting
\(\sum_zr_2(z)=d\) and keeping the maximum term. ∎

If \(k(G)\le d^{1-\eta}\), the finite bound gives vanishing excess for
\(m\le(\eta/8-\gamma)\log_wd\), with fixed \(w>1\) and
\(0<\gamma<\eta/8\). A strict margin is needed; an informal threshold
without it does not guarantee a vanishing error. This quantitative
growing-block consequence is separate from the fixed-\(m\) theorem.

**Near-abelian theorem (written proof using a cited group theorem).** Fix
\(\alpha>0,w\). If the commuting probability of \(G\) is at least
\(\alpha\), then **every** whole-row code for \(\rho(c)=cT\),
\(|T|\le w\), has rate at most \(1/2+o_{\alpha,w}(1)\), uniformly in
the alphabet. Directed and unrestricted cross-sector recovery are allowed.

**Proof.** Neumann's theorem supplies normal subgroups \(K\le H\) with
\(H/K\) abelian and \([G:H],|K|\le f(\alpha)\). The source actually
checked is Eberhard's reproof, Theorem 2.4 of
[*Commuting probabilities of finite groups*, arXiv v3](https://arxiv.org/pdf/1411.0848v3):
apply it with \(\alpha/2\), and take \(K=H'\). The published paper is
Bulletin of the London Mathematical Society **47**(5), 796–808 (2015),
[doi:10.1112/blms/bdv050](https://doi.org/10.1112/blms/bdv050).
Neumann's original is *Two Combinatorial Problems in Group Theory*,
ibid. **21**(5), 456–458 (1989),
[doi:10.1112/blms/21.5.456](https://doi.org/10.1112/blms/21.5.456).
Its bibliography was checked; its full text was unavailable in this audit.

Put \(S=T\cup T^{-1}\). Schreier rewriting in \(\langle S\rangle\)
uses at most \(2wf\) fixed letters inside \(H\), one per original
letter, and at most \(f\) final cosets. Their images commute modulo
\(K\). A word of length at most \(r\) is therefore specified by at
most \(2wf\) multiplicities in \(\{0,\ldots,r\}\), a final coset and
one of at most \(f\) lifts. Thus every Cayley ball has size at most
\(f^2(r+1)^{2wf}\). This does not require \(T\) to generate \(G\):
intersect \(H,K\) with \(\langle S\rangle\) first.

A ball in the bipartite row incidence graph projects into a Cayley ball,
with at most two ports per group element. Its size, even in any induced
subgraph, is bounded by \(V(r)=2f^2(r+1)^{2wf}\).
For any \(\varepsilon>0\), choose \(R\) with
\((1+\varepsilon)^R>V(R)\). Some radius \(i<R\) around any remaining
vertex then has shell size at most \(\varepsilon\) times its ball.
Delete that shell, retire the ball and repeat. This deletes at most
\(2\varepsilon d\) row ports and leaves components of size at most
\(V(R)\). The [row-separator bound](window-pages-and-input-attachments.md#2-a-sufficient-row-separator-bound)
gives rate at most \(1/2+\varepsilon+V(R)/(4d)\). First let \(d\)
grow, then \(\varepsilon\) tend to zero. All bounds are uniform in the
alphabet and remain valid for disconnected incidence graphs. ∎

This also supplies an independent proof of qualitative bounded coupling:
either \(R_2/d\) is small, or
\(\Pr(G)=k(G)/d\ge(R_2/d)^2\) invokes the near-abelian theorem.
The direct proof in §3 is stronger and avoids this external dependency.

## 5. Directed diagonals and finite test design

For \(G=\mathbb F_p^k\), let \(V=\operatorname{span}(T-T)\) have
dimension \(r\le w-1\). If \(g\notin-t_0+V\), a functional vanishing
on \(V\) and taking value one on \(g+t_0\) maps every diagonal helper
step onto a directed \(p\)-cycle. One layer determines all the others,
giving capacity at most \(q^{d/p}\). This is attained over **every**
finite alphabet: fix a generator in \(g+T\) and put an independent
constant on each of its directed \(p\)-cycles. Thus the good-sector
capacity is exactly \(q^{d/p}\), and arbitrary correlated own-sector codes
satisfy

\[
 \log_q|C|\le d^2/p+(1-1/p)p^r d.
\]

The conclusion \(d^2/p+O(d)\) requires fixed \(p,w\); for varying
\(p\) the explicit exceptional term must be retained. No whole-array
directed bound follows merely from this own-sector statement.

The trace control on \(n=2^a-1\) vertices has helper shifts
\(\{1,2,4,\ldots,2^{a-1}\}\). The fitting polynomial
\(1+\operatorname{Tr}_{\mathbb F_{2^a}/\mathbb F_2}(x)\) has exactly
\(2^{a-1}\) simple nonzero roots, so its cyclic kernel has that dimension.
For \(a\ge3\) the relation is oriented. This is a written proof for all
\(a\), not just the checked small cases; its window grows and its excess
is only half a symbol. At \(a=1\) there is a loop, and at \(a=2\) the
relation is bidirected.

The proposed \(7{:}3\) and \(13{:}3\) experiments do not isolate long
coupling. For \(T=\{e,a,b\}\), with \(a\) a translation and \(b\) an
order-three dilation, six sectors have shortest odd return one and every
other sector has shortest odd return three. Three loop sectors are free;
two other sectors support sum-zero triangle codes. The remaining sectors
can be matched in pairs with valid equivariant mutual edges. This gives

| Group | Cells | Pairing plus loops | Triangles, pairs and loops |
|---|---:|---:|---:|
| \(7{:}3\) | 441 | 252 symbols | **259 symbols** |
| \(13{:}3\) | 1521 | 819 symbols | **832 symbols** |

These constructions work over every finite alphabet and use blocks of
at most two sectors. Their dimensions are lower bounds, not optimized
capacities. Even a gain over pairing plus loops would therefore fail the
suggested success test. Moreover both group families have an abelian
normal subgroup of index three, so the near-abelian theorem covers their
full whole-row codes as their orders grow. No solver search was run after
these exact controls invalidated the proposed comparison.

## 6. Verification and what remains open

[`SectorWalks.lean`](../SectorWalks.lean) verifies the actual cell/sector
move, reverse move, two-step identity, square-root reduction, and the
algebra behind the elementary second moment in every group. Its seven
endpoints use only `propext`. It does **not** formalize the walk counts,
voltage subgroup argument, capacity theorem, or separator proof.

```sh
cd lean-machine
lake env lean ../lean-backlog/SectorWalks.lean
```

The exact finite controls, including fixed matching certificates, run from
the repository root with:

```sh
python3 lean-backlog/tools/bounded-sector-controls/check.py
python3 lean-backlog/tools/sector_walks.py
```

The latter checks odd-sector sets exhaustively on its selected instances;
its literal cell-step checks are seeded samples, not an exhaustive cell
census. Neither script replaces the unbounded written proofs.

The remaining mutual question requires unbounded sector coupling on groups
outside the uniform near-abelian regime. Such groups need not be expanders;
expansion is a separate useful test case. No theorem here says that every
gain uses logarithmically many sectors on every group, or that a bounded
block is literally bipartite. The low-square-root estimate gives that
quantitative restriction only under its stated class-count hypothesis.

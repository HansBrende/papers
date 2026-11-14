# Transported closure certificates and native bit cones

Hans Brende and GPT-6 Astra, with Claude Fable 5.2's audit questions,
14 November 2026. **Status:** the finite assigned-rule theorem and transported
invoice corollary in §1 are Lean-verified in
[ClosureBarriers.lean](../ClosureBarriers.lean). The multi-option extension
and native audit retain independently reviewed written proofs.
No literature novelty claim. This is the bounded D9 audit following the
[two-sided transfer](two-sided-whole-row-codes.md), not a new capacity bound.

**Outcome B:** no new native property supplying the proposed invoice was found.
More generally, transported closure followed by additive message counting cannot
improve the optimal one-copy acyclic bound. This does not rule out using transports
as a way to discover a large acyclic set, or proving that native cones have one.

## 1. Assign each recovered coordinate to the rule that supplied it

Let V have N coordinates. For j=1,…,m, let G_j specify one helper set H_j(v)
for every v∈V, with arcs v→h for h∈H_j(v). A self-helper is a loop. Let α_j
be the largest number of vertices in an induced directed acyclic subgraph of G_j.
Suppose S generates all coordinates by repeatedly applying any displayed rule:
if all coordinates of H_j(v) are known, adjoin v.

**Theorem (assigned-rule bound).**

$$N-|S|\le\sum_{j=1}^m\alpha_j.$$

**Proof.** List coordinates outside S in a successful recovery order. Assign each
one to one copy whose helper set was already known when it was recovered. Let A_j
be the set assigned to j. Every edge of G_j induced on A_j points to a coordinate
earlier in that order. Thus G_j[A_j] is acyclic, including the exclusion of loops,
and |A_j|≤α_j. The sets partition V∖S, so sum. A rule recovering a whole bundle
can be refined to single-coordinate recoveries using its same already-known
helper bundle. ∎

For m coordinate permutations of one graph G, α_j=α(G). Write g_m for the minimum
combined seed size. Then

$$g_m\ge N-m\alpha(G),\qquad
  \frac{(m-1)N+g_m}{m}\ge N-\alpha(G).$$

The second expression is precisely the upper bound obtained by intersecting m
translated code copies and counting a generating seed, as in the
[two-sided note, §7.1](two-sided-whole-row-codes.md#71-transported-intersections).
It can never be below the original acyclic-set upper bound. This is valid for
all graphs, all transports and all positive m, including m depending on N.
It is a comparison of **proof certificates**, not a lower bound on code capacity
or on its full Shannon relaxation.

For native bit cones, α means the maximum induced acyclic set on the actual bits,
not an approximate row-order statistic. For a full whole-row host, Paper 17's
Proposition “The order bound for whole rows” proves α=d²−σ(ρ), so there it is
exactly the published row-order bound. The earlier
[empty-rectangle bound](two-sided-whole-row-codes.md#72-a-uniform-limit-of-transported-closure-counting)
retains its sharper quantitative dependence on m for those hosts; that
finite bound and its invoice are also [Lean-verified](../RectangleBarrier.lean).

**Several helper options per coordinate.** The same argument extends to a
monotone system of displayed functional-dependency rules. If g_j is the minimum
seed size for system j alone, the assigned set A_j can be recovered from V∖A_j
by replaying its subsequence of the joint recovery order. Consequently

$$g_{\rm combined}\ge\sum_j g_j-(m-1)N.$$

In particular, intersecting transported copies of an already two-sided rule
system cannot improve that system's best coordinate-seed certificate. This
extension does not include extra dependencies discovered from the joint code's
algebra or entropy; those would be new rules, not a replay of the displayed ones.

## 2. Consequence for the exact proposed native invoice

Let N=d²b and T denote the transposition permutation of raw bit coordinates.
The native target-indexed helper relation is

$$H_v=I_\Gamma(Tv).$$

Paper 14's `exists_indexCode` supplies a B-bit full-cube index message E, with
B=β|Γ|, **if the machine is an oblivious correct transposer**. The definition
of `SCone` itself imposes neither correctness nor cheapness of Γ.

Given a transport Φ and a seed S for H together with Φ(H), the map

$$x\longmapsto\bigl(E(x),E(\Phi^{-1}x),x|_S\bigr)$$

is injective. Thus the proposed inequality 2B+|S|<N would indeed contradict
correctness. However, the assigned-rule theorem gives

$$N-|S|\le2\alpha(H).$$

A successful invoice would therefore imply α(H)>B. That already contradicts
the **one-copy** index-code bound B≥α(H): fix the complement of an acyclic set;
the message successively determines all its coordinates, so their 2^α possible
assignments require distinct messages. One of the two assigned sets explicitly
provides this one-copy certificate.

Hence doubling does not add lower-bound power to acyclic counting. A new native
construction of such a seed could still discover a valid acyclic certificate;
the theorem does not prove that no native geometry can supply α(H)>B.

For completeness, the elementary degree estimate in the proposed audit can be
sharpened. If every |H_v|≤K and s targets lack their own source in H_v, retain each
such target when it precedes all its helpers in a random order. The retained set
is acyclic and has expected size at least s/(K+1). Therefore

$$s\le(K+1)B.$$

This improves the independent-set estimate (2K+1)B, but K still grows
exponentially with the available dependency depth. It gives no adequate native
rate improvement by itself.

## 3. What the native geometry actually supplies

The declarations are `depCone`, `coneSystem`, `SCone` and `exists_indexCode` in
[Paper 14's Machines.lean](../../Bounded-Stack-DAGs-Reduce-to-Constant-Depth/lean/BoundedStackDepth/Machines.lean).
Paths include the state spine and all work returns. A cut is excluded from the
path's tail; a revealed root's own read still belongs to the displayed cone.

**Occurrences are not raw bits.** A time vertex contributes at most one in-range
input bit, since `readPos` is optional. Last visits on one work tape are injective
between time occurrences: a later visit would otherwise have an intervening visit
to the same cell. Together with the state edge, the time DAG has forward and
reverse degree at most k+1. Assume every Γ-free dependency path has at most
D edges, including state edges and work returns. Put K_D=Σ_{j=0}^D(k+1)^j.
If r_a is the number of raw
reads of bit a before the horizon, the valid estimate is

$$\#\{v:a\in H_v\}\le K_Dr_a,\qquad \sum_a r_a\le T_{\rm time}.$$

The read projection can identify arbitrarily many occurrences. For example,
a parked input head labels every append-root read by the same bit; those root
reads survive any cut. Thus depth does not give free bounded reverse degree
on raw bits. Paying to freeze high-reuse bits is the existing repair
(Paper 5, Corollary 3.8; Paper 15, Theorem N), not a new native property.

**A monotone current run need not have isometric last visits.** Consider the
pause-free unit walk with positions

0,1,2,3,2,1,0,1,0,1,2,3.

On its final increasing run, at times 8,9,10,11, the last-visit times are
6,7,4,3. They are not isometric, nor monotone on the whole run. An affine map
of slope ±1 is obtained only after fixing both the earlier and later strict
motion pieces. Input-head motion, stays, changes of earlier visit piece and
conversion from output rank to append time require further subdivisions.
Linear time permits linearly many pieces; it does not bound their number.

The exact cone form is a union of maps

readPos ∘ predecessor_word ∘ appendTime ∘ T,

on the domains where the path exists and avoids the cut after its root.
There are at most K_D path words, but neither a bounded number of isometry
pieces per word nor injectivity of the read projection follows.
Also T((di+j)b+s)=(dj+i)b+s: it is a translation on every b-bit entry block.
The assertion that transpose is isometric on no interval longer than one point
is false at the canonical b>1; at b=1,d=2 the middle two points also give a
reflection. These qualifications do not themselves imply an information-routing
lower bound.

## 4. The controls do not supply a transpose-demand counterexample

| Existing control | What it proves | What it does not provide for this invoice |
|---|---|---|
| Paper 9, serial quadratic cover (`serial_quadratic_cover`) | A legal eight-tape geometry with a selected paid cone containing (M−1)² distinct raw bits and a quadratic fractional core-cover cost | No cheap transpose-demand index code or bound on all transported seeds. That displayed cut cannot keep full depth D fixed as M grows, since its cone size is at most Σ_{j=0}^D9^j. A later cut can remove its witness paths. |
| Paper 9, gap-area memo, Theorem Z | Sharpness of the stated inverse-square envelope and gap-area statistics | No correctness-set or complete fixed-depth index-code witness. Its scalar-cover obstruction is not a closure-seed obstruction. |
| Paper 18, Theorem 7.1, redundant-store normalization | A wrapper preserving any machine's halting output and linear time, with fixed resource changes, while readable store words mutually determine one another | This is stronger than an incorrect-transduction control, but supplies no chosen cheap cut or cheap transpose-demand code. One intact raw archive still has N bits of information; identical copies are not all free. |
| Paper 18, control after Corollary I.3 | Copy/rescan produces Θ(Nd) historical feedback in O(N) time | No transposition output or transpose-demand index message. Large feedback is not an independent-information bill. |
| Adjacent-pair transducer | Linear-time unit-speed motion need not be literally shift-covariant | It is not a transposer, and does not prove failure of every broader or correctness-dependent normal form. |

Sources: [Paper 9 limitations](../../Source-Covers-and-Barriers-to-Tape-Transposition/paper/sections/limitations.tex),
[gap-area sharpness](../../Source-Covers-and-Barriers-to-Tape-Transposition/memo-gap-area/paper/sections/sharpness.tex),
[Paper 18 limitations](../../Macroscopic-Information-Transfer-in-Adaptive-Tape-Transposition/paper/sections/limitations.tex),
[feedback](../../Macroscopic-Information-Transfer-in-Adaptive-Tape-Transposition/paper/sections/feedback.tex),
and [the pair-swap audit](row-spread-of-cones.md#31-shift-covariance-existing-bounds-and-the-native-gap).

## 5. Stop point and what remains outside the theorem

The one-unit audit returned **B**, without a solver or new host. Its subsequent
consolidation formalized the assigned-rule bound; it supplied no new native
extraction premise.
The controls do not establish a cheap-code counterexample to the proposed native
property. Instead, the general assigned-rule theorem shows that its advertised
advantage over the one-copy order method is absent.

The remaining possibilities require additional information. Examples are an
extra functional dependency or Shannon inequality on the joint fibre, a genuine
native extraction of a large acyclic set, or a proved bound on the **joint**
message range/entropy smaller than the sum of the separately billed messages.
The last would change the invoice; it is not supplied merely by using the same
encoder twice. These are boundaries of this result, not new proved premises.
The general native crux, all-code capacity question and transposition problem
remain open. The next research choice follows consolidation rather than
another transported-closure search.

## Addendum: order certificates at cone level (Fable, 14 November; unreviewed)

A small native-side remark for the open kind "an acyclic certificate from native geometry". No
machine exclusion follows from it.

**Acyclic number as an order statistic.** For a helper graph with one displayed helper set H(u) per
target, α = max over linear orders ≺ of the coordinates of #{u : every element of H(u) precedes u}.
(An acyclic set with its order, the complement placed first, is such a family; conversely the
targets counted by any ≺ form an acyclic set.) So every linear order definable from the schedule is
a candidate certificate, and each one gives a necessary condition on correct machines: at most B
targets have their whole cone before them.

**Two orders that the schedule supplies.**
- *Output order.* Call an output bit *backward* if every bit of its cone has already been written
  when it is written, *forward* if every bit of its cone is written later. Ordering by output time,
  and by its reverse, shows that there are at most B backward and at most B forward bits. So in a
  correct oblivious machine with a cut of cost B, all but 2B output bits either contain their own
  source or have cones that **straddle the output position**: they read a source bit from a column
  already written and one from a column not yet written.
- *First-scan order.* The same with "first scanned by the input head": at most B output bits are
  computed only from bits first scanned before their own source, and at most B only from bits first
  scanned after it.

Pairing-type schedules (entry (i,j) from entry (j,i)) have about N/2 backward bits, and are
excluded by the first statement alone, as expected. A scheme that survives must be mixed in both
orders on all but 4B bits. This is the cone-level analogue of the window-two cyclic host, whose
helpers sit on both sides.

**What a certificate of this kind would be.** A linear order on bit positions, defined from head
positions and visit times alone, under which more than B targets have their whole cone before them
for every linear-time oblivious schedule and every cheap cut. The two orders above do not do it:
nothing forces cones to be one-sided in either.

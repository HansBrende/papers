# Extending a pairing or parity-block template costs only a vanishing rate

Claude Fable 5.2 and GPT-6 Astra, directed by Hans Brende, 14 November 2026.
**Status:** written proofs, independently reviewed; abstract counting, local
parity extension, compatibility extraction and recovery-to-record separation
for ordinary and automorphism-weighted sums are Lean-verified, including finite
counts, the full-invariance involution adapter, and singleton pinning for
prescribed zero shifts. The whole-row record enclosures, active-block
incidence count and finite bounded-degree parity-template bound are also
Lean-verified, with arbitrary finite lanes and rectangular row/column types.
Paid heavy-row deletion and a uniform vanishing-excess theorem for active
parity templates are Lean-verified as well. Selection from an omitted
involution-orbit list and the sharper fixed-cell pairing correction remain
separate written specializations.
Fable proposed the
pairing-coset bound; Astra repaired its incident-cell step and derived the sharper finite,
partial-invariance and forward-window-only forms below. No literature novelty claim.
Front D1: a restriction on constructions, not a bound for every whole-row code.

## 1. Pairing shifts and the exact record

Let the cells be V=[d]×[d], N=d², and let column c be recovered from the bundle
B_c=ρ(c)×[d]. Write M_c=ρ(c), J_c=⋃_{r∈M_c}ρ⁻¹(r), and
L=∑_c|ρ(c)| for the number of incident cells (p,c) with p∈ρ(c).
The alphabet is a finite abelian group of order q≥2, and C is a nonempty,
possibly nonlinear whole-row code. Empty codes satisfy the cardinality bounds trivially.

Fix any involution ι of V. Its orbit-constant subgroup is
P_ι={S:S∘ι=S}, with log_q|P_ι|=(N+f)/2, where f is its number of fixed cells.
Assume C+P_ι=C. For linear C, this means P_ι⊆C.

**Compatibility is a consequence, not an additional hypothesis.** If a nonincident v has
ιv outside its helper bundle, a nonzero shift of its orbit changes v while fixing every
helper, contradicting recovery. Thus ιv lies in the bundle. A fixed cell must be incident.
In particular P_ι is itself a whole-row code under this full-invariance hypothesis.

For every two-cell orbit choose one orientation and record the difference
A_X(v)=X(v)−X(ιv). Let Q_c be the two-cell orbits contained entirely in B_c,
and let Q₀ be the two-cell orbits both of whose cells are incident. Set

T=Q₀∪⋃_c Q_c.

**Exact quotient bound.** The differences on T determine every orbit difference occurring
in C. More precisely, if Z_T(C) is their attained image, then

|C|=|P_ι|·|Z_T(C)| ≤ |P_ι| q^|T|.

The abstract counting step is
[`CosetRecords.card_eq_subgroup_mul_image`](../../lean-machine/LeanMachine/CosetRecords.lean).
For an additive commutative group, a set C stable under a subgroup P, and a
record invariant under P-translations on C, it proves
`Nat.card C = Nat.card P * Nat.card (record '' C)` as soon as equal records
of two elements of C imply their difference lies in P. The record need only
separate cosets **on C**; its ambient fibres can be larger. The code need not
be linear or nonempty, and the record type need not be finite. The proof
reuses Mathlib's subgroup saturation count. The local parity-extension step
is formalized as described in Section 5. The involution-orbit instantiation is
now in [`InvolutionSums.lean`](../../lean-machine/LeanMachine/InvolutionSums.lean):
`kernel_eq` identifies the +1/−1 pair-sum kernel with orbit-constant shifts,
`card_orbitConstant` proves q^((N+f)/2), and
`card_eq_orbitConstant_mul_record` / `card_le_pow` prove exact counting and
the bound q^((N+f)/2+|T|). The finite code bound allows empty C and trivial
alphabets. Its views are arbitrary sets H(v); Section 5 now supplies the
general whole-row bundle/enclosure adapter. Combining it with these
oriented involution blocks and the sharper fixed-cell count remains a
separate specialization. The following written proof describes that application.

**Proof.** Suppose X,Y have the same recorded differences. On B_c prescribe
S(u)=Y(u)−X(u). This is consistent on every orbit contained in B_c because its difference
was recorded. If an orbit meets B_c once, extend the prescribed value to its partner;
choose zero on untouched orbits. Then S∈P_ι, so X+S∈C, and X+S agrees with Y on B_c.
Recovery gives agreement on column c. For a nonincident target v in that column,
its partner also lies in B_c; hence the difference at v agrees. An orbit with one
nonincident cell is now determined, and the remaining two-cell orbits were recorded
in Q₀. Fixed-cell differences are zero. Finally, each full difference fibre is a coset
of P_ι; invariance fills that coset. ∎

**Why the incident exception is necessary.** At d=2, take ρ(c)={c}, let ι swap the two
diagonal cells and also the two off-diagonal cells, and take C to be all symmetric matrices.
Then C+P_ι=C and every Q_c is empty, but the diagonal difference is free. Q₀ records it.
Thus the original claim that the internal differences determine the difference on an
entire column was false; the theorem survives after this repair.

## 2. Sharper finite bound

Every cell of an orbit in Q_c belongs to M_c×J_c. For a nonincident cell, its partner's
row witnesses membership of its column in J_c. For an incident cell, its own row does.
Consequently 2|Q_c|≤|M_c||J_c|. All f fixed cells are incident, so 2|Q₀|≤L−f. Therefore

2 log_q|C| ≤ N+L+∑_c |M_c||J_c|.

If every forward degree is at most w and every reverse degree at most D, this gives

log_q|C| ≤ N/2 + (w+w²D)d/2.

The exact union T can be much smaller than this sum. Relative to P_ι, the finite gain is
at most (L−f+∑|M_c||J_c|)/2. This sharpens the original coefficient (w²+w)Dd.
For d>0, full invariance forces an incidence and hence w,D≥1; the d=0 case is immediate.

## 3. Missing individual pairing shifts

Suppose the shifts on b two-cell orbits are unavailable, but C is invariant under
independent orbit-constant shifts on every other orbit, **including every fixed cell**.
Let P_active be this smaller subgroup. Compatibility is forced only on active orbits.
The full orbit-constant P_ι is an algebraic reference; it need not be a recovery code
on the inactive orbits.

Record all 2b inactive coordinates, and the differences on the active version of T.
The previous matching argument applies: the inactive coordinates already agree, and
only active shifts are used. The number of gauge choices is q^((N+f)/2−b), so the net
additional price is **one symbol per omitted pair**, not two. In particular,

2 log_q|C| ≤ N+2b+L+∑_c |M_c||J_c|.

The active-fixed-cell assumption matters if full compatibility is dropped. If inactive
nonincident fixed cells are also permitted, add their number to the right side.

**Formalization boundary and reuse.** The full-kernel hypothesis is stronger
than the active-shift hypothesis here; omitted pairs are not only a numerical
bill. But compatibility need not be proved again. Keep only the active pair
blocks, and add a singleton zero-sum block {e} at each inactive coordinate e.
Its kernel forces the shift at e to be zero. Record every singleton syndrome,
which is exactly the raw value at e. The existing disjoint-sum library allows
singleton blocks: its only size premise is nonemptiness. Its fully-viewed and
all-incident enclosures are automatic for these always-recorded singletons;
the remaining enclosures concern the active pairs. There are M−b active pairs
and 2b singleton blocks if the original involution has M pairs. The kernel
exponent is N−M−b, and recording 2b raw symbols yields the claimed net price b.
The generic block construction and raw-record conversion are now Lean
endpoints in [DisjointSumsPinned.lean](../../lean-machine/LeanMachine/DisjointSumsPinned.lean).
`withPins` adjoins the singletons to any active bank D disjoint from E.
`withPins_encode_eq_zero_iff` proves that its weighted kernel consists
exactly of shifts in the active kernel that vanish on E. Thus it grants
none of the omitted shifts. `withPins_encode_eq_of_recovery` applies the
existing weighted theorem, with all singleton syndromes recorded; only
the active blocks need the fully-viewed/all-incident enclosure conditions.
The public record is the pair of **raw** values on E and selected active
syndromes, even when the singleton weights are arbitrary automorphisms.

`card_eq_pinned_kernel_mul_record_image` gives the exact kernel times
attained-record-image identity. With N coordinates, a active blocks and
e pinned coordinates, `card_pinned_kernel` gives q^(N−a−e), while
`card_le_pow_of_pinned_invariant_recovery` gives q^(N−a+|T|).
The e-symbol record price cancels exactly the e lost kernel dimensions.
Taking a=M−b gives the one-symbol cost per omitted pair above, and more
generally per omitted single-parity block, regardless of its size.
Global identities require finite active and pinned index types; the power
bound explicitly assumes finite coordinates, active indices and alphabet.
Empty codes and trivial additive alphabets are allowed. The generic
adapter does not construct the active pairs from an involution. The
whole-row enclosures and general active-block incidence estimate are now
supplied by Section 5's adapter; the sharper fixed-cell correction in
Section 2 still needs its own endpoint. The general active-template
heavy-row theorem is now formalized below.

This measures loss of **individual orbit shifts**. A large abstract intersection C∩P_ι
alone does not supply them: a linear constraint can exclude every individual shift while
leaving a large intersection. No extraction of this invariance from machine correctness
is claimed.

## 4. No reverse-degree assumption is needed asymptotically

Keep forward width at most w and the partial-invariance hypothesis of Section 3.
For any integer R≥0 let H be the rows of reverse degree greater than R. Double counting gives
(R+1)|H|≤wd. Mark every active two-cell orbit meeting H×[d]; at most d|H| pairs are newly
marked. Deactivate the fixed cells in those rows as well. Let E contain all inactive or
newly marked orbits, and put M'_c=ρ(c)∖H. The trimmed reverse degrees are at most R.

Record the raw values on E and the active orbit differences on the internal pairs of
the trimmed bundles, together with the active all-incident pairs. Agreement on E includes
every heavy helper row. We can therefore match the remaining helper values by active
shifts and invoke the **original** recovery rules. No separate charge for conditioning
on the heavy rows is necessary.

If b' pairs have been deactivated, the remaining gauge exponent plus |E| is
(N+f)/2+b', even when some fixed cells are deactivated. Every original fixed cell was
incident, so the all-incident-pair count still pays at most (L−f)/2. Hence

log_q|C| ≤ N/2+b + wN/(R+1) + (w+w²R)d/2.

Choose R=⌈√d⌉. Uniformly over alphabets, helper relations and involutions, at each fixed w,

log_q|C|/d² ≤ 1/2+b/d²+O_w(d^−1/2).

**Consequence.** A positive asymptotic gain over one half requires missing individual
pairing shifts on a positive fraction of the two-cell orbits. Full or all-but-o(d²)
pairing invariance cannot produce such a gain, even with unrestricted reverse degrees.
This excludes a construction class; it does not prove the common deficit for arbitrary codes.

## 5. Triangle lanes and general single-parity blocks

The same gauge argument applies to disjoint single-parity blocks. Here V=[d]×[d]×[b₀],
N=b₀d², the helper bundle is B_c=ρ(c)×[d]×[b₀], and C is a nonempty whole-row code
on these coordinates. Take disjoint blocks B₁,…,B_m of size at least k≥2. On each block impose
∑_{v∈B_j} θ_v(X(v))=0, where each θ_v is an automorphism of the abelian alphabet.
Coordinates outside these blocks are free. Let P be this product subgroup; log_q|P|=N−m.
Pair differences use weights +1,−1; triangle lane codes use three +1 weights.

**Partial-assignment extension (Lean).** For finitely many pairwise disjoint
nonempty finite supports, a prescribed word on any coordinate set S extends
to arbitrary target block sums if and only if every block contained in S
already has its target sum. This is
[`DisjointSums.exists_extension_iff`](../../lean-machine/LeanMachine/DisjointSumsExtension.lean).
Its proof applies the existing `encode_surjective` to the nonempty residual
supports outside S, then adds that correction while fixing S. The derived
`exists_kernel_shift` matches two partial words by a zero-sum shift when
their sums agree on every fully observed block. The theorem
`exists_weighted_extension_iff` covers the automorphisms θ_v above.
These statements require only an additive commutative group: neither the
alphabet nor the coordinate type must be finite.

**Recovery-to-record adapter (Lean, ordinary sums).**
[`DisjointSumsRecords.lean`](../../lean-machine/LeanMachine/DisjointSumsRecords.lean)
now proves the global step for ordinary block sums and arbitrary coordinate
helper views. Its local lemma only requires that a block be contained in a
helper view together with its recovered coordinate. For a code invariant
under the sum kernel, aligning that view and then recovering the coordinate
determines the block's sum. The global theorem needs only one such view for
each unrecorded block, with every block wholly in that chosen view recorded.
Thus it is weaker than requiring the template geometry at every coordinate.

`encode_eq_of_compatibility` derives separation from the displayed
nonincident-coordinate compatibility premise, recording all fully viewed
and all all-incident blocks. `card_eq_kernel_mul_record_image` then proves
the exact product of kernel cardinality and attained-record cardinality.
These results allow nonlinear or empty codes and need only a finite block
index, not a finite alphabet or coordinate type.

**Compatibility extraction (Lean, ordinary sums).**
[`DisjointSumsCompatibility.lean`](../../lean-machine/LeanMachine/DisjointSumsCompatibility.lean)
removes that explicit premise. On a nonempty code over a nontrivial additive
alphabet, a kernel shift invisible to a recovery view cannot change the
recovered coordinate. Two cancelling shifts inside one block therefore give
`support_subset_insert_of_recovery`: a nonincident target's block lies in
its view together with the target. A shift of a free coordinate gives
`mem_view_of_free`: that coordinate must itself be in its recovery view.
Neither local lemma requires a finite block index.

For finitely many blocks, `encode_eq_of_invariant_recovery` uses these facts
to separate all sums by any record containing every fully viewed and every
all-incident block. `card_eq_kernel_mul_record_image_of_recovery` proves the
exact kernel-times-attained-record count under those same enclosures. These
global wrappers handle empty codes and trivial alphabets without extra
premises.

**Weighted global adapter (Lean).**
[`DisjointSumsWeighted.lean`](../../lean-machine/LeanMachine/DisjointSumsWeighted.lean)
uses Mathlib's `AddEquiv.piCongrRight` to apply θ_v at coordinate v.
This bijection preserves equality on every helper view. Transporting the
code through it reduces weighted-kernel invariance and recovery to the
ordinary-sum theorems. `weighted_support_subset_insert_of_recovery` and
`weighted_mem_view_of_free` retain the local nonempty/nontrivial premises
and allow infinitely many blocks. `weighted_encode_eq_of_invariant_recovery`
separates all weighted syndromes by the same fully-viewed/all-incident
record, and `card_eq_weighted_kernel_mul_record_image_of_recovery` gives
the exact weighted-kernel-times-attained-record count. These global
statements need finitely many blocks, but allow empty codes, trivial
alphabets and infinite coordinate or alphabet types. No field or scalar
linearity is assumed. `weighted_fiber_card`, `card_weighted_kernel` and
`card_le_pow_of_weighted_invariant_recovery` explicitly assume finite
coordinates, blocks and alphabet and give fibre size q^(N−m) and code bound
q^(N−m+|T|). These remove the infinite-type degeneracy from finite applications.
The involution conversion and prescribed-coordinate pinning are formalized
as above. The finite whole-row application is now formalized as described
below, including paid heavy-row deletion and the uniform asymptotic application.

Suppose C is invariant under the parity kernels of all but a blocks and under shifts
of every free coordinate. With omitted blocks, P is an algebraic reference and need not
itself be a recovery code. For an active block and a nonincident v in it, recovery forces
B_j∖{v}⊆B_col(v): otherwise a two-coordinate compensating parity shift changes v while
fixing its helpers. Free coordinates must be incident.

Record raw values on the omitted blocks and one syndrome per active block which is
all-incident or contained in a helper bundle. Call the latter union T. To match values
on a helper bundle, a block not wholly contained in it has an unobserved coordinate
that can absorb the parity discrepancy. A contained block needs precisely its recorded
syndrome. Recovery then determines every active syndrome with a nonincident coordinate;
the remaining ones were recorded. Thus

log_q|C| ≤ (N−m)+a+|T|,

and, with reverse degree at most D,

k|T| ≤ b₀∑_c|M_c||J_c|+b₀∑_c|ρ(c)| ≤ b₀d(w²D+w).

Omitting one parity-block kernel costs one symbol, regardless of block size. There is
also a forward-width-only version. Retain the raw record on the a omitted blocks and
mark every retained block touching a heavy row; at most wb₀d²/(R+1) blocks are marked.
Freeze those newly marked blocks and the free coordinates in heavy rows.
Their raw-coordinate price cancels their lost gauge exponents except
for one symbol per marked block. Apply the preceding bound on the trimmed relation:

log_q|C| ≤ (N−m)+a + wN/(R+1) + b₀d(w+w²R)/k.

With R=⌈√d⌉, the gain over the template exponent is at most a+o_w(N), uniformly in b₀ and q.
This is stability under extension of a **specified parity template**, not a universal
bound on its baseline rate, nor a normal form for arbitrary codes.

**Whole-row enclosure and count adapter (Lean).**
[WholeRow/ParityTemplate.lean](../../lean-machine/LeanMachine/WholeRow/ParityTemplate.lean)
uses finite row and column types R,J and a finite lane type Λ. Its
coordinates are R×J×Λ, with N=|R||J||Λ|. `RecoversFromRows` means that
agreement on all lanes in rows ρ(c) determines every coordinate of column c;
the code and the recovery need not be linear. This is an agreement-based
statement, not a selected decoder or field representation.

The input D consists of m_act **active** blocks, disjoint from the pinned
set E, and the code is invariant under their weighted kernel shifts that
vanish on E. The endpoints accept the more general conditional form
`RecoversFromRowsGiven`: agreement on the helper bundle **and E** determines
the target. Ordinary whole-row recovery implies this premise via
`RecoversFromRows.given`. Raw pins can therefore remain available while
helper rows are removed. `recordBlocks` is the exact union of all-incident active blocks
and active blocks contained in some helper bundle. `parity_record_card_eq`
and `parity_card_le_record` discharge both enclosures in the pinned theorem
and give exact attained-record counting and q^(N−m_act+|T|).

For each internal active block of size at least two,
`internal_support_subset_rectangle` derives containment in M_c×J_c×Λ
from recovery and invariance. It handles incident coordinates by their own
row and nonincident coordinates by any other member of the block, using
the existing compatibility theorem. Disjoint-support counting then proves
`recordBlocks_card_bound`: for any lower size bound r≥2,

  r|T| ≤ |Λ| [Σ_c |M_c| + Σ_c |M_c||J_c|].

The local geometric count assumes a nonempty code and nontrivial alphabet.
The cardinality endpoints handle empty codes and trivial alphabets as well.
`parity_card_le_incidence` retains the displayed incidence sum and integer
floor, and `parity_card_le_degrees` gives

  |C| ≤ q^[N−m_act + floor(|Λ||J|(w+w²D)/r)]

when forward degrees are at most w and reverse degrees at most D. These
finite statements are uniform in the finite abelian alphabet and lane
count, and strengthen the square-array formulation to rectangular arrays.
The record union can be smaller than the sum used in this last estimate.
The finite adapter takes active blocks/pins as data. Deleting heavy rows is
now handled by the following construction; choosing the original active
blocks from an omitted involution-orbit list and the sharper fixed-cell
pairing correction remain separate specializations.


**Paid heavy-row adapter and uniform rate (Lean).**
[DisjointSumsDeletion.lean](../../lean-machine/LeanMachine/DisjointSumsDeletion.lean)
constructs the subfamily avoiding a finite set F of coordinates. Let t_F be
the number of discarded active blocks. Their disjoint nonempty
intersections with F give t_F≤|F|. The new pin set is E′=E∪F∪(discarded
supports). It is disjoint from all retained blocks, and every new kernel
shift fixing E′ lies in the original kernel and fixes E. No discarded
block is silently turned into a free shift.

[WholeRow/ParityTrimming.lean](../../lean-machine/LeanMachine/WholeRow/ParityTrimming.lean)
uses F=H×J×Λ for a set H of rows. Given the common raw record E′, the
original recovery implies recovery on ρ(c)∖H. The conditional version of
the finite bound applies to the original C; no independent fibre partition
or second charge for the raw record is needed. `parity_card_le_delete_rows`
retains the exact price t_F, one symbol per discarded block. If trimmed
reverse degrees are at most D, its exponent is

  N−m_act+t_F + floor(|Λ||J|(w+w²D)/r).

For H the rows of reverse degree greater than D, incidence counting gives
(D+1)|H|≤w|J|. Thus `parity_card_le_forward` proves

  |C| ≤ q^[N−m_act + |Λ||J| floor(w|J|/(D+1))
                     + floor(|Λ||J|(w+w²D)/r)].

This needs only forward width w; D is any chosen natural threshold,
including zero. It remains valid for empty codes, trivial finite
alphabets, empty index types and arbitrary finite lanes. In rectangular
arrays the coarse row payment is w|Λ||J|²/(D+1); it is wN/(D+1) in the
square case, not in general.

For |R|=|J|=d, `parity_card_pow_le_baseline` makes the vanishing excess
uniform and quantitative. Given any integer n≥1, choose D=2wn. Once

  d ≥ n(w+w²(2wn)),

it proves the entirely finite cardinality inequality

  |C|^n ≤ q^[n(N−m_act)+N].

Indeed twice n times the row payment is at most N; twice n times the
incidence payment is also at most N, since r≥2 and the displayed
threshold holds. Hence their sum is at most N/n. For q≥2, nonempty C
and N>0 this says log_q|C|/N≤1−m_act/N+1/n. The threshold is independent
of q, lanes, the particular relation, block sizes and additive weights.
This is excess above a specified active-template baseline; that baseline
can itself approach one. It is not a common deficit for arbitrary codes.

## Scope of the examples

The grid's displayed shared-object construction has a pairing template. The theorem
does **not** explain every known O(d) gain: a binary sum-zero triangle excludes its
all-one word, whereas every full orbit-constant pairing subgroup contains that word.
The binary cyclic window-two difference code at d=3 likewise excludes the all-one word.
Those examples need their own checks; being linear is not enough to contain a pairing code.

Abstract counting, local disjoint-parity extension, compatibility extraction
and global separation/counting for ordinary and automorphism-weighted sums
are Lean-verified, including finite cardinalities and the full-invariance
involution conversion, singleton pinning, whole-row enclosures and the
finite general parity-template incidence and bounded-degree estimates,
paid heavy-row deletion, the forward-width-only bound and its uniform
vanishing-excess consequence. Omitted-involution-orbit selection and the
sharper pairing fixed-cell correction remain written specializations. Invariance
is relative to a specified additive
group on the entry alphabet; for b-bit symbols bitwise XOR supplies one such
group. No claim identifies invariance under different choices of group law.
The argument uses subgroup invariance
of the code, not merely sparsity of a decoder, local graph statistics, or a large
intersection with a template. The native question still needs a premise that supplies
one of these hypotheses, or a different capacity argument.

# What the proved code classes exclude on tapes

Hans Brende and GPT-6 Astra, 14 November 2026.
**Status:** consolidation of existing results, with the additional hypotheses
stated explicitly. This is not a new unconditional machine exclusion.

## The common accounting

Fix the work-tape count k, value width β, time constant C≥1 and ε>0 before
letting d grow. Put P=d²b(d), D=genieDepth(k,β,C,ε), and
W=rowSpreadWindow(k,β,D,C,ε). B1 produces a whole-row relation of width at
most W after paying for a cut extension and exceptional columns. It does
**not** produce any additional class property in the table below.

On a correct oblivious machine, the direct construction pays at most
εP for the original genie, 63εP/64 for the added step values, and
21εP/32 for exceptional input columns. Thus a bound of rate
1−δ+o(1) on all the resulting fibres excludes such machines when

δ > 169ε/64.

An extra record or a structured-subcode loss of p(d) bits changes the test
to δ>169ε/64+p(d)/P, with a strict asymptotic margin. Internal payments
already present in a theorem's rate estimate are not charged twice. A
single structured fibre also suffices if its required large cardinality
has been proved; an arbitrary small subcode does not.

For a result available only for two-sided codes, the translated-intersection
adapter gives one-sided deficit δ₂/2. The test is δ₂>169ε/32; an extra p-bit
payment made before intersection changes it to δ₂>169ε/32+2p/P. The
**intersection code** must satisfy the class premise: intersecting transported
codes does not preserve every encoder or decoder restriction.

The unrestricted consumers are Lean-verified:
[`wholeRow_window_bound_excludes`](../RowSpreadCrux.lean) and
[`twoSidedWholeRow_window_bound_excludes`](../TwoSidedCodeTransfer.lean).
For a restricted class, the table describes the additional input needed at
the cardinality step of that proof; it does not assert a separately formalized
class-extraction theorem. With no further payment, half rate needs ε<32/169
on the one-sided route, or ε<16/169 on the two-sided route. Two-thirds rate
needs ε<64/507. The window W must be the one obtained from this same ε.

There is a stronger quantifier for a **native Crux** theorem. It bounds
arbitrary index codes on every cone system of the specified class. Its
raw-boundary argument, at fixed old depth D, pays 105ηP/64 and uses
rowSpreadWindow(k,rawConeSize(k,D),D,C,η). To obtain a restricted-class
Crux, the class property must hold for those arbitrary raw-conditioned
index-code fibres. A property only of the actual machine's correct fibres
gives a conditional machine-class exclusion, not this full Crux statement.
See [`native_indexCode_bound_of_wholeRow`](../RowSpreadCrux.lean).

## Class-to-machine table

In every row, the missing extraction premise is: **the counted native fibres,
after the stated payments, have this property uniformly at the required W and
canonical growing entry alphabet.** The table does not prove that premise.
“Half” means rate at most 1/2+o(1). Scalar-coordinate counts N are d² for
whole entries or d²b for individual lanes; entropy must be normalized by
the corresponding alphabet capacity. A fixed-field scalar result is not
automatically a theorem about arbitrary coupled b-bit entries.

| Additional property of the fibres, relation or decoder | Proved bound and exact scope | Source / status |
|---|---|---|
| Outside a fixed exceptional-coordinate tuple Z, each coordinate is determined by one other row, with that choice fixed on the fibre. | `2H(X)≤Σ H(row)+H(Z)`. Half if the exceptional entropy is o(N). A further general common record Q adds `2H(Q)` to this inequality. Nonlinear, all finite alphabets. | [Row spread §18.3](row-spread-of-cones.md#18-signed-row-synergy-and-recovery-budgets); [conditional separator discussion](window-pages-and-input-attachments.md#2-a-sufficient-row-separator-bound). Written. |
| Injective full independent-source encoder; each helper union resolves every source it touches; nonnegative column weights cover each row with total weight one. | `2K≤N+L+N₃`, with loop mass L and distance-three mass N₃. Half when `L+N₃=o(N)`. Saturation and balanced weights are extra assumptions, even for nonlinear encoders. | [Row spread §21.3](row-spread-of-cones.md#21-token-blocks-accounting-and-bounds-for-fundamental-presentations). Written. |
| Injective full independent-source encoder over the same finite source/output alphabet; essential support per coordinate at most fixed a. | At most two essential sources per coordinate: **rate≤2/3+o(1)**. Mean support≤μ<3: **rate≤(1+μ)/4+o(1)**. Fixed forward window suffices; no reverse-degree bound. Uniform over alphabets and nonlinear functions. These are not half bounds. The internal source-freezing bill is included. | [Sparse encoders §§1–4](sparse-encoder-cores.md). Written. |
| Fundamental transversal presentation, or the separately specified systematic nonlinear source-block presentation; two raw rows share at most λ helper columns. | `(λ+2)K≤(λ+1)N+L`. At λ=1, `2K≤N+L+N₃` gives half if near mass is o(N); the coarser bound gives two-thirds. A conditioning step must preserve the required presentation, or pay for a proved replacement. | [Row spread §§21.6–21.9](row-spread-of-cones.md). Written. |
| The bipartite **row-helper graph** has a separator deleting z ports and leaving components of at most K ports. | `log_q(card C)≤(d²+dz+Kd/2)/2`; the source has the sharper exact component sum. Half for z=o(d), K=o(d), or uniform row hyperfiniteness. All alphabets, nonlinear recovery. Work-window planarity alone is insufficient; input attachments remain. | [Row separator theorem](window-pages-and-input-attachments.md#2-a-sufficient-row-separator-bound). Written, reusing Paper 5. |
| A group row relation of bounded window, with commuting probability bounded below; or marked finite quotients of one fixed finitely generated amenable group. | Half through row hyperfiniteness. All alphabets and directed, nonlinear recovery. Fixed marking/generator and uniformity conditions matter; no arbitrary expanding-group conclusion. | [Near-abelian branch](bounded-sector-coupling.md); [amenable sources §4](symmetry-and-locality.md). Written. |
| The actual recovery support has components of size s=o(log d), or the code is an independent product on blocks of that size, in a balanced fixed-window grid. | Half, uniformly in alphabet and lane count. The finite error is `w/[2(R+1)]+Σ_(j<2s)max(2,w,R)^j/(2d)`; take the limits in the stated order. This concerns actual support, not the dense whole-row completion. | [Grid component bound §§2–3](grid-labellings-and-amplified-codes.md). Written. |
| Group host with fixed w; recovery uses mutually available helpers, and each connected cell component meets at most fixed m displacement sectors. | Exponent at most `d²/2+O_(w,m)(d²/log d)`. If B_m cells lie in larger components, add `B_m/2`. Nonlinear, all alphabets, correlations allowed. One-way helpers are not covered. | [Bounded-sector theorem](bounded-sector-coupling.md). Written; group identities in [SectorWalks.lean](../SectorWalks.lean). |
| Scalar affine linear decoder with one common triangularizable block side; complete flags include commuting blocks. | `D≤(d²+Σ s_j²)/2` for the compatible flag blocks. A complete flag gives `d(d+1)/2`. Every field. The physical one-class line/Toeplitz cases have their own proved hypotheses. | [Paper 17, order and symmetry](../../Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/paper/sections/order.tex); [row spread §31](row-spread-of-cones.md#31-shift-covariance-existing-bounds-and-the-native-gap). |
| At most two shared Kronecker terms; the specified three-term standard-seed assemblies; or a fixed-size identity-lift seed with the allowed basis changes and a rank-o(d²) perturbation. | Half. Finite bounds are pairing, pairing+3, and `d²/2+O_s(d)+rank perturbation`, respectively. Every field. This does not cover arbitrary three-term or arbitrary bounded-term decoders. | [Two terms](two-term-equality.md), [seed assemblies](three-term-seed-assemblies.md), [identity lifts](identity-lift-comparison.md). Written / earlier results as cited. |
| Group scalar linear decoder with growing twisted symmetry subgroup H, or a common unital factor algebra of dimension c=o(d²). Includes the precisely defined anonymous fixed-radius local rules and sparse Bruhat profiles. | Bounds `D≤d²/2+d²/(2√card H)` and `D≤(d²+d√c)/2`. Locality/Bruhat applications have their stated perturbation payments. All fields. Code symmetry alone is not decoder symmetry; vertex IDs violate the anonymous-local premise. | [Symmetry and locality §§1,3,6](symmetry-and-locality.md). Written. |
| The audited 18-parameter balanced split/nonsplit SL₂ decoder profile. | **Rate≤3/4**, every field including characteristic two. This is a useful constant deficit, not half, and not a theorem about arbitrary sector-dependent coefficients. | [Symmetry and locality §6](symmetry-and-locality.md). Written. |
| Bounded analytic tensor weight; contracting recovery with sublinear trace; or an injective sign-changing intertwiner with distinct paired eigenvalues. | Half under the precise stated premises. Weight/contraction use ℝ/ℂ or a compatible embedding; contraction alone does not remove its trace term. At eigenvalue 1, sign symmetry needs characteristic≠2; actual bipartite support has an all-field proof. | [A, bounded weight](../A-bounded-weight.md), [B, recovery matrices](../B-recovery-matrix.md). Lean, with field scopes there. |
| Fixed affine helper family with an appropriate parity character, bounded complex coefficients, and dimensions tending through primes. | Half on that subsequence. Closed-walk small-coefficient bounds have separate limiting-growth hypotheses, sometimes giving zero rate instead. A finite-prime census is not a limiting estimate. | [Pass calculus §5](pass-calculus.md). Written. |
| A general scalar linear decoder has the required frontier-rank or local-invertibility certificates in a chosen row order. | C1/C2 give sums of local dimension bounds. **They do not by themselves give half rate.** The sum must be at most `(1−δ)d²` to pass the invoice. | [Second-rule formulas](../C-second-rule.md). Lean. |
| A basis-hypercube host with a fixed independent set of w generators. | Every code has exponent at most `d²/2+2^(w−2)d`. All finite alphabets. The displayed folded-cube codes are lower-bound calibrations; they are not additional universal exclusions. | [Diagonal calibration §3](diagonal-code-calibration.md); Paper 17's whole-row order theorem. Written. |
| A balanced coarse Fano layout with at least γd good columns; or a sparse incidence lift respecting a fixed finite base of side s with Shannon bound U<s². | Fano gives deficit `4γ/21`; the base lift has rate at most `U/s²`. Nonlinear, all alphabets, generally not half. A coarse layout or quotient must actually be supplied; B1 does not supply it. | [Paid coarse patterns](paid-coarse-patterns.md), [finite-gap amplification](finite-shannon-gap-amplification.md). Written; finite Fano formal status is listed in the consolidation index. |

For the linear rows, an explicit scalar realization is enough: if q entry
symbols embed injectively in a field F and a fibre lies in an affine
F-subspace of dimension D, an information-set projection gives at most q^D
words. The fibre need not be the whole subspace. This also permits F=ℂ,
but only with the actual scalar decoder and any norm bounds uniform in the
growing alphabet. Binary vector-linearity does not imply scalar
F_(2^b)-linearity. A theorem about a nonlinear decoder on a linear source
needs that source premise; the affine-kernel observation does not replace it.

## What remains, and what the barriers leave open

The table is a list of exact conditional exclusions, not a measure or density
on the universe of machines. No additional native extraction theorem is proved
here. In particular, B1 does not force separators, symmetry, a sparse independent
encoder, bounded sector coupling, or any listed field representation.

The assigned-rule theorem excludes improving the optimal acyclic certificate
by merely combining displayed recovery rules with unit coordinate prices and
additive message bills. The rectangle theorem supplies a further quantitative
limit on mixing hosts. Neither theorem excludes additional entropy inequalities,
native extraction of a larger acyclic set, or a genuinely cheaper joint message.

There is also a fourth logical possibility: **correctness forces a source or
decoder restriction with an algebraic or source-counting bound** from the table.
For example, a paid full-cube two-source encoder extraction would have the
existing two-thirds theorem as its consumer. Sparse recovery and cheap circuits
alone do not give such an extraction. This identifies an opening left by the
barriers, not a new premise, experiment, or research front.

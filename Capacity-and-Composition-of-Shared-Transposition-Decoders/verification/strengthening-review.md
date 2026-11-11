# Bounded strengthening review

This review examines one concrete extension of the complete-map composition
results. The uniform argument is symbolic and is now verified in Lean. It is
not a parameter search or a native tape experiment. Independent reviews of the
final manuscript are recorded separately.

The tested family is the binary masked neighbor map
`L_m = I + diag(m) T`, acting separately on every row and lane, surrounded
by arbitrary column-equivariant maps before the final shared rule. The final
rule is permitted arbitrary nonlinear functions and arbitrary lane mixing.
All factors have the same complete finite domain; no initialized workspace
or donated intermediate encoding is supplied.

The review establishes the following uniform extension. If exactly one mask
entry is one, so the word map is `I + E_(0,1)` after a rotation, then no exact
factorization `transpose = K B L_m H` exists with at most two final receiver
classes, for any `d >= 3` and any positive width. Here `B` and `H` are total
column-equivariant maps. The proof is in the single-site appendix.

Its added ingredient is an exact group calculation. Conjugating the adjacent
pair by `L_m` yields the cyclic shift and
`A = U_1 U_0 U_(-1) U_0`, where `U_i = I + E_(i,i+1)`. For `d >= 4`, squaring
`A` supplies all translated step-three transvections. At `d >= 5`, conjugating
one such transvection by `A` also supplies step four. Cyclic commutator
chains supply reverse step three; combining it with step four supplies step
one and then all elementary transvections. These act transitively on nonzero
words.
The coincident-index case `d = 3` is checked by its explicit seven-element
orbit, and `d = 4` by the step-three cycle. The balance theorem forbids
adjacent equal receiver classes. The period theorem rules out the remaining
alternating partition at even `d`.

The prior anchored-difference theorem covers masks with exactly one zero.
Together these are two uniform endpoint families, not a theorem about every
mask. For a general mask with at least one zero, the inverse is the finite
geometric sum of the nilpotent weighted shift. A nontrivial period of the mask
is handled by the periodic-first-factor class count; with two final classes,
this leaves only aperiodic masks and possible half-period masks. The forced
fixed-image period constraint remains necessary but does not by itself settle
those remaining cases.

No additional mask census, solver query, timing run, native construction,
capacity-fraction estimate, or error-density theorem was performed or inferred.
The extension uses the exact same complete-map, same-tensor-side interface as
the manuscript's balance and period theorems. It does not allow an arbitrary
equivariant postprocessor after the final shared map.

The complete endpoint is Lean-verified in
`SharedDecoders.CompositionSingleSiteEndpoint.single_at_most_two_classes_impossible`.
It derives the actual single-site group action, step-three and step-four
transvections, cyclic generation, complete-state balance, and final period
contradiction. It assumes no external transitivity or group-generation
certificate. The dimension-three orbit is an ordinary kernel `decide +kernel`
proof over the eight scalar words; no `native_decide` or external evaluation
axiom is used. The theorem allows arbitrary nonlinear surrounding maps and
arbitrary mixing between lanes, for every positive width and every dimension
at least three.

The anchored-difference endpoint is also fully Lean-verified in
`SharedDecoders.CompositionAnchoredEndpoint.anchored_at_most_two_classes_impossible`.
Both endpoints use only the standard Lean axioms `propext`, `Classical.choice`,
and `Quot.sound`. The final independent
[English–Lean review](english-lean-review.md) and
[proof/citation review](proof-citation-review.md) both examined this endpoint
and found no unresolved substantive issue within its stated hypotheses.

# Independent slab-geometry review

Reviewed 10 November 2026, after the author declared the module and lemma
stable. This is an independent source and proof-interface review of
`lean/AdaptiveTransfer/SlabGeometry.lean` against `lem:slab-geometry` in
`paper/sections/returns.tex`, with the model and replay definitions needed
to interpret that lemma. It does not extend the scope of the earlier review
to the rest of Paper A.

Reviewed SHA-256 values:

- `lean/AdaptiveTransfer/SlabGeometry.lean`:
  `4995f3d9b6d23d0b75101f6ae9fddf153f61b84a7fea8f5ed5a4eeb1208b204f`
- `paper/sections/returns.tex`:
  `3fe0f11cf8c01f401a8bc03d700ad1732f7603b305c318211f5a9fa545e679ad`

No defect was found in this scope. Both `exists_slab_geometry` and
`native_slab_geometry` establish the advertised conclusion rather than
assuming a chunk with the desired properties.

The checked assumptions are `d,b ≥ 1`, `P=d²b ≥ 2`, and real parameters
`a,c ≥ 1`. The finite theorem takes two unit walks, strictly increasing
append times for all `P` output ordinals, and `T ≤ 2cP`. It constructs
integers `ell,s,e` with `0 ≤ s ≤ e ≤ T` and the literal chunk
`{t ∈ [s,e) : ell ≤ y(t) < ell+W}`. Natural division gives the advertised
`floor(P/2)` size bound; `runStarts` counts its maximal nonempty runs.

The constants agree exactly: `W=ceil(P/(80ac))` and
`N=floor(160ac²)+1`. Offset averaging gives at most `N−1` walls and hence
at most `N` runs. In the short case, the outer interval starts at zero,
so `P/(2N)` outputs and the stripe bound give a saving of at least
`P/(4N)−3Ndb` without a snapshot charge. In the long case,
`floor(P/2) ≥ P/3` and the runtime bound give more than `P/(24c)` outputs.
After the stripe bound and `aW ≤ P/(80c)+a`, the margin is greater than
`P/(120c)−3Ndb−a`, which implies the required
`P/(4N)−3Ndb−a`. The snapshot expression is zero exactly when `s=0`,
matching the manuscript's indicator `iota`.

I checked the imported offset, chunk-dichotomy and stripe theorem interfaces,
and the definitions of `outIn`, `inCells`, `runStarts` and `tposOf`.
`omittedSlabBits` is exactly the demanded raw set `pi(O) \ I`; it excludes
public endmarker positions and uses the actual transpose permutation.

The native endpoint takes one `TransposesInput M d b c X` hypothesis and
a chosen `f : Fin M.k`. It fixes the trace to `trace M (List.ofFn X)`.
Membership in that trace's fibre is proved by reflexivity, so use of
`fibre_haltTime` introduces no shared-trace premise. That theorem supplies
the actual halting-time bound `floor(c(P+1))` and exactly `P` append events.
The valid ordinal bounds prevent the default branch of `appendTime` from
being used; strict monotonicity and append times below halt are derived.
The raw and work paths are the actual native head positions, via the
existing trace/run identities. No other input, obliviousness assumption,
preselected output set or supplied suitable-chunk certificate is required.

No Lean or manuscript source was edited in this review. The author reported
a warning-free targeted compile; I did not run a competing build or a new
axiom audit. Full package and generated-audit verification remain integration
checks. Formalizing this geometry lemma does not formalize the variable-message
replay injection or the later counting and asymptotic results whose status
lines remain distinct.

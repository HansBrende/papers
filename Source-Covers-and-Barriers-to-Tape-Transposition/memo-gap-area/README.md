# Frozen Gap Areas and the Sharpness of Source-Cover Certificates

**Hans Brende and Claude Opus 5.5 (Anthropic)**, October 2026.

An extension memo to *Source Covers and Barriers to Tape Transposition* by Hans Brende and
GPT-6 Astra (OpenAI), the paper in the parent directory.

- [PDF](paper/main.pdf) and [LaTeX sources](paper/), licensed under [CC BY 4.0](paper/LICENSE).
- [Lean library](lean/), licensed under [Apache 2.0](lean/LICENSE). It requires the parent
  paper's library through the relative path `../../lean` and copies nothing from it.

## The question

Does one deterministic multitape Turing machine transpose every square matrix with dimension `d`
and entry width `b(d) = max(1, ceil(log₂ d))` in time `O(L)`, where `L = d² b(d)`? This is
question (T) of the series.

The source-cover paper fixes one complete computation geometry and a nonempty correctness set,
and bounds the correctness deficit below by a geometric credit minus a revelation cost. The
credit is at most the circular point-gap area of the complete raw-source bank, frozen at the
first output time of each column. For two exceptional families the paper names the
inverse-square hop profiles as the nearest unresolved case. This memo takes the frozen gap area
itself as the certificate, applies it to two classes of geometries, and shows where it stops.

## What is proved

**All numbered results and definitions are formalized in Lean.** Every declaration cited in the
memo depends at most on `propext`, `Classical.choice` and `Quot.sound`. The Lean statements are
authoritative; the outlines in the PDF explain the proofs.

- **Theorem G (frozen gap area).** Along every joint profile of every near-full sequence, the
  limiting mean frozen point area over legal phases and columns, with the first `R` core
  families protected and modulus `M`, is at most `β τ_R / (M − R)`, where `τ_R` is the limiting
  hop tail. The number of exceptional families is arbitrary.
- **Theorem A (funnels).** In no near-full sequence do infinitely many geometries have funnels of
  a fixed depth over raw intervals of a fixed positive relative length: chains of time sets, each
  fed by at most one family and only from the next set, ending in a set fed by none. No envelope
  on the core sizes is assumed.
- **Theorem B (single-sweep terminal landings).** No near-full sequence consists of geometries
  with two designated families, an older one `e` and a newer one `g`, among which are all the
  exceptional families, whose input head is constant on the lower regions of the core families
  and of `g` and at the column roots, and sweeps once, nondecreasingly, on the lower region of
  `e`, while no core family and not `g` act there. No envelope is assumed.
- **Theorem Z (sharpness for two exceptional families).** An explicit sequence of admissible
  geometries with two exceptional families and hop counts `|G_i| ≤ 512 L / i²`, the boundary case
  of the parent paper's power envelopes, has, in every hop order, at every protected prefix
  `J ≥ R` and at every modulus `M > R`, mean frozen point area over legal phases and columns at
  most `10⁷ / R²`, and hop tail after `R` at least `1 / (32 R)`. Hence the necessary condition of
  Theorem G holds on it whenever `3.2·10⁸ (M − R) ≤ β R`, for instance at `M = 2R + 2` for every
  capacity constant `β ≥ 10⁹`: in the finite form of Theorem Z(c) and along every joint profile.
  So Theorem G at these moduli cannot exclude the two-exception inverse-square class. The
  geometries carry a single input and are not near-full; the certificate does not involve the
  correctness sets.

Not formalized: the comparison of Theorem G with the parent paper's reciprocal-cover bound (a
remark with a proof sketch), and a few elementary consequences stated in prose and labelled in
the PDF.

## What is open

- Whether Theorem G at larger moduli (relative to `R`), or the parent paper's necessary
  complete-observable movement and global continuation density, exclude the two-exception
  inverse-square class.
- Whether transposition-specific constraints on the work heads exclude admissible two-exception
  geometries that have no bounded-depth funnels and are not single-sweep terminal-landing
  geometries.

These are certificates for specified geometries, not a decision of (T).

## Building and verifying

Readers need the whole repository, with sibling directories in place. The Lean package uses
the parent paper's library and, through it, the libraries of the second, fourth and eighth papers
and the shared `lean-machine` library. Fetch the second paper's pinned external dependency as
described in its [README](../../Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/README.md).
Then, in `lean/`:

```sh
lake exe cache get
lake build
lake env lean MemoAxioms.lean
```

The cache command is needed only when the pinned dependency objects are not already available.
The last command prints the axioms of every declaration the memo cites.

The index of Lean declarations in the PDF and `lean/MemoAxioms.lean` are generated from the
LaTeX sources. From this directory:

```sh
python3 tools/lean_index.py
python3 tools/lean_index.py --check
```

Build the PDF in `paper/` with `latexmk -pdf -interaction=nonstopmode main.tex`.

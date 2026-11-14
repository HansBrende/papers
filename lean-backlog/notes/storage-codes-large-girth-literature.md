# Storage codes at large girth: what the literature has, and the degree-three twin of our open case

Status: literature survey by Claude Fable (through a web-search subagent, abstracts and HTML pages
only; no paper was read in full), 14 November 2026. Tags: [H] read on an abstract or HTML page,
[S] search snippet only, [I] my inference. Statements tagged [S] or [I] must be checked against the
papers before any use. Section 3 is mine and unreviewed.

A *storage code* on a graph is a set of words in which every coordinate is a function of its
neighbours' coordinates (guessing games, index coding with symmetric side information). Pairing on a
perfect matching gives rate 1/2; the linear capacity is n minus the minimum rank of a matrix with
nonzero diagonal supported on the edges. The abstract twin of a whole-row host of window w is a graph
of degree w.

## 1. Findings

**No theorem, conjecture or refutation was found for "bounded degree and girth → ∞ implies capacity
n/2 + o(n)".**

- *Degree two.* Odd cycles have capacity n/2 (Christofides–Markström, EJC 2011 [S];
  Blasiak–Kleinberg–Lubetzky, arXiv:1004.1379 [S]; exact values in Atkins–Rombach–Skerman,
  arXiv:1602.03586 [S]).
- *Triangle-free is not enough.* Cameron–Dang–Riis, arXiv:1410.2405 [H]: Clebsch (degree 5, girth 4)
  has 10 ≤ capacity ≤ 11 of 16; Hoffman–Singleton (degree 7, girth 5) has capacity ≥ 29 of 50 by a
  linear code over F₅; Higman–Sims ≥ 77 of 100. The conjecture that the clique-cover value is exact
  for triangle-free graphs is therefore false. Families with rate → 1 on triangle-free graphs
  (Barg–Zémor arXiv:2110.02378; Barg–Schwartz–Yohananov arXiv:2212.12117; Huang–Xiang
  arXiv:2301.01668) [H] all have growing degree, and are Cayley graphs of F₂^r [I], so contain
  four-cycles.
- *Large odd girth is not enough.* Golovnev–Haviv, arXiv:2002.08580 [H]: for every odd ℓ there are
  graphs with no odd cycle of length ≤ ℓ and minrank n^{1−δ} over every finite field.
- *Four-cycle-free gives a linear bound over ℝ only.* Codenotti–Pudlák–Resta, TCS 2000 [H, via
  Haviv arXiv:1806.00638]: C₄-free graphs have real minrank above n/6; triangle-free graphs with
  minrank O(n^{3/4}) exist.
- *Small graphs.* Baber–Christofides–Dang–Riis–Vaughan, arXiv:1410.8349 [H]: a floating-point search
  found the Shannon bound equal to the clique-cover value on all graphs with at most 10 vertices
  except two. For triangle-free graphs the clique-cover value is the fractional matching number, at
  most n/2 [I]; so Petersen has capacity 5 although n − α = 6 [I].
- *Entropy arguments beyond n − α.* Mazumdar–McGregor–Vorotnikova, arXiv:1706.09197 [H], for all
  alphabets and nonlinear codes: if V = X ⊔ Y with both induced graphs bipartite and both boundary
  sets independent, capacity ≤ n/2; a cycle with chords whose ends are at least four apart has
  capacity n/2.
- *Zero forcing.* No use of it for index or storage codes was found. For matrices whose off-diagonal
  support is exactly a graph G the nullity is at most Z(G); Z ≤ ((Δ−2)n+2)/(Δ−1) for connected
  graphs (Amos et al.) [S]; Z ≤ n/2 for connected cubic graphs other than K₄ and K₃,₃
  (Gentner–Rautenbach; Brešar–Brezovnik arXiv:2010.00637) [H]; random cubic graphs have
  0.070n ≤ Z ≤ 0.171n (Bal et al., arXiv:1812.06477) [H].
- *Product structure.* Nothing on the swapped tensor square (p,c) ~ (q,m) iff q ~ c and m ~ p.
  Nearest: Cameron–Dang–Riis's blow-up lemma gn(G(t), s) = t·gn(G, s^t) [H].

## 2. What this says about our open case

- The abstract problem at degree three is open in both directions, like R(3). The known examples
  above one half need degree at least five.
- Any proof for arrays that would also apply to abstract graphs of degree five or seven and girth at
  most five is wrong. A proof may use degree three, large girth, or the array structure.
- The cubic window is n/2 ≤ capacity ≤ n − α ≤ 0.555n at large girth [I], against 1/2 and 3/4 for
  arrays: the array question is much wider open than its abstract twin.

## 3. A target that the closure barriers do not cover (mine)

For **linear** codes there is a rule beyond closure: in the system (I − M)x = 0 an equation with
exactly one unknown determines it. So the nullity is at most the forcing number of the support
pattern, with both rules. The assigned-rule theorem bounds closure alone.

**Target A (abstract, linear).** Let B have nonzero diagonal and let its off-diagonal support graph be
triangle-free of maximum degree three. Then nullity(B) ≤ n/2.
Known pieces: bipartite graphs (n − α); exact symmetric cubic patterns (Z ≤ n/2); perfect matchings
attain n/2; with support one the statement is immediate (each class of proportional coordinates has
at least two members). Open: directed and partial supports on non-bipartite graphs.

**Target B (abstract, nonlinear).** Triangle-free graphs of maximum degree three have storage
capacity at most n/2. This is the degree-three twin of R(3) = 1/2. Evidence: every graph with at
most ten vertices (floating point), odd cycles, the chord families.

**Target C (arrays).** The same with cells as vertices, for decoders whose support has at most three
cells. This is the shape of a native bit cone of size three, and it would be a
correctness-independent bound for a class of linear schedules.

A counterexample to A would be a linear code above one half with no triangles at degree three, which
is exactly the mechanism a construction would need.

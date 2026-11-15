# Literature leads for the Matrix Coding Conjecture (15 November 2026)

Status: notes from the literature pass run before publishing paper 21, updated the same day after
nine papers were obtained and read. Kept by Claude Fable. Each item says **how it was read**.
"Checked" means I read the passage in the paper's text myself. "Reader" means an independent reading
agent's report on the full text, which I did not re-read line by line. Nothing here is a result
unless it points to paper 21.

## 1. The question exists at growing windows, and is false there

- **Mittal and Raz (ITCS 2021), Section 8.1, Conjecture 36; Theorems 3 and 29.** The transpose is
  conjectured to be (c d², c d)-block-rigid: no set of 2^((1−c)d²) matrices of bits has every
  column a function of c·d rows. That is a whole-row deficit c at window c·d. Theorem 29 (block
  rigidity excludes linear-time multitape machines with advice, by the cut of Paul, Pippenger,
  Szemerédi and Trotter) would turn it into a lower bound. *Checked* in the paper.
- **Braverman and Forbes, in Mittal's dissertation (Princeton 2025), Proposition 10.8.3, Lemma
  10.8.5.** False: F₂-linear whole-row codes of codimension d^(1+ε) at window d^(1−α). *Checked.*
- **Alon, Moitra and Sudakov (JEMS 2013), Lemma 2.13 and Theorem 2.21.** A graph on d vertices
  (words; edges between words agreeing in few positions) missing at most d^(3/2+ε) edges, with
  equal missing degrees, partitioned into d^(2−cε³) induced matchings. In our terms: rate tending
  to one already at window about d^(1/2+ε). *Checked* (statement and the degree count); the
  translation is in paper 21's remark on growing windows.
- **Their limits, Section 3.** Theorem 3.9: a bipartite graph covered by disjoint induced
  matchings of one size r ≥ 3 misses at least Ω(r^(2/3)·(|U||V|)^(2/3)) pairs; in our terms
  w ≥ Ω(r^(2/3) d^(1/3)). Proof sketched there. Theorem 3.12 is the non-bipartite degree form.
  *Checked* (statements).
- **Paper 21, Proposition "Parities over induced matchings"** (written, not Lean, sent for
  review): for any partition into induced matchings of mixed sizes, all but (w² + 3w/2)·d^(3/2)
  entries lie in matchings of at most two entries, so such codes have rate 1/2 + O(w² d^(−1/2)).
  So the refuting mechanism gives exactly the pairing rate at a fixed window.
- **Consequences.**
  - **Every proof attempt has a free test: it must fail at window d^(1/2+ε).** An argument that
    never uses the size of the window is wrong.
  - For parity codes over induced matchings the threshold is between d^(1/4) (our proposition;
    d^(1/3) for equal sizes by Theorem 3.9) and d^(1/2+ε). For arbitrary codes nothing is known
    between bounded windows and d^(1/2+ε). This is the new open problem of paper 21.
  - **Lead (the natural next class).** Linear codes whose checks are not mutual: a check recovers
    one entry (i, j) from entries in rows ρ(j), and those entries need not be recovered by the same
    check. The path count of the proposition uses mutuality three times. Which part survives for
    checks of bounded support? Checks of unbounded support in one column are the first case it
    cannot see.

## 2. Coded caching: the same objects

- **Dictionary** (second paper of the series; Yan, Cheng, Tang and Chen): users are columns,
  packets are rows, user j caches packet i of every file when i ∈ ρ(j), user j wants file j. A
  linear delivery of S symbols is a linear whole-row code of codimension S; subpacketization equals
  the number of users, and every user caches w packets per file. Coding gain ≈ 1/(1 − rate). The
  conjecture says: bounded gain, however large w is.
- **Wan, Tuninetti and Piantanida (arXiv 2001.04810), Theorem 2, Lemma 1, the "acyclic IC
  bound".** For one placement, one demand vector and one order of the users, the load is at least
  the number of packets of each user's file cached by none of the users before it. This is our
  bound from acyclic sets. *Checked* for the displayed bound; the reader confirms it is stated per
  instance, before averaging. They call it looser than the full submodularity bound; no example of
  a fixed placement where it is strict was found by the reader.
- **Shangguan, Zhang and Ge (arXiv 1608.03989).** *Reader.* Lower bounds only for placement
  delivery arrays, and only when load and memory ratio are both constants (their Theorem III.3):
  not our regime, where the memory ratio is w/d. Constant number of cached packets with linear
  subpacketization is not treated. Open there: whether polynomial subpacketization suffices.
- **Shanmugam, Ji, Tulino, Llorca and Dimakis (arXiv 1508.05175).** *Reader.* Their converse
  (Theorem 6) is for random placement with clique-cover delivery: gain 4g/3 needs
  F ≥ (g/(2et))·(N/M)^(g−2). They say a lower bound for deterministic placement "is not known".
  Paper 21's proposition is such a bound in one corner (deterministic placement, delivery by
  induced matchings, as many packets as users, bounded cache). No claim of novelty is made for it.
- Nothing in these papers bounds arbitrary or nonlinear delivery at a fixed window beyond the
  acyclic bound.

## 3. Entropy tools

- **Shearer-type inequality for random bijections** (Dinur, Keller and Marmor, arXiv 2505.00894,
  Theorem 1.8; Barthe, Cordero-Erausquin, Ledoux and Maurey, arXiv 0907.2858, Proposition 20 in
  the arXiv version). *Reader.* For sets covering each point at most k times,
  2k·D(P‖Q) ≥ Σ D(P_U‖Q_U) when Q is uniform on bijections. Assessment (the reader's and mine): it
  is a Shannon-type inequality, so it cannot beat the polymatroid bound, and the direct
  application to "rows ρ(j) and column j" returns about w/(w+1). **Low.**
- **Riis, "Term Coding" (arXiv 2601.16614).** *Reader.* Our system is already in its normal form
  with one function symbol per equation, so its Proposition 5.8 gives the number of solutions as
  the guessing number of the cell digraph for every alphabet, exactly; the sandwich theorem adds
  nothing. Usable facts on alphabets: monotonicity and supermultiplicativity (Proposition 5.5) and
  gn(n) ≥ (t/(t+1))·gn(q) for t = ⌊log_q n⌋ (Theorem 5.6). Rates of convergence are open there.
- **Gadouleau and Riis (arXiv 1010.2619), Proposition 10.** *Reader.* If every row is a function
  of whole rows (no transpose), the problem is a guessing game on d vertices over the alphabet of
  rows. The transpose is exactly what that reduction does not cover. Their upper bounds are the
  acyclic bound and a girth bound that is trivial here.
- **Lexicographic products** (Blasiak, Kleinberg and Lubetzky; cited in the series): the cell
  relation is not such a product, and tensoring helper maps multiplies windows. **Low.**

## 4. Cautions

- Half-rate conjectures have failed before: Valiant-type shift conjectures (Riis 2007) and one
  half on triangle-free graphs (Barg and Zémor; Golovnev and Haviv; Huang and Xiang; papers 13 and
  15 of the series). *Abstracts only* for the outside papers. Those codes are linear on Cayley or
  coset graphs; whether they can have whole rows as helper sets is an open problem of paper 21.
- The linear case (minimum rank over the support pattern of the swap) is the subject of the
  synthesis paper; small-size computations have been done there.

## 5. Not checked

Works citing Mittal and Raz: eight are listed by a citation index (November 2026), all on parallel
repetition by their titles; not read. Dissertations of Dang, Shanmugam, Arbabjolfaei, Freksen,
Kamma and Dvořák. Stoß 1973 and Kirchherr 1988. Regenerating, batch and PIR codes as possible
counterexample patterns. Exchangeable-array and graphon entropy methods.

# Literature leads for the Matrix Coding Conjecture (15 November 2026)

Status: notes from the literature pass run before publishing paper 21. Kept by Claude Fable. Each
item says **how it was read** and whether the series already uses it. Nothing here is a result.
"Reader" means the independent search agent of that pass, which read abstracts and summarised HTML
pages and opened no PDF. "Checked" means I read the text myself.

## 1. The main finding: the question exists at growing windows, and is false there

- **Mittal and Raz (ITCS 2021), Section 8.1, Conjecture 36; Theorem 29.** The transpose is
  conjectured to be (c d², c d)-block-rigid: no set of 2^((1−c)d²) matrices of bits has every
  column a function of c·d rows. That is a whole-row deficit c at window c·d. Their Theorem 29
  (block rigidity excludes linear-time multitape machines, even with advice, through the cut of
  Paul, Pippenger, Szemerédi and Trotter) would turn it into a lower bound. *Read:* the
  dissertation's restatement (Question 10.8.2, Definition 10.3.7, Theorem 10.1.3), checked; the
  2021 paper's numbering from the reader and from the second paper of this series.
- **Braverman and Forbes, in Mittal's dissertation (Princeton 2025), Proposition 10.8.3 and Lemma
  10.8.5.** The conjecture is false: for every ε > 0 there is α > 0 with, for infinitely many d,
  an F₂-linear whole-row code of codimension d^(1+ε) at window d^(1−α). Remark 10.8.6: random
  helper sets of twice the size also work, with weaker bounds. *Read:* checked.
- **Consequences for us.**
  - Paper 21's conjecture is the same question at a fixed window. The paper now says so (its
    remark on growing windows, the related-work paragraph, and a new open problem).
  - **Every proof attempt has a free test: it must fail at window d^(1−α).** An argument that
    never uses the size of the window is wrong. The order bound w/(w+1) passes the test (it is
    vacuous there). So does any valid Shannon bound. Heuristic arguments should be run through it
    first.
  - The refuting codes are sums of parities over induced matchings of the bipartite graph of
    non-incident cells. An induced matching with r edges needs r − 1 ≤ w, so at a fixed window
    only matchings of bounded size exist; size two is the pairing code. This is the class of
    "clique-cover" codes for which the backlog has a written, unreviewed bound (mutual triangles
    cover o(d²) cells when w = o(d^(1/3)); see the note on triangle-free hosts). **Lead:** state and prove the class theorem "parity codes over induced
    matchings have rate 1/2 + o(1) at every fixed window", with the window growth at which it
    stops. It would locate the threshold of the new open problem for this class.

## 2. Coded caching: the same objects, with their own converse literature

- **Dictionary (second paper of the series; Yan, Cheng, Tang and Chen 2017; Shanmugam, Tulino and
  Dimakis 2017).** Columns are users, rows are packets, "user j caches packet i of every file"
  means i ∈ ρ(j), and a delivery of S coded symbols for the demand "user j wants file j" is a
  linear whole-row code of codimension S. Subpacketization equals the number of users (F = K = d)
  and each user caches w packets of every file. *Read:* the series' second paper, checked; the two
  caching papers were read for that paper, not again now.
- **Lead: converses under limited subpacketization.** In this language the conjecture says: with
  linear subpacketization and w cached packets per file, the coding gain is bounded by an absolute
  constant however large w is. The coded-caching literature has lower bounds on subpacketization
  for a given gain (for placement delivery arrays, by hypergraph Turán arguments: Shangguan, Zhang
  and Ge) and finite-length converses (Shanmugam, Ji, Tulino, Llorca and Dimakis). *Not read in
  this pass.* Two things to check: whether any of them covers arbitrary linear or nonlinear
  delivery (they are usually for restricted delivery), and whether the standard converse for
  uncoded placement is our order bound w/(w+1) under the dictionary (I expect so: both are
  acyclic-set arguments).

## 3. Entropy tools not yet used in the series

- **Shearer-type inequality for permutations** (Barthe, Cordero-Erausquin, Ledoux and Maurey 2011,
  as used by Dinur, Keller and Marmor, arXiv:2505.00894, for non-adaptive time-space bounds).
  *Read:* abstract, by the reader. An entropy inequality built for permuted coordinates; the swap
  of rows and columns is such a permutation. First step: write the entropy of a uniform codeword
  over the cover {rows ρ(j)} ∪ {column j} and see whether the permutation form gives anything
  below w/(w+1) at window three. By the test of Section 1 it must degrade as w grows.
- **Riis, "Term Coding" (arXiv:2601.16614).** *Read:* abstract, by the reader. A sandwich theorem:
  the number of solutions of a system of term equations is governed by a guessing number, with
  entropy upper bounds and Lean proofs. A whole-row code is such a system. Possible use: the
  passage between a fixed alphabet and the canonical growing alphabet, which is open in the
  synthesis paper (its Problem 9.4).
- **Lexicographic-product supermultiplicativity** (Blasiak, Kleinberg and Lubetzky 2011; the
  series already cites them). The cell relation is not a lexicographic product, and tensoring two
  helper maps multiplies the windows, so by Section 1 this amplifies deficits only into the regime
  where the conjecture can fail. I rate it low.

## 4. Cautions from the literature

- **Half-rate conjectures have failed before.** Riis (2007) refuted Valiant-type shift conjectures
  through guessing numbers; rate one half on triangle-free graphs was refuted by storage codes of
  rate tending to one (Barg and Zémor; Golovnev and Haviv; Huang and Xiang; in the series, papers
  13 and 15). *Read:* abstracts, by the reader; the series papers, checked. All those codes are
  linear and live on Cayley or coset graphs. Whether such codes can have whole rows as helper sets
  is already an open problem of paper 21.
- **Alignment converses** (Maleki, Cadambe and Jafar 2014) characterise index-coding rate one half
  per message, which corresponds to storage codes of codimension two: not our regime. Low.
- **The linear case** (minimum rank over the support pattern of the swap) is the subject of the
  synthesis paper and of much of this backlog. The reader's first suggestion, small-size minrank
  computations, has been done there.

## 5. Not checked

The 2021 Mittal–Raz paper itself (only the dissertation's restatement was read line by line);
works citing it (the citation service refused the reader's queries); the dissertations of Dang,
Shanmugam, Arbabjolfaei, Freksen, Kamma and Dvořák; Stoß 1973 and Kirchherr 1988; regenerating,
batch and PIR codes as possible counterexample patterns; exchangeable-array and graphon entropy
methods.

# Cone systems have the whole-row shape

Status (13 November 2026, Hans Brende and Claude Fable 5.2): Lemma 1, Proposition 2 and Corollary 3
have written proofs here, **not reviewed and not formalized**. They use the definitions of the
fourteenth paper ([Bounded-Stack DAGs](../../Bounded-Stack-DAGs-Reduce-to-Constant-Depth/), Definition of
depth-TCP and the crux, Corollary O). Front D4 of [the roadmap](../wall.md): this is a candidate for the
missing class property, and it would tie front D1 to the machines.

## The claim in one sentence

For every machine with k work tapes and every ε, a genie of cost at most 2εL leaves a cone system in
which, for all but εd output rows, the cones of **all** output bits of the row lie in at most w input
rows, with w depending on k, β, C and ε only. So every fibre is a ρ-code of window w in the sense of
paper 17, Problem 9.4(c), up to εd columns.

## Setting

A machine with k work tapes, value width at most β, an input of L = d²b bits read by a two-way head,
an append-only output, and a run of T ≤ C(L + 1) steps. An *input row* is one of the d blocks of db
consecutive input positions, an *output row* likewise. The dependency DAG has a state edge from every
step to the previous one and, for each work tape, an edge from a step to the last earlier visit of the
cell under that head. Γ is a set of revealed steps; the cone set of an output bit is the set of input
positions under the input head at the steps of the Γ-free paths from its append step.

Cut the time into N = ⌈T/(db)⌉ ≤ Cd + 1 *windows* of db consecutive steps.

## Lemma 1 (a window reads the leavings of three windows per tape, on average)

For one work tape and a window W_i, let m_i be the number of earlier windows W such that some cell
visited during W_i was last visited, before W_i began, during W. Then Σ_i m_i ≤ 3N.

*Proof.* At the beginning of W_i label every cell by the last window that visited it (or by "never").
The labels cut the tape into maximal blocks of equal label; let Φ_i be their number, so Φ_0 = 1. During
W_i the head visits a contiguous range of cells. The m_i labels in question belong to blocks that meet
this range. Afterwards the range is one block, the blocks inside it are gone, and at most two of the
blocks that met it survive as remainders, so Φ_{i+1} ≤ Φ_i − m_i + 3. Summing, Σ m_i ≤ 3N + Φ_0 − Φ_N ≤ 3N. ∎

This is the block structure of Hopcroft, Paul and Valiant, without making the machine block-respecting.
The only property of a tape that it uses is that a head visits a contiguous range in a window.

## Proposition 2 (row spread)

Let ε > 0, let Γ be any set of steps of full depth at most D (for instance the genie of Corollary O(a)
at ε), and put M = ⌈4k(k + 1)βC/ε⌉ and M′ = ⌈2C/ε⌉. For all large d there are a set Γ′ ⊇ Γ with
β·#(Γ′ ∖ Γ) ≤ εL and a set of at most εd output rows such that, for every other output row r, the cone
sets with respect to Γ′ of all output bits of row r lie in at most

  w = 3 (M′ + 1)(M + 2)^D

input rows.

*Proof.* Call a window *bad* if the numbers m_i of Lemma 1, summed over the k tapes, exceed M. By the
lemma there are at most 3kN/M bad windows. For every bad window add to Γ the step before it and, for
every step t of it and every tape, the last earlier visit of the cell under the head at t if that visit
lies before the window. That is at most k(db + 1) + 1 steps per bad window, so the added cost is at most
β · (3kN/M) · (k + 1)(db + 1) ≤ εL for large d. Adding steps does not increase the depth.

Every edge of the dependency DAG goes from a step to a step of the same window, of the window before
it, or (a tape edge) of one of the windows counted in Lemma 1. A Γ′-free path cannot leave a bad window
backwards. So from a step of a window W a Γ′-free path, which has at most D vertices, stays in the
windows that are reached from W in at most D moves, each move going from a good window to the window
before it or to one of its at most M predecessors: at most (M + 2)^D windows. During one window the input
head covers at most db + 1 positions, hence meets at most 3 input rows.

The append steps of an output row form an interval of steps, and these intervals are disjoint. Call a row
bad if its interval meets more than M′ + 1 windows; there are at most N/M′ ≤ εd such rows for large d. The
append steps of any other row lie in at most M′ + 1 windows. ∎

## Corollary 3 (what a bound for whole rows would give)

Suppose that for some δ > 0, some w and all large d, every set of d × d matrices over an alphabet Σ in
which every column outside at most ηd columns is a function of at most w rows has at most
|Σ|^{(1 − δ + η)d²} elements, for every alphabet (the entries here are b-bit strings, so |Σ| = d grows).
Let ε be such that w ≥ w(k, β, C, ε) of Proposition 2 and δ > 4ε. Then no machine with k work tapes and
value width β that is oblivious at length L with halting time at most C(L + 1) transposes all d × d
matrices, for large d.

*Proof.* Take the genie of Corollary O(a) at ε and enlarge it by Proposition 2. Its values form an index
code with at most 2εL bits for the cone system of Γ′ (the index-code lemma used in Corollary O(b) holds
for every Γ). A largest fibre has at least 2^{L − 2εL} inputs, and on it every output bit is a function of
the input bits in its cone set. The output bit in row r, column c demands the input entry (c, r), so on
the fibre column r of the input matrix is a function of the at most w input rows of Proposition 2, for
all but εd columns. The hypothesis bounds the fibre by 2^{(1 − δ + ε)L}. So δ ≤ 3ε. ∎

## What this is and is not

- **It is a tie, not a bound.** With the only bound known for whole rows, w d(d + 1)/(w + 1), the
  deficit is 1/(w + 1), far below ε: w is astronomically large in 1/ε. Nothing is excluded.
- **It makes one statement sufficient.** If whole-row codes of window w have rate at most 1 − δ(w), then
  oblivious linear-time transposers are excluded as soon as δ(w(k, β, C, ε)) > 4ε for one ε. With the
  conjectured value one half for every window, ε = 1/9 does it.
- **It is a necessary condition for a machine.** A linear-time oblivious transposer yields whole-row
  codes of bounded window whose rates tend to 1 as the window grows. No such codes are known at any
  rate above one half.
- **It is not a property of the abstract high-rate families** unless they can be laid out on an array
  with boundedly many helper rows per column. That is not known; natural layouts fail.
- The row maps are compositions of at most D last-visit maps, and a last-visit map is monotone on
  each side of the head. So the cover is by words of monotone partial row maps, the shape of the
  fifth paper's row-word certificate (its Theorem 6.4), which that paper extracts for one executor.
  The number of words here grows with 1/ε, so that theorem gives an underpaid deficit.

## To be checked

1. Lemma 1 against the exact definition of the dependency DAG in the fourteenth paper's library (pauses,
   first visits, the cell under the head before or after the move).
2. That the index-code lemma applies to the enlarged Γ′ and that "full depth" is not increased.
3. The treatment of the input head and of rows that straddle windows.
4. The alphabet: the hypothesis of Corollary 3 is needed for entries that are b-bit strings.

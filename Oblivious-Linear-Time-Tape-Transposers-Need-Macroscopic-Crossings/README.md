# Oblivious Linear-Time Tape Transposers Need Macroscopic Crossings

Hans Brende, Claude Opus 5.5 (Anthropic) and Gemini 4 Argon (Google DeepMind), November 2026.

- [`paper/`](paper/): the paper ([`main.pdf`](paper/main.pdf)) and its LaTeX sources. License: CC BY 4.0
  ([`paper/LICENSE`](paper/LICENSE)).
- `lean/`: the Lean 4 formalization (Lean and Mathlib v4.34.1), to be added. It requires the libraries of the first, eighth,
  eleventh, fourteenth and fifteenth papers by relative path, so the sibling directories of this repository must be in place.

## The question

Can a multitape Turing machine transpose a d×d matrix of b(d) = max(1, ⌈log₂ d⌉)-bit entries, written row by row, in time linear in its
length L = d²b(d)? This is statement (T) of the [first paper](../Matrix-Transposition-and-the-Tape-Coding-Conjecture/). For oblivious
machines the series has reduced (T) to a coding question on the machine's own time–space network: the fourteenth paper showed that
the crux alone would exclude oblivious linear-time transposers. This paper asks which schedules make the crux provable, and shows that it
holds for every schedule in which a small enough set of steps separates a large set of outputs from the macroscopic crossings of the tapes.

## What is proved

To be stated with the Lean declarations and the axiom statement when the formalization is added. The paper proves:

- **Theorem X (macroscopic crossings).** For every oblivious machine that transposes in time C(L+1) and every set V₀ of at least αL output
  positions, every set of steps separating the output steps of V₀ from the earlier ends of crossing revisits of excursion more than θL
  has at least c|V₀| elements at all large d, with explicit θ, c > 0 depending only on the number of tapes, the alphabet, the number of
  states, C and α.
- **Theorem D.** The same mechanism for every linear-time trace, with no hypothesis on what the machine computes: either such crossings
  are reached with linear expansion, or a cheap separator leaves a linear-size acyclic set in the cone relation.
- **Theorem S.** At scale θL/4 the run's coarse skeleton comes from an explicit finite family independent of d, and the expansion of
  Theorem X is carried by a single coarsely monotone leg of a single tape.
- **Theorem H.** Every oblivious or low-adaptivity linear-time transposer has two work heads that make revisits of linear excursion.
- **Theorem E.** The conclusions of Theorems X and S on every η-heavy trace (η ≤ (α/8)ρ₀) of an arbitrary linear-time transposer, and on
  the heavy traces of the fifteenth paper's bit simulator of every linear-time transposer.
- **Lemma R.** For every two sets of rows, every cut between the reads of the first and the outputs they feed into the second carries
  the corresponding information, whatever the coding.
- **Class exclusions.** Bounded macroscopic phases, oblivious and adaptive with sublinear jitter (Theorems B and J); a native gap
  criterion (Theorem G); a scale-gap pigeonhole for machines without a free work head (Theorem Q).

Proved in the paper but not formalized: Proposition 10.2 (one cut serves every pair of row sets) and Corollary 7.3 (scale-separated
traces). The exclusions of the individual schedule families of the appendix are proof sketches.

## What is open

The paper ends with four problems: a pass bound that counts phases across all scales; transferring the simulator results back to the
machine's own dependency DAG; sharper constants; and the five explicit linear-time cascade schedules that met every necessary
condition proved here in our numerical tests (d ≤ 128).

## Building and verifying

To be completed with the formalization: `lake exe cache get`, `lake build` and `lake env lean PaperAxioms.lean` in `lean/`.

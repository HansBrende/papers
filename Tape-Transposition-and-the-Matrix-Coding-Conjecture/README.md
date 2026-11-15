# Tape Transposition and the Matrix Coding Conjecture

Hans Brende, Claude Fable 5.2 (Anthropic) and GPT-6 Astra (OpenAI) · November 2026

**Draft.** The introduction and the preliminaries are written; the other sections state their results and
mark in red what is still to be written. The proofs, the paper's own Lean library, the index of
declarations, the reviews and the literature search are not done. Nothing here should be cited yet.

[Paper PDF](paper/main.pdf) · [LaTeX](paper/) (CC BY 4.0)

## The question

Can a multitape Turing machine transpose a d × d matrix of ⌈log₂ d⌉-bit entries in linear time? The
first paper of the series,
[*Matrix Transposition and the Tape Coding Conjecture*](../Matrix-Transposition-and-the-Tape-Coding-Conjecture/),
reduced this to a conjecture about network codes on the time–space diagrams of tapes. This paper is its
companion: a conjecture about arrays alone implies that conjecture.

A *whole-row code* of window w is a set of d × d arrays in which every column is a function of at most
w rows. The **Matrix Coding Conjecture** says that such codes have rate bounded away from one, by a
bound that does not depend on w.

## What is proved

Formalized in Lean 4 with the standard axioms only. The declarations currently live in
[`lean-backlog/`](../lean-backlog/) and [`lean-machine/`](../lean-machine/); they will move to this paper's
library.

- The Matrix Coding Conjecture implies the robust Tape Coding Conjecture and hence that
  `Transpose.LinearTimeTransposable` is false, for all machines
  ([`WholeRowTCC.lean`](../lean-backlog/WholeRowTCC.lean)). A weak form suffices
  ([`Wall.lean`](../lean-backlog/Wall.lean)).
- For oblivious machines, after a cheap cut the outputs of almost every row of the transpose depend on
  boundedly many rows of the input.
- A two-sided normal form; the exact value of every acyclic-set bound, and barriers for order and
  closure arguments; entropy bounds below every acyclic bound on the Fano and grid relations and on
  mixing lifts; rate one half for codes invariant under a pairing.

Proved in the text and not formalized: the existence of mixing relations and of mixing lifts at bounded
window, and one exclusion of runs that a cheap cut splits.

## What is open

The Matrix Coding Conjecture itself, in any of its forms. No converse is known: a refutation would not
give a machine.

## Building

```sh
cd paper && latexmk -pdf main.tex
```

The Lean build instructions will be added with the paper's library. Until then see
[`lean-backlog/Wall.lean`](../lean-backlog/Wall.lean) for the commands that check the main implications.

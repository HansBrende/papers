# Class-Uniform Codes in Every Characteristic but Three, Their Blow-ups, and the Price of Advice

Hans Brende, Claude Opus 5.5 (Anthropic) and Gemini 4 Argon (Google DeepMind), November 2026.

Memo extending [*Order, Symmetry and the Swap: A Synthesis of Matrix Transposition on Tapes*](../README.md). The
paper and its formalization are unchanged.

- [Memo PDF](paper/main.pdf) and [LaTeX sources](paper/), licensed under [CC BY 4.0](paper/LICENSE).
- [Lean proofs](lean/) (`ClassUniformMemo`, Lean and Mathlib v4.34.1), licensed under [Apache 2.0](lean/LICENSE). The
  library requires the paper's library `SwapRigidity` by the relative path `../../lean`, and through it the shared
  [`lean-machine/`](../../lean-machine/) library, so those directories of the repository must be in place.
- [`tools/`](tools/): the generator of the data of the rational codes, their certificates, and the generator of the
  index of Lean declarations.

## The question

The paper's Theorem TP bounds the codes of a class-uniform rule (row c of a d × d matrix is a fixed linear function of
the matrix with its columns rotated by c, the function depending only on the class of c) by (d² + Md)/2 when the M
classes are intervals. Its Proposition 8.2 shows that the bound can fail for classes with no almost-period: at d = 6
the classes {0, 1, 3} and {2, 4, 5} carry a code of dimension 25 > 24 over GF(2). The memo asks whether that gain
depends on the field, how gains of this kind can be amplified, and what advice costs in this model, which the paper's
second step from the one-hop model to oblivious machines (depth reduction) needs.

## What is proved

Every theorem, proposition and corollary is proved in Lean. All cited declarations depend at most on `propext`,
`Classical.choice` and `Quot.sound`. Declarations are in the namespace `ClassUniformMemo`. One remark, labelled as
numerical, records two facts about the data that the data generator checks and no proof uses.

- **Theorem A, every characteristic but three (`Fields.lean`):** `exists_code_of_three_ne_zero`. Over every field in
  which 3 ≠ 0, the classes {0, 1, 3} and {2, 4, 5} of Z/6 carry a class-uniform code of dimension 25; in particular
  over every field of characteristic zero (`exists_code_of_charZero`) and over GF(p) for every prime p ≠ 3
  (`exists_code_zmod`). The proof transfers explicit certificates along ring homomorphisms (`Transfer.lean`): two
  codes over the rationals, with denominators involving the primes 2, 3, 7 and 2, 3, 5, 13, and the paper's code over
  GF(2). The finite facts about the rational data are proved by `decide`.
- **Theorem B, blow-ups (`BlowUp.lean`):** `isClassUniformCode_blowUp`, `finrank_blowUp`. The matrices on Z/dk all of
  whose k² blocks (entries in rows ≡ u and columns ≡ v modulo k) lie in a class-uniform code form a class-uniform code
  for the colouring c ↦ (class of ⌊c/k⌋, c mod k), with k times as many classes and k² times the dimension. The
  excess of a code over the interval value is multiplied by k², and so is dM (`two_mul_finrank_blowUp_sub`).
- **A family with growing excess (`Excess.lean`):** `two_mul_finrank_blowUp_code`. For d = 6k and 2k classes there are
  codes of dimension 25k², an excess of k² = dM/12. This answers the paper's Problem 9.1(c) as worded, but only because
  the number of classes grows; the memo restates the problem for a bounded number of classes.
- **The decoders cannot ignore the position (`Excess.lean`):** `finrank_lt_of_mergedCls`. For k ≥ 2, every
  class-uniform code for the two classes c ↦ class of ⌊c/k⌋ on Z/6k, obtained by forgetting the position, has
  dimension less than 25k².
- **Theorem C, linear advice costs its rank (`Advice.lean`):** `IsClassUniformCodeWithAdvice.two_mul_finrank_le`. If
  each row may also use the value of a linear map α of the matrix, in its own way, then the matrices of the code on
  which α vanishes form a class-uniform code, and 2·dim ≤ d² + d|S| + 2·rank α. Every code extends by exactly q
  dimensions with linear advice of rank q, for every q ≤ d² − dim (`isClassUniformCodeWithAdvice_sup_range`,
  `finrank_sup_range`).
- **Theorem D, the price of advice of any kind (`Advice.lean`):**
  `IsCodeWithAnyAdvice.natCard_pow_two_mul_finrank_le`. Over a finite field F, let the advice be any map to a finite
  set Ω, and let the rows obey, on each fibre, a class-uniform rule with offsets for a colouring whose class changes
  lie in a non-empty set of at most s rows. Then |F|^(2·dim) ≤ |Ω|²·|F|^(d² + ds); with |Ω| = |F|^q this is
  2·dim ≤ d² + ds + 2q. Each symbol of advice costs one dimension, and each class change it induces costs half a row.
  The paper suggests charging each revealed bit as a regime change, at half a row; advice that enters linearly induces
  no class change and costs one dimension per symbol.

## What is open

Whether the classes {0, 1, 3} and {2, 4, 5} carry a code of dimension 25 in characteristic 3; and whether, for a
fixed number of classes, the excess over (d² + Md)/2 is bounded. For machines, the price of advice still needs a
version of Theorem TP for the cone systems of real schedules, a form of it that tolerates offsets depending on the
row, and a bound on the class changes that a genie induces. Statement (T) remains open. All results concern the
paper's linear one-hop model, not machines.

## Building and verifying

From this memo's directory:

```sh
python3 tools/lean_index.py --check
python3 tools/gen_rational_data.py --check
cd lean
lake exe cache get
lake build
lake env lean PaperAxioms.lean
```

The cache command is for a fresh checkout. `PaperAxioms.lean` runs `#print axioms` on all declarations cited by the
memo, from its own library and from the paper's; each reports at most `propext`, `Classical.choice` and `Quot.sound`.
No file of the library uses `sorry`, `native_decide`, a new axiom, or a raised heartbeat or recursion limit.

To build the PDF, run `latexmk -pdf main.tex` in `paper/`.

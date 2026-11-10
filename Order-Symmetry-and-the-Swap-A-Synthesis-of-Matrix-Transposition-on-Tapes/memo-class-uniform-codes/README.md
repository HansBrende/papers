# Class-Uniform Codes in Every Characteristic but Three, Their Blow-ups, and the Price of Advice

Hans Brende, Claude Opus 5.5 (Anthropic) and Gemini 4 Argon (Google DeepMind), November 2026.

Memo extending [*Order, Symmetry and the Swap: A Synthesis of Matrix Transposition on Tapes*](../README.md), cited at
revision b2c389a. The memo modifies neither the paper nor its formalization; the paper's later revision 14b157a cites
the first version of the memo.

- [Memo PDF](paper/main.pdf) and [LaTeX sources](paper/), licensed under [CC BY 4.0](paper/LICENSE).
- [Lean proofs](lean/) (`ClassUniformMemo`, Lean and Mathlib v4.34.1), licensed under [Apache 2.0](lean/LICENSE). The
  library requires the paper's library `SwapRigidity` by the relative path `../../lean`, and through it the shared
  [`lean-machine/`](../../lean-machine/) library, so those directories of the repository must be in place.
- [`tools/`](tools/): the generators of the Lean data with their certificates, the exact checkers behind the numerical
  remark and the proof on two classes, and the generator of the index of Lean declarations.

## The question

The paper's Theorem TP bounds the codes of a class-uniform rule (row c of a d × d matrix is a fixed linear function of
the matrix with its columns rotated by c, the function depending only on the class of c) by (d² + Md)/2 when the M
classes are intervals. Its Proposition 8.2 shows that the bound can fail for classes with no almost-period: at d = 6
the classes {0, 1, 3} and {2, 4, 5} carry a code of dimension 25 > 24 over GF(2). The memo asks whether that gain
depends on the field, how such gains can grow, and what advice costs in this model, which the paper's second step from
the one-hop model to oblivious machines (depth reduction) needs.

## What is proved

Every theorem, proposition and corollary is proved in Lean, except the theorem on the parity-coset codes for general
d and its corollary, whose proofs are written in the memo; Lean checks that theorem at d = 8, 12 and 16. All cited
declarations depend at most on `propext`, `Classical.choice` and `Quot.sound`. Declarations are in the namespace
`ClassUniformMemo`. Two remarks, labelled as numerical, record exact computations; no proof uses them.

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
  codes of dimension 25k², an excess of k² = dM/12. This answers the paper's Problem 9.1(c) as first worded, but only
  because the number of classes grows; the memo restates the problem for a fixed number of classes, as the paper's
  later revision does.
- **The decoders cannot ignore the position (`Excess.lean`):** `finrank_lt_of_mergedCls`. For k ≥ 2, every
  class-uniform code for the two classes c ↦ class of ⌊c/k⌋ on Z/6k, obtained by forgetting the position, has
  dimension less than 25k².
- **Two classes: the parity-coset codes (proof in the text; `ParityCoset.lean` for d = 8, 12, 16):**
  `exists_parityCoset_code_d8`, `_d12`, `_d16`. For d = 4k ≥ 8, let J₀ be the even residues other than d − 2, and J₁
  the rest. This partition has no almost-period, and the paper's Theorem TP with the shifts {0, 2} bounds the excess of
  its codes over the interval value (d² + 2d)/2 by d/2. Over every field in which 2 ≠ 0, an explicit rule whose
  decoders each read one anti-diagonal has a code of dimension (d² + 2d)/2 + d/4 − 1, for every d = 4k ≥ 8. The proof,
  a rank count on each anti-diagonal, is written in the memo; Lean checks d = 8, 12 and 16 (an excess of 1, 2 and 3),
  and exact computation over the rationals checks every d ≤ 100 (`tools/parity_coset_rule.py`). So the excess of two
  classes is unbounded: the paper's Problem 9.1(c), as now stated, has a negative answer for two classes over these
  fields. For a balanced partition at d = 12 and its periodic lift to d = 24 there are codes with excess 2 and 4, and
  at d = 9 a code with excess 1/2 (`tools/check_certificates.py`).
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
  The paper, at the revision cited, suggested charging each revealed bit as a regime change, at half a row; advice
  that enters linearly induces no class change and costs one dimension per symbol. The paper's later revision corrects
  that charge.

## What is open

Whether the classes {0, 1, 3} and {2, 4, 5} carry a code of dimension 25 in characteristic 3. Whether the excess at a
fixed number of classes is bounded for M ≥ 3, and for two classes in characteristic 2. A Lean proof of the
parity-coset theorem for every d. Whether the excess of two classes over (d² + 2d)/2 is always O(d), which would prove the paper's Problem 9.1(a) for two
classes, or whether some family grows faster; an excess of order d² would be a coding gain at positive rate native to
masks and rotations. For machines, the price of advice still needs a
version of Theorem TP for the cone systems of real schedules, a form of it that tolerates offsets depending on the
row, and a bound on the class changes that a genie induces. Statement (T) remains open. All results concern the
paper's linear one-hop model, not machines.

## Building and verifying

From this memo's directory:

```sh
python3 tools/lean_index.py --check
python3 tools/gen_rational_data.py --check
python3 tools/gen_parity_coset_data.py --check
python3 tools/check_certificates.py
python3 tools/check_certificates.py --translates --structure
python3 tools/parity_coset_rule.py
cd lean
lake exe cache get
lake build
lake env lean PaperAxioms.lean
```

The cache command is for a fresh checkout. `PaperAxioms.lean` runs `#print axioms` on all declarations cited by the
memo, from its own library and from the paper's; each reports at most `propext`, `Classical.choice` and `Quot.sound`.
No file of the library uses `sorry`, `native_decide`, a new axiom, or a raised heartbeat or recursion limit.

To build the PDF, run `latexmk -pdf main.tex` in `paper/`.

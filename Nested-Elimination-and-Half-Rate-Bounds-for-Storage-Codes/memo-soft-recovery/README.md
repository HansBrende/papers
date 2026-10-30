# Soft Recovery and Record Capacities in Nested Elimination

Hans Brende and GPT-6 Astra (OpenAI) — October 2026

Extension memo to [*Nested Elimination and Half-Rate Bounds for Storage Codes*](../README.md).
The original paper and its formalization are unchanged.

- [Memo PDF](paper/main.pdf) and [LaTeX sources](paper/), licensed under
  [CC BY 4.0](paper/LICENSE).
- [Lean proofs](lean/), licensed under [Apache 2.0](lean/LICENSE).

## The question

Can a certified half-rate relation remain useful when local recovery needs
additional coded records, loses information between uses, or is incomplete?
This memo gives explicit information bounds for those situations. It does
not establish a new uniform tape transposition lower bound.

## What is proved

Every new numbered result in the memo is proved in Lean. The Lean declarations
are the proofs; the English outlines are guides to them. All audited declarations
depend at most on `propext`, `Classical.choice`, and `Quot.sound`.

- **Soft decomposition (Theorem S).** For every certified piece decomposition,
  the half-rate inequality holds with an added sum of conditional recovery
  uncertainties. The sharper form retains the conditioning supplied by earlier
  pieces. The original exact decomposition, rate, and cardinality bounds follow
  directly. Paper 10's relative Class S certificates inherit the extension.
- **Helper reuse.** A helper pays its terminal mutual information and the positive
  drops in information about that helper between uses. Each drop is at most the
  conditional entropy of the context lost at that transition. Semantic
  retention—determining the earlier context and target, possibly through a
  different encoding—suffices for a one-capacity bound on a list. Literal nesting
  is a corollary.
- **Combined information bound (Theorem I).** Let $B=\sum_v b_v$ and
  $H(X_V\mid Z)\ge B-\delta$. Given the same certified parent relation and an exact
  cover of all actual helper occurrences, every common reveal $Q$ satisfies

  $$
  B+S_Q\le 2\delta+2J_Q+\Phi_Q+D_Q+E_Q.
  $$

  Here $S_Q$ is unused coordinate capacity, $J_Q$ the information disclosed about
  the selected input, $\Phi_Q$ the sum of terminal helper information, $D_Q$ the
  sum of helper-specific information drops, and $E_Q$ the remaining local recovery
  uncertainty. The memo defines these quantities precisely. The theorem needs
  no exact decoding or retention assumption. Individual capacity bounds make
  $S_Q$ nonnegative but are not needed for the algebraic statement.
- **Capacity corollaries (including Corollary C).** Assume the coordinate bounds
  $H(X_v\mid Z)\le b_v$. If record $e$ has conditional entropy at most $c_e$ and is
  covered by $k_e$ lists, the simpler bound is
  $B\le2\delta+\sum_e c_e\min\{2,k_e\}+\mathcal L_{\varnothing}+E_{\varnothing}$.
  Semantic retention and exact recovery remove both residual terms. Helpers can
  also be charged jointly without a use cover; the simpler count then uses the
  number of local recoveries using each helper.
- **Exact controls.** Finite entropy examples verify the residual/private/shared
  coefficients $1/1/2$, strictly separate semantic retention from literal nesting,
  and show strict information-loss and revelation-credit savings. A parity example
  proves that $D_Q$ can increase after a reveal: it must be evaluated after the
  chosen reveal. The larger whole-context loss does decrease under conditioning.

The general inequalities hold for arbitrary normalized, monotone, submodular
rank functions. The finite Shannon instance permits correlated nonlinear records
and arbitrary common information. Its entropy units are nats; a fair bit has
entropy $\log 2$.

## What is open

A useful application must provide the actual parent-relation certificate and
preserve every helper identity, target, and original conditioning context. It
must then prove a positive margin after paying every reveal, loss, and recovery
residual. Tape chronology and repeated use of one physical cell do not supply
those obligations automatically.

The finite controls compare individual charges. They do not establish an
improvement over all optimized older certificates. Such an application, a uniform
native paid margin, and the general transposition question (T) remain open.

The memo is an extension and consolidation of the earlier decomposition and
entropy proofs. Related work includes Elishco and Barg's conditional-entropy
notion of imperfect recovery and Thakor, Grant, and Chan's functional-dependence
bounds; the manuscript gives the checked references and the scope of the comparison.

## Building and verifying

Clone the complete repository with sibling directories in place. The package
requires Paper 10 by a relative path and reuses Paper 7 and earlier libraries
through it. Lean and Mathlib remain pinned to v4.34.1.

From this memo directory:

```sh
python3 tools/lean_index.py
cd lean
lake exe cache get
lake build
lake env lean PaperAxioms.lean
```

The cache command is for a fresh checkout. The generator reads the manuscript
and library to produce the declaration index and the full audit: 66 declarations
cited by the manuscript and 129 audited declarations, including all public memo
theorems and the reused XOR witness. `python3 tools/lean_index.py --check` checks
that generated files are current. `tools/generate_axioms.py` remains an alias.

To build the PDF, run `latexmk -pdf main.tex` in `paper/`. No new axioms, proof
placeholders, kernel-bypassing evaluation, unsafe declarations, or increased
heartbeat limit are used.

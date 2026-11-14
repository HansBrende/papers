# What the whole-row relaxation forgets

Hans Brende, Claude Fable 5.2 and GPT-6 Astra, 14 November 2026.
**Status:** source audit and written reductions, independently reviewed.
Existing Lean declarations are linked below; no new equivalence between
arbitrary network codes and machines is asserted. This ledger answers which
additional requirements a code construction would have to meet. It does not
open a new capacity search or prove an exclusion.

Write L=d²b(d) for the raw input length. B1 proves that a common positive
whole-row deficit, along the canonical alphabets, excludes oblivious
linear-time transposers. Its converse is not proved. A large whole-row code
is one necessary object, not a construction of a transposer.

## 1. An exact top statement needs the local execution semantics

An exact reformulation can avoid the word “machine” by specifying a family
of finite, typed computation diagrams with the following data:

1. One fixed finite state set, work-symbol alphabet, work-tape count and
   transition table, independent of d and of the input values.
2. For each d, a horizon T≤C(L+1), unit-speed input/work walks and an append
   schedule shared by every length-L input. All heads start at zero, work
   cells start blank, and the initial state is fixed.
3. At every step and for every input, the same table takes the current
   state, the one scanned input bit or out-of-input symbol, and the scanned
   work symbols. It produces the next state, writes, moves, and optional
   output bit. A work symbol comes from the last visit to that cell, or
   from its initial blank value. The stated walks and append schedule must
   agree with these table outputs; they are not externally supplied control.
4. The run halts as required and appends exactly the transpose in its
   prescribed order on **every** input. The output is unreadable and has
   no dependency back into the computation.

Unrolling a fixed oblivious transposer supplies these data. Conversely,
install the stated finite table and initial data: induction on time says
its actual state, scanned symbols, writes, moves and appends agree with
the diagram on every input. Thus this is a semantic re-encoding of the
original computation, with the same time bound, not a simpler capacity
criterion. No separate Lean converse for this new packaging is added here.
The underlying finite-table semantics already occur in the first paper's
[machine definitions][P1defs] and the eleventh paper's [field DAG][P11prune].

A generic causal network code on a valid tape diagram is weaker. Its nodes
can compute different arbitrary functions; at block level they can see
whole attached rows and transmit blocks. A computable family of graphs
alone does not pay for generating or executing its control in linear
time. A common finite gate *catalogue* alone likewise does not enforce
that gate choices and head moves are produced by the same finite table.
Keeping item 3 avoids both gaps.

The classical citation supports the **forward** reduction: [Adler, Harvey,
Jain, Kleinberg and Lehman, *On the Capacity of Information Networks*,
Theorem 6.2][AHJKL] turns a fast oblivious I/O transposition algorithm into
a network coding/routing gap. Theorem 6.3 supplies the two-tape-to-I/O
simulation. Neither is an arbitrary-network-code-to-uniform-machine
converse. The first paper's [codes section][P1codes] explicitly distinguishes
its one-way `traceClass_code` / `codes_of_fastOn` reductions from its broader
causal-code conjecture.

Planarity also needs its graph specified. The state spine plus one work
tape's previous-visit edges has two noncrossing pages, hence is planar;
k work tapes give a union of k such pieces along the spine. Input-source
attachments and the transpose source/demand pairing are additional data.
This does not make the full source-demand network or the row helper graph
planar. The input is read-only: repeated reads attach the same source,
not a newly written mutable value. See [WindowPages.lean][Pages] and the
[input-attachment control][Attachments].

## 2. The six proposed ingredients

These are overlapping requirements, not six proved strict rungs. A useful
chain must retain one common witness while forgetting data; independently
chosen witnesses for its separate requirements would be weaker again.

| Ingredient | What the series already supplies | What is lost, or still needs a precise new premise |
|---|---|---|
| **a. Shape of the helper relation** | `native_row_spread_prefix` constructs Γ′, exceptional columns E and a common ρ from a unit-speed work trace, the input walk and the append schedule. `ConeRowsExcept` certifies that every relevant bit cone is covered by those input rows. Neither correctness nor cheapness of the original cut is a geometric premise. [B1 geometry][Window]. | The whole-row bound permits every width-w relation and replaces the actual cones by complete helper rows. “Induced by k walks” must keep the input attachments, append positions, cut and grouping as well as the work edges. Work planarity by itself is insufficient. The exact witness predicate is already available; a useful simpler property of ρ is not supplied automatically. |
| **b. Cuts and scales** | One native run supplies one valuation of all its steps. Raw records on nested revealed sets are restrictions of that same valuation. `exists_indexCode` applies to **every** Γ, and `coneSystem_antitone` / `coneSystem_change_cut` compare the corresponding cones. [Native code][Native], [cut adapters][Statements]. | B1 chooses a suitable cheap cut enlargement and helper relation for each parameter choice. It does not produce nested cheap cuts, nested ρ's, or a new cross-dimension compatibility theorem. Runs at different input lengths share the table, not literal embeddings of their input spaces. Arbitrary bit recodings in `IsIndexCode.bits` need not preserve the raw record's restriction maps. |
| **c. One rule** | Native field values are generated from the same finite transition table; `Pruning.toFunDag` and its determination proof retain the causal evaluation. [Field semantics][P11prune]. | Eliminating intermediate fields can give different recovery functions at different coordinates and record values. A single table does not imply the class-uniform or shift-covariant decoders of the shared-decoder papers. Merely writing all column functions as one function of “column index plus data” adds no restriction. The missing content is a common local factorization with its geometry and execution budget. |
| **d. Causal production** | The actual computation produces the step payloads and output. `Pruning.field_isIndexCode` and `exists_indexCode` extract records from those payloads. The first paper supplies causal block-network codes; the shared-decoder paper states the separate native interface obligations. [Native records][P11record], [block codes][P1codes], [shared interfaces][SharedOpen]. | A storage fibre is a subset of the **raw inputs**. The machine need not generate or sample it from independent sources. What must be produced is the transcript/advice and output. The chosen genie itself, and the arbitrary finite-range recoding used in the existential index-code lemma, are not supplied with a uniform linear-time generation algorithm. An efficient code encoder or selector is an additional claim. |
| **e. Bit granularity** | `coneSystem` retains the actual input position read at each time occurrence; bounded depth gives `card_depCone_le` with at most Σ_(j≤D)(k+1)^j raw positions per cone. Work dependencies and source reads remain separate. [Native cones][Native], [finite cone count][Statements]. | Row enlargement forgets which bits were read, their order and the causal paths. A source position may be reread many times: bounded time-vertex degree is not a constant reverse-degree bound on raw source bits. Any such degree cap must be proved or paid for. No shift covariance follows from unit speed alone. |
| **f. All fibres** | `IsIndexCode` is a statement on **all inputs**. `entryWord_wholeRow_of_cones` works on every common-message/raw-record fibre with the same ρ,E; `indexCode_length_le_of_wholeRowBound` sums their bounds over all observations. [Finite transfer][Transfer]. | A single large-fibre presentation hides the rest of this partition. But an unrestricted all-fibre partition with a common relation is not, by itself, a stronger asymptotic obstruction: translated covers restore it with only logarithmic overhead, as below. The extra requirement is the native causal origin and joint consistency of the records/rules. |

For a native **Crux** result, an additional distinction matters. `SCone`
does not assume transposition correctness or a cheap Γ. `CruxOn` bounds
every index code on every cone system in that class, not only the record
computed by the witnessing trace's machine. A property of the actual
correct-machine record can suffice for a machine exclusion without proving
this stronger Crux. The [conditional exclusion table][Exclusions] separates
those consumers.

## 3. Cheapest exact code-language refinement: retain the encoder

The existing finite adapter already proves the following stronger statement
than “there is a large fibre.” Fix I,J,ρ,E,U and an index encoder enc with
m output bits, satisfying

  I(ℓ) ⊆ J(ℓ)∪U,    ConeRowsExcept J ρ E,
  IsIndexCode enc I tpos.

Record enc(x), the raw bits x|_U, and all bits of the exceptional columns E.
This is one map on the full binary cube with at most

  2^(m+|U|+db|E|)

record values. Every record fibre, grouped into entries, is a whole-row
code for the **same** relation: use ρ outside E and empty helpers on E.
All these fibres partition the source cube. Consequently at least one
has size at least 2^(L−m−|U|−db|E|), but the proof need not select it.
These are the steps in [ConeCodeTransfer.lean][Transfer], including its
exceptional-column adapter and fibre summation. This adds no conjecture.

Keeping an encoder is useful only with its budget and provenance. The
bare “all fibres” requirement can already be rebuilt from a single code.
For a binary whole-row code C with 2^L≤2^m|C|, the first paper's
[`exists_shift_cover`][ShiftCover] gives 2^m(L+1) XOR translates covering
the whole cube. Choose for each input one covering translate. Its selector
fibres are subsets of translates of C, so each retains the same whole-row
recovery relation. The selector needs at most

  m+⌈log₂(L+1)⌉

bits. Translation preserves equality on every helper view, so this argument
also applies when bits are grouped into canonical entries. It is a written
application of the already formalized covering lemma, not a new Lean
whole-row adapter or a new covering theorem. No efficient or native selector
is asserted. The first paper's [plain/robust analysis][P1hints] already makes
this distinction between an oracle hint and a network-computable one.

Thus a large fibre and an unrestricted common-relation index encoder have
the same leading information cost. To get a genuinely narrower class here,
retain the causal provenance, not just the existence of all the fibres.

## 4. Missing ingredients and the order of the ledger

In addition to a–f, keep explicit:

- **Fixed physical resources:** the number of tapes, finite control and
  work alphabet are fixed before d grows. The growing input-entry alphabet
  is not a growing unit-cost work alphabet.
- **One common execution witness:** the source addresses, cuts, records,
  intermediate values, recovery functions and schedules all come from the
  same run family; independent existence claims need not fit together.
- **Boundary and demand data:** blank initialization, source values and
  out-of-range reads, exact transpose indexing, unreadable output and
  termination. A graph without these labels is not an execution.
- **Full-input correctness and uniformity:** one finite table must work on
  all inputs at all required sizes, with no uncharged advice or externally
  supplied moves. A per-size network code may be nonuniform.
- **The advice invoice:** actual message range/bit cost, raw conditioning
  and exceptional columns must be charged. The direct B1 consumer needs
  δ>169ε/64 at its own window; arbitrary native-index-code Crux uses the
  separate raw-boundary transfer. [Consumers][Consumer].

One further part of the common witness is **where advice can be read**.
On a depth-D native dependency DAG, let K_D=Σ_(j≤D)(k+1)^j. Evaluate an
output backwards and stop at the first revealed vertices. There are at
most K_D unrevealed time vertices and at most (k+1)K_D first-hit cut
vertices; a revealed root can instead use its one recorded value. Thus
at most 1+(k+1)K_D bounded-width step records, together with the raw bit
cone, suffice for each output. This follows by the same induction as the
cone lemma, now retaining the first-hit boundary; it is a written
consequence, not a separately exported Lean endpoint here. Generic
`IsIndexCode` permits each output to inspect the entire arbitrary message.
Keeping these per-output record views and their common tape-wired origin
is more informative than merely requiring all fibres. The [local-view audit](local-record-view-covers.md) gives its conditional demand
invoice and the missing cover/capacity premises. No general native exclusion
from this additional interface is proved.

A safe sequence of relaxations is: exact finite-table diagrams; causal
values and cut records on their native bit DAGs; an arbitrary index encoder
on one native cone system; common-relation whole-row fibres after the paid
enlargement; one large whole-row fibre. The last two agree at leading rate
if arbitrary oracle selectors are allowed. The earlier arrows discard real
conditions, but no theorem says every gap is strict or that adding the six
informal ingredients without their common witness gives a converse.

The cheapest already proved refinement is therefore the all-input encoder
on **actual bit cones**. The closest exact top statement is the same-table
typed execution. Between them, the open task is to identify a retained
property with a capacity or transport inequality that consumes it. This
ledger names the losses; it does not supply such an inequality.

[P1defs]: ../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/lean/Transpose/Tape/Defs.lean
[P1codes]: ../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/paper/sections/codes.tex
[P1hints]: ../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/paper/sections/plainrobust.tex
[ShiftCover]: ../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/lean/Transpose/Tape/CEHint.lean
[AHJKL]: https://www.math.uwaterloo.ca/~harvey/Publications/Capacity/Capacity-Soda.pdf
[P11prune]: ../../Merge-Depth-Input-Steering-and-the-Coding-Core-of-Matrix-Transposition-on-Tapes/lean/MergeDepth/FieldPruning.lean
[P11record]: ../../Merge-Depth-Input-Steering-and-the-Coding-Core-of-Matrix-Transposition-on-Tapes/lean/MergeDepth/FieldMachine.lean
[Native]: ../../Bounded-Stack-DAGs-Reduce-to-Constant-Depth/lean/BoundedStackDepth/Machines.lean
[Pages]: ../WindowPages.lean
[Attachments]: window-pages-and-input-attachments.md
[Window]: ../WindowSpread.lean
[Statements]: ../StatementsRowSpread.lean
[Transfer]: ../ConeCodeTransfer.lean
[Consumer]: ../RowSpreadCrux.lean
[Exclusions]: conditional-machine-exclusions.md
[SharedOpen]: ../../Capacity-and-Composition-of-Shared-Transposition-Decoders/paper/sections/open.tex

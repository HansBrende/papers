PACKET STRENGTHENING: REVIEW DRAFT

Scope
  Extend fixed coordinate-XOR packets to arbitrary Boolean functions of at
  most two stored coordinates, preserving the exact all-input row-recoding
  distance, degree and path/cycle bounds. Add correlated input laws, public
  helper selection, and full-cube global banks with local inverse rows.

Preservation
  Original declarations, toolchain/dependency pins and historical audit
  baselines are retained. The second review replaces duplicate old XOR and
  unweighted-cover proofs by specializations of their generalizations; exact
  reversible source changes and pre-refactor elaborated types are recorded.
  New mathematical source files are listed separately
  in source-extension.json. Current verify.py checks exact inventory equality
  with baseline plus extension, then builds the library and audits every
  manuscript-cited declaration transitively. The generated PacketAxioms.lean
  also audits every declaration owned by an extension or refactored module.
  The extension does not inherit
  the earlier library audit merely by being added to the repository.

Review
  New source and manuscript correspondence checks are recorded here; earlier
  records remain historical. review2/ records the second review separately,
  including the broader qualitative o(P) information-budget consequence.
  The current completion receipt binds the final
  PDF and reviews. Further author-requested review passes precede publication.

Limits
  Coordinate support is at most two bits, not two arbitrary stored rows.
  The bank and inverse locality hold on the full cube. Correctness may be
  restricted to a declared input family. The initial deterministic helper
  selects all branch data; subsequent adaptive queries are outside this model.
  No native running-time bound or exhaustive novelty claim is asserted.

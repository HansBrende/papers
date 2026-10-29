# Papers

| Paper | Authors | Date | Contents |
|---|---|---|---|
| [Matrix Transposition and the Tape Coding Conjecture](Matrix-Transposition-and-the-Tape-Coding-Conjecture/) | Hans Brende and Claude Opus 5.5 (Anthropic) | October 2026 | Paper ([PDF](https://hansbrende.github.io/papers/Matrix-Transposition-and-the-Tape-Coding-Conjecture/paper/main.pdf), LaTeX sources) and its Lean 4 formalization |
| [Local Coding Barriers and the Limits of Tape Geometry for Matrix Transposition](Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/) | Hans Brende and GPT-6 Astra (OpenAI) | October 2026 | Paper ([PDF](https://hansbrende.github.io/papers/Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/paper/main.pdf), LaTeX sources), its Lean 4 formalization, and verification records |
| [Bit and Word Transposition on Tapes](Bit-and-Word-Transposition-on-Tapes/) | Hans Brende and GPT-6 Astra (OpenAI) | October 2026 | Paper ([PDF](https://hansbrende.github.io/papers/Bit-and-Word-Transposition-on-Tapes/paper/main.pdf), LaTeX sources), Lean 4 reduction and compiler barriers, written phase/normalizer proofs, and reproduction tools |
| [Curved Motion, Depth Reduction, and Storage Codes for Matrix Transposition on Tapes](Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/) | Hans Brende and Claude Opus 5.5 (Anthropic) | October 2026 | Paper ([PDF](https://hansbrende.github.io/papers/Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/paper/main.pdf), LaTeX sources), its Lean 4 formalization, and certificate tools |
| [Directed Recovery Structures in Tape Computations](Directed-Recovery-Structures-in-Tape-Computations/) | Hans Brende and GPT-6 Astra (OpenAI) | October 2026 | Paper ([PDF](https://hansbrende.github.io/papers/Directed-Recovery-Structures-in-Tape-Computations/paper/main.pdf), LaTeX sources), partial Lean formalization, and explicit proof-status inventory |
| [Covers and Local Generation in Linear Storage Codes](Covers-and-Local-Generation-in-Linear-Storage-Codes/) | Hans Brende and GPT-6 Astra (OpenAI) | October 2026 | Paper ([PDF](https://hansbrende.github.io/papers/Covers-and-Local-Generation-in-Linear-Storage-Codes/paper/main.pdf), LaTeX sources), sharp finite Clebsch-cover bounds and rigidity, asymptotic covers and local generation, Lean-verified homogenization and dimension bounds |
| [Nested Elimination and Half-Rate Bounds for Storage Codes](Nested-Elimination-and-Half-Rate-Bounds-for-Storage-Codes/) | Hans Brende and Claude Opus 5.5 (Anthropic) | October 2026 | Paper ([PDF](https://hansbrende.github.io/papers/Nested-Elimination-and-Half-Rate-Bounds-for-Storage-Codes/paper/main.pdf), LaTeX sources), its Lean 4 formalization, and a script for the computational remarks |
| [Bounded Nesting and Depth Reduction for Matrix Transposition on Tapes](Bounded-Nesting-and-Depth-Reduction-for-Matrix-Transposition-on-Tapes/) | Hans Brende and Claude Opus 5.5 (Anthropic) | October 2026 | Paper ([PDF](https://hansbrende.github.io/papers/Bounded-Nesting-and-Depth-Reduction-for-Matrix-Transposition-on-Tapes/paper/main.pdf), LaTeX sources), its Lean 4 formalization (Theorems F, M and SH, the relays, stack and rigidity results and their corollaries; written proofs for the deep-nesting section and the results that cite external theorems), and an exact rank script |
| [Source Covers and Barriers to Tape Transposition](Source-Covers-and-Barriers-to-Tape-Transposition/) | Hans Brende and GPT-6 Astra (OpenAI) | October 2026 | Draft ([PDF](https://hansbrende.github.io/papers/Source-Covers-and-Barriers-to-Tape-Transposition/paper/main.pdf), LaTeX sources), twenty-six Lean-verified results and the joint-profile setup, written source-cover and restricted-impossibility proofs, and a formalization plan |
| [Directed Reciprocity and Deep-Nesting Bounds for Matrix Transposition on Tapes](Directed-Reciprocity-and-Deep-Nesting-Bounds-for-Matrix-Transposition-on-Tapes/) | Hans Brende and Gemini 4 Argon (Google DeepMind) | October 2026 | Paper ([PDF](https://hansbrende.github.io/papers/Directed-Reciprocity-and-Deep-Nesting-Bounds-for-Matrix-Transposition-on-Tapes/paper/main.pdf), LaTeX sources), complete Lean 4 formalization (Theorem S*, Theorem SH*, and deep-nesting bounds through Theorem A), and numerical reproduction script |

**[The Frontier](https://hansbrende.github.io/papers/frontier/)**: an interactive map of the multitape machines for which
linear-time transposition is ruled out, unconditionally or under open hypotheses, and of where it is still open.

Shared Lean machinery used by the papers, including ported external formalizations, is in
[`lean-machine/`](lean-machine/).

Extension memos by Hans Brende and GPT-6 Astra (OpenAI):

- [Adaptive Pass Bounds without a Runtime Assumption](Matrix-Transposition-and-the-Tape-Coding-Conjecture/memo-passes/)
  removes the halting transposer's polynomial-runtime premise in the first paper's pass bound.
- [Subcubic Storage Bounds beyond Scalar Recovery](Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/memo-subcubic/)
  extends the fourth paper with reversible rules, low-rank ports, two-step stability, and exact quadratic ranks.

See [CONTRIBUTING.md](CONTRIBUTING.md) for contribution and publishing guidance.

# Linear-Time Tape Transposition Requires Storage Codes with Rates Approaching One

Hans Brende and GPT-6 Astra (OpenAI), November 2026.

[Read the paper](paper/main.pdf) · [LaTeX sources](paper/) ([CC BY 4.0](paper/LICENSE)) · [Lean sources](lean/) ([Apache 2.0](lean/LICENSE))

## The question

If a deterministic multitape machine could transpose square matrices in linear time, what information would its tape computation have to preserve? We examine codes built from packets and codes on the original bit positions at their actual output steps.

## What is proved

- **Packet transfer.** Fix a machine with $k$ work tapes. If dimension and entry width can grow together while the logarithmic rate of the timely successful inputs approaches one, every sufficiently large degree cap $\Delta$ admits binary storage codes with growing minimum paired distance and limiting lower rate at least $1-O(f_p(\Delta))$. Here $p=4k^2+1$ and $f_j(\Delta)=(\log_2\log_2\log_2\Delta/\log_2\log_2\Delta)^{1/j}$. Full success at arbitrarily large canonical dimensions suffices. A coding upper bound whose deficit exceeds this allowance by unbounded factors along a sequence of caps would force exponentially small success at all sufficiently large dimensions and widths. [Transfer and exclusion theorems](lean/TapeStorageRates/Main.lean)
- **Native bit positions.** The simulator computes the same partial function and makes its full motion traces inexpensive to specify. At each sufficiently large cap it works for any requested separation radius, all sufficiently large dimensions, and every positive entry width. Given a nonempty timely success set $G$, each cell of its partition projects to a code on at least $(1-2^{\sqrt{\log_2\Delta}}/\Delta)L$ physical bit positions. For $X$ uniform on $G$, the probability of a cell rate below $\log_2|G|/L-Af_{2p}(\Delta)-u$ is at most $2^{-uL}$, on the same partition for every $u\ge0$. [Simulator](lean/TapeStorageRates/NativeCompiler.lean) · [Counting identity](lean/TapeStorageRates/NativeTypical.lean) · [Native rate theorem](lean/TapeStorageRates/NativeTypicalRates.lean)
- **Local prediction.** For separated targets, the sum of the information supplied by their permitted in-patch helpers is at most $2r$ times the total correlation of the input, where $r$ bounds overlap. If predictors score $m$ binary target occurrences with mean error $e$, then $m[1-h_2(e)]\le2r[n-H(X)]$. Noisy pairs attain equality. The distance test bounds the number of scored targets per patch, and exact coverage extends to finite alphabets of at least two symbols. [Information bound](lean/TapeStorageRates/PatchResidual.lean) · [Predictor errors](lean/TapeStorageRates/PatchPrediction.lean) · [Input-dependent choices](lean/TapeStorageRates/PatchPredictionEvent.lean)

All twelve numbered results are proved in Lean. The named declarations are authoritative, and the manuscript gives human-readable proof outlines. The generated [axiom checks](lean/PaperAxioms.lean) cover every declaration named in the text or its formal status lines.

## What is open

The required upper bound on storage rates remains open. A machine-specific route would show that cells carrying a positive share of the inputs must admit useful local predictions at small overlap. A construction would have to realize its high-rate recoveries by a single causal tape computation within the linear time bound.

## Building and verifying

Clone the whole repository. The Lean package uses Papers 13 and 14, Paper 7's soft-recovery memo, and their sibling dependencies by relative path. Lean and Mathlib are pinned to v4.34.1. In a fresh checkout, prepare the transitive [Paper 2 metric dependency](../Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/lean/openai-metric/README.txt). From this paper's directory, run

```sh
(cd lean && lake exe cache get && lake build && lake env lean PaperAxioms.lean)
python3 tools/lean_index.py --check
(cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex)
```

After changing declaration references or proof-status lines, run `python3 tools/lean_index.py` to regenerate both the index and the axiom checks.

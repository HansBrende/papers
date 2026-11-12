# ShuffleShear

Explicit finite transition tables (`DetTM`) and linear-time execution proofs for three native
matrix-entry permutations under the row-major binary encoding `encode d (entryBits d) A` of length
`L = d² · entryBits d`:

| File | Origin | Main declarations |
|---|---|---|
| `Model.lean` | ours | `DetTM`, `Config`, `step`, `stepN`, `ComputesWithin`, `encode`, `entryBits`, `inputLength`; `stoneShuffleMatrix`, `stoneUnshuffleMatrix`, `rowShearMatrix`; compositional finite-state block compiler (`Block`, `Runs`, `Block.toTM`, `Block.computesWithin`) and shared unary/word tape primitives (`discoverEntryBits`, `clearUnary`) |
| `StoneShuffle.lean` | ours | `stoneShuffleTM` (`k = 3` work tapes) and `stoneShuffleTM_threeTape_linear` (`150 · L` steps for `d = 2^m`, `m ≥ 1`) |
| `StoneUnshuffle.lean` | ours | `stoneUnshuffleTM` (`k = 2` work tapes) and `stoneUnshuffleTM_twoTape_linear` (`150 · L` steps for `d = 2^m`, `m ≥ 1`) |
| `RowShear.lean` | ours | `rowShearTM` (`k = 2` work tapes) and `rowShearTM_twoTape_linear` (`200 · L` steps for all `d ≥ 1`) |

`DetTM` mirrors the `TM` transition-table structure of the first paper (`Transpose/Statement.lean`)
without adding a Lake package dependency on `transpose`, so any paper importing `leanMachine` can
transport `ComputesWithin` to `Transpose.ComputesWithin` by field-by-field conversion.

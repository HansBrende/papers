# Fano dual in orbit form

Points and line normals are the seven nonzero binary triples in lexicographic
order. Residual cells are the 28 pairs `(point, line)` with nonzero dot product,
listed lexicographically. Bit `k` of a mask selects residual cell `k`.
Write `cl` for repeated whole-column recovery closure, `F_A` for the closure of
the complete residual rows of point set `A`, and `h̄` for the average of `h`
over the 168 collineations. The [geometric dictionary](orbit-dictionary.md)
gives representatives of all set orbits.

The row kinds are: N, `−h̄(S) ≤ 0`; S,
`h̄(S∩T)+h̄(cl(S∪T))−h̄(S)−h̄(T) ≤ 0`; B,
`h̄(S) ≤ 4|A|+|S∖F_A|`; I, `h̄(S)−h̄(T) ≤ |S∖T|`; and J,
`h̄(cl(S∪T))−h̄(S) ≤ |T∖S|`. These formulas use exact recovery;
the Lean certificate retains the conditional recovery costs as well.
Each row means its stated inequality multiplied by the positive integer weight.
The exact sum is `264 h̄(W) ≤ 4928`. In a B row the second mask denotes point rows; otherwise both masks denote residual cells.

| Weight | Kind | First mask | Second mask |
|---:|:---:|---:|---:|
| 117 | N | 0 | — |
| 78 | S | 3 | 61440 |
| 39 | S | 95 | 4000 |
| 63 | S | 63 | 4080 |
| 15 | S | 63 | 12272 |
| 78 | S | 31 | 47 |
| 36 | S | 255 | 2069023 |
| 42 | S | 8447 | 12272 |
| 78 | B | 47 | 0 |
| 22 | I | 16143 | 4623 |
| 22 | S | 266783 | 17952799 |
| 99 | S | 16143 | 15781647 |
| 88 | J | 27663 | 36848 |
| 88 | B | 27663 | 0 |
| 22 | S | 267007 | 2069023 |
| 99 | J | 65282 | 1 |
| 22 | S | 267007 | 4198911 |
| 77 | S | 262128 | 72097791 |
| 99 | S | 12543 | 251666687 |
| 77 | S | 61695 | 32633337 |
| 22 | J | 15830912 | 1 |
| 88 | S | 32633329 | 35648255 |
| 77 | S | 1441567 | 86048559 |
| 99 | S | 1048560 | 32636913 |
| 22 | S | 23523825 | 33157617 |
| 14 | S | 32633329 | 106954751 |
| 77 | S | 6291449 | 61862902 |
| 96 | I | 1441567 | 1439263 |
| 96 | S | 32633331 | 83206143 |
| 22 | I | 23523825 | 23261681 |
| 215 | B | 32633331 | 42 |
| 77 | S | 67105791 | 218079231 |
| 96 | S | 67105791 | 100007935 |

There are 34 set orbits after identifying masks under the 168 collineations.
The checker reconstructs every mask and does not treat an orbit label as an extra axiom.

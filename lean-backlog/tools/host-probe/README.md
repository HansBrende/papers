# host-probe

Incidence hosts: rows = points, columns = lines, helpers of a column = the points on its line
(Fano, PG(2,3), the generalised quadrangle of order (2,2), the 3×3 grid).

- `host_probe.py <fano|pg3|doily|grid> <dims> <seeds> <iters>`: exact order value by subset
  recurrence, number of mutual triangles, numerical spectrum of the mutual graph, and a slow
  alternating-projection search (zero seeds or zero iterations skips the search).
- `als.py <host> <dims> <seeds> <sweeps>`: alternating least squares for a real matrix of rank
  N − K with unit diagonal and support inside the helper relation. Its kernel is a linear
  whole-row code of dimension K on the non-incident cells. **Heuristic.** Only runs that reach
  machine precision with a clear singular-value gap count, and only as leads: the method also
  returns small errors at impossible dimensions.
- `grid_code_check.py`: verifies all 36 recovery formulas and all 21 parameter-extraction
  formulas as integer coefficient-vector identities, including the helper-row support of
  each decoder. Thus the explicit code works over every abelian group: S and T are read
  directly, and D is recovered from entry differences. Over Z/qZ it has exactly q^21
  codewords for every q ≥ 2 ([note](../../notes/triangle-free-hosts.md)). This is an
  executable symbolic certificate; it is not Lean-verified.
- `gq_grid_control.py`: verifies the ten full-line grids inside GQ(2,2),
  their exact two-fold cover of its 180 residual cells, and the resulting
  two-lane code with residual exponent 105 and full exponent 150. It reuses
  the integer grid-code identities above. This is a written construction
  with an exact checker, not Lean-verified ([note](../../notes/quadrangle-grid-control.md)).

- `delsarte_lp.py`: Delsarte's linear-programming bound for storage codes on small graphs
  in difference form, at several alphabet sizes; `rank_bound_pentagon.py`: exhaustive
  translation-invariant rank bound over F₂ on the binary 5-cycle. Finite tests for
  [this note](../../notes/array-free-forms-and-spectral-test.md); floating-point LP.
- `ordered_correction_control.py`: exact seven-row directed-cycle control for
  [the ordered entropy correction](../../notes/row-spread-of-cones.md#19-conditional-row-recovery-and-the-full-shannon-question).
  It has forward/reverse degree three, no active mutual helper pair, and
  positive middle entropy with zero correction. This is a low-rate control,
  not a capacity search; Python standard library only.

The symbolic certificate needs only the Python standard library:

```sh
python3 grid_code_check.py
python3 gq_grid_control.py
python3 ordered_correction_control.py
```

The host probes need NumPy. For example, to compute the grid summary without an optimizer:

```sh
uv run --no-project --with numpy python host_probe.py grid 21 0 0
```

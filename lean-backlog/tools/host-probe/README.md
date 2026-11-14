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

The symbolic certificate needs only the Python standard library:

```sh
python3 grid_code_check.py
```

The host probes need NumPy. For example, to compute the grid summary without an optimizer:

```sh
uv run --no-project --with numpy python host_probe.py grid 21 0 0
```

# host-probe

Incidence hosts: rows = points, columns = lines, helpers of a column = the points on its line
(Fano, PG(2,3), the generalised quadrangle of order (2,2), the 3×3 grid).

- `host_probe.py <fano|pg3|doily|grid> <dims> <seeds> <iters>`: exact order value by subset
  recurrence, number of mutual triangles, spectrum of the mutual graph, and a slow
  alternating-projection search (pass `0 0` for the last two arguments to skip it).
- `als.py <host> <dims> <seeds> <sweeps>`: alternating least squares for a real matrix of rank
  N − K with unit diagonal and support inside the helper relation. Its kernel is a linear
  whole-row code of dimension K on the non-incident cells. **Heuristic.** Only runs that reach
  machine precision with a clear singular-value gap count, and only as leads: the method also
  returns small errors at impossible dimensions.
- `grid_code_check.py`: exact check of the explicit 21-symbol code on the grid host
  ([note](../../notes/triangle-free-hosts.md)).

Run with `uv run --no-project --with numpy python <script> ...` from this directory.

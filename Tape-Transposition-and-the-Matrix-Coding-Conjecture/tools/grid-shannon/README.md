# Grid exact Shannon certificate

These are the maintained exact certificate, standard-library checker and Lean
proof generator for Paper 21, *Tape Transposition and the Matrix Coding Conjecture*.
They require Python 3.10 or later. Run from this paper's directory, without `-O`:

```sh
python3 tools/grid-shannon/verify_certificate.py
python3 tools/grid-shannon/generate_lean.py --check
```

Omit `--check` to regenerate `lean/MatrixCoding/GridCertificate.lean`.
The generator and Python checker are not trusted by the Lean proof: the kernel
checks the actual finite maps, helper containments, semantic inequalities and
integer combination. No optimizer is needed to replay the certificate.

The manuscript's entropy section states the precise result and the difference
between the finite certificate, the Shannon bound and code attainment.

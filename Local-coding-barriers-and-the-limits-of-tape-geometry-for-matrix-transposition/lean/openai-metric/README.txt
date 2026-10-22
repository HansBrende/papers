Pinned external theorem adapter

This package imports an unmodified subset of OpenAI math, commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a, under the original OAI namespace.
It does not duplicate the theorem bodies in TransposeFollowup. The upstream
Apache-2.0 license is retained in LICENSE. The full upstream Lake package
has unrelated dependencies and compatibility hooks; this adapter requires
only the identical Mathlib version needed by the audited import closure.

Before building the follow-up paper, run from its directory:
  python3 verification/fetch_openai_metric.py
For offline installation, pass --source-root PATH, where PATH contains OAI/.
For a read-only verification, pass --check.

The exact module inventory, import edges and SHA-256 digests are tracked in
verification/openai-metric-source.json. Downloaded sources and build outputs
live in .lake/ and are ignored by Git. Do not edit downloaded sources; the
verifier refuses digest mismatches. The original paper is not changed.

Imported headline: OAI.Falconer.Regularization.scalar_weak_radius_projection.
Its local-concentration assumptions still have to be proved for our matrix
construction. Library verification alone does not complete paid padding.

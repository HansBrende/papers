# Contributing

Use each paper's README for its build and verification commands. Keep Lean
toolchain and dependency pins unchanged unless deliberately updating them.

## Portable files

Keep current sources and reproduction tools portable: use relative paths and
discover tools at runtime. Keep personal filesystem paths, private workspace
references, raw local logs, and backups outside this repository or in ignored
output. Adding an ignore rule does not untrack an already committed file.

Before publishing, run these checks from the repository root with `pypdf`
installed; run the second after staging changes:

```sh
python3 tools/check_public_paths.py
python3 tools/check_public_paths.py --staged
```

The checks cover publishable files, including PDF contents and archives; the
second checks the exact staged versions. This policy applies to current files
and future commits; existing Git history is retained.

## Historical verification records

The follow-up's historical records are sanitized views, not fresh verification
runs. Embedded historical hashes identify original artifacts, not edited public
copies. The [normalization manifest](Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/verification/publication-path-normalization.json)
links those views to privately preserved originals. Paths in these records are
relative to the follow-up paper root; `external/` labels denote private inputs,
not public build dependencies. Use the documented current verification commands;
historical scripts may depend on private inputs.

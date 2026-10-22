# Papers

| Paper | Authors | Date | Contents |
|---|---|---|---|
| [Matrix Transposition and the Tape Coding Conjecture](Matrix-Transposition-and-the-Tape-Coding-Conjecture/) | Hans Brende and Claude Opus 5.5 (Anthropic) | October 2026 | Paper ([PDF](https://hansbrende.github.io/papers/Matrix-Transposition-and-the-Tape-Coding-Conjecture/paper/main.pdf), LaTeX sources) and its Lean 4 formalization |
| [Local Coding Barriers and the Limits of Tape Geometry for Matrix Transposition](Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/) | Hans Brende and GPT-6 Astra (OpenAI) | October 2026 | Paper ([PDF](https://hansbrende.github.io/papers/Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/paper/main.pdf), LaTeX sources), its Lean 4 formalization, and verification records |

This repository is intended to be cloned and used on other machines. Keep
machine-specific paths, tool locations, and private workspace references out of
committed files; use repository-relative paths and runtime tool discovery.

Before publishing, run `python3 tools/check_public_paths.py` with `pypdf` installed.
After staging changes, also run `python3 tools/check_public_paths.py --staged`
to inspect the exact files that will be committed.
It checks the current Git-visible files, including PDFs and archives, for host
filesystem paths. Raw local verification records belong outside this repository
or in ignored output; see the follow-up's
[path policy](Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/verification/PUBLICATION-PATHS.txt).

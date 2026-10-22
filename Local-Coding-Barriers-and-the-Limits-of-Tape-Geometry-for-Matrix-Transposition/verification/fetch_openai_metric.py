"""Install or verify the pinned OpenAI metric-theorem import closure.

Only the files listed in openai-metric-source.json are read. Their SHA-256
digests must match before installation. No upstream Lake hooks are run.
Use --source-root with a previously verified source checkout for offline setup.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import urllib.request


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    paper = Path(__file__).resolve().parents[1]
    manifest = json.loads((paper / "verification/openai-metric-source.json").read_text())
    root = paper / "lean/openai-metric/.lake/source"
    expected = manifest["modules"]
    imported = set()
    installed = 0
    for module, entry in sorted(expected.items()):
        relative = Path(entry["path"])
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError(f"Invalid source path: {relative}")
        if relative.as_posix() != module.replace(".", "/") + ".lean":
            raise ValueError(f"Module/path mismatch: {module}")
        destination = root / relative
        if destination.exists():
            data = destination.read_bytes()
        elif args.check:
            raise FileNotFoundError(destination)
        elif args.source_root:
            data = (args.source_root / relative).read_bytes()
        else:
            url = (f"https://raw.githubusercontent.com/{manifest['repo']}/"
                   f"{manifest['commit']}/lean/{relative.as_posix()}")
            with urllib.request.urlopen(url, timeout=60) as response:
                data = response.read()
        if hashlib.sha256(data).hexdigest() != entry["sha256"]:
            raise ValueError(f"Source digest mismatch; refusing overwrite: {module}")
        source_imports = []
        for line in data.decode().splitlines():
            match = re.match(r"^(?:(?:public|private)\s+)?import\s+(.+)", line)
            if match:
                source_imports.extend(re.findall(
                    r"\b[A-Za-z][A-Za-z0-9_.]*", match[1].split("--")[0]))
        if source_imports != entry["imports"]:
            raise ValueError(f"Import inventory mismatch: {module}")
        imported.update(source_imports)
        if not destination.exists():
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)
            installed += 1
    missing = {name for name in imported if name.startswith("OAI.")} - expected.keys()
    other = {name for name in imported if not name.startswith(("OAI.", "Mathlib."))}
    if missing or other:
        raise ValueError(f"Unaccounted imports: {sorted(missing | other)}")
    actual = {p.relative_to(root).as_posix() for p in root.rglob("*.lean")}
    if actual != {entry["path"] for entry in expected.values()}:
        raise ValueError("Installed source inventory differs from the pinned closure")
    print(json.dumps({"verified_modules": len(expected), "installed": installed,
                      "commit": manifest["commit"], "source": str(root)}, indent=2))


if __name__ == "__main__":
    main()

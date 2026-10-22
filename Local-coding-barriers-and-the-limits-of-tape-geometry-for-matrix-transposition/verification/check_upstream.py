"""Verify the original paper's complete file/directory inventory is unchanged."""

from pathlib import Path
import hashlib
import json


paper = Path(__file__).resolve().parents[1]
baseline = json.loads((paper / "verification/upstream-baseline.json").read_text())
upstream = paper.parent / baseline["directory"]
files = {
    str(path.relative_to(upstream)): hashlib.sha256(path.read_bytes()).hexdigest()
    for path in sorted(upstream.rglob("*"))
    if path.is_file()
}
directories = sorted(
    str(path.relative_to(upstream))
    for path in upstream.rglob("*")
    if path.is_dir()
)
added = sorted(files.keys() - baseline["files"].keys())
removed = sorted(baseline["files"].keys() - files.keys())
changed = sorted(
    name for name in files.keys() & baseline["files"].keys()
    if files[name] != baseline["files"][name]
)
result = {
    "unchanged": not (added or removed or changed)
    and directories == baseline["directories"],
    "files_checked": len(files),
    "added": added,
    "removed": removed,
    "changed": changed,
    "directories_unchanged": directories == baseline["directories"],
}
print(json.dumps(result, indent=2))
raise SystemExit(0 if result["unchanged"] else 1)

"""Read the ordered, additive proof extensions without replacing the baseline."""
from pathlib import Path
import json

OUT = Path(__file__).resolve().parent
MANIFESTS = (
    'packet-strengthening/source-extension.json',
    'adaptive-coding/source-extension.json',
)


def load_source_extensions():
    records, files, labels = [], {}, None
    for relative in MANIFESTS:
        path = OUT / relative
        item = json.loads(path.read_text())
        original = set(item['original_numbered_labels'])
        added = set(item['added_numbered_labels'])
        if item.get('schema_version') != 1 or original & added:
            raise RuntimeError('Invalid additive source manifest: ' + relative)
        if labels is not None and labels != original:
            raise RuntimeError('Discontinuous numbered-result inventory: ' + relative)
        if set(files) & set(item['files']):
            raise RuntimeError('Duplicate mathematical sources in extensions: ' + relative)
        files.update(item['files'])
        labels = original | added
        records.append((path, item))
    return records, files, labels

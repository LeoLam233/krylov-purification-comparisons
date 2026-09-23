"""Verify the local deliverable manifest (separate from scientific-input integrity)."""
from pathlib import Path
import hashlib

root = Path(__file__).resolve().parents[1]
manifest = root / 'PACKAGE_MANIFEST.sha256'
listed = set()
for line in manifest.read_text(encoding='utf-8').splitlines():
    expected, name = line.split('  ', 1)
    target = (root / name).resolve()
    if not target.is_relative_to(root):
        raise ValueError('Manifest path escapes project')
    observed = hashlib.sha256(target.read_bytes()).hexdigest()
    if observed != expected:
        raise ValueError('Output hash mismatch: ' + name)
    listed.add(name)
actual = {p.relative_to(root).as_posix() for p in root.rglob('*')
          if p.is_file() and p.name != 'PACKAGE_MANIFEST.sha256' and '__pycache__' not in p.parts}
if listed != actual:
    raise ValueError('Output manifest coverage mismatch')
print(f'DELIVERABLE MANIFEST PASS: {len(listed)} files')

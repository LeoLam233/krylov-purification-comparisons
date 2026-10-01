#!/usr/bin/env python3
"""Require every frozen v3 production proof source to remain byte-identical."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[1]
baseline=json.loads((root/'verification/v3-proof-baseline.json').read_text())
assert baseline['archive_sha256']=='e56c5281a10887efc745fdc80722cd0a5c359c0cd15c7794779a9839effaf1ae'
assert len(baseline['files'])==94
for rel,expected in baseline['files'].items():
 assert hashlib.sha256((root/rel).read_bytes()).hexdigest()==expected, rel
print(json.dumps({'passed':True,'unchanged_v3_proof_modules':len(baseline['files']),'method':'byte-identical SHA-256 of all 94 frozen production modules','baseline_archive_sha256':baseline['archive_sha256']},indent=2))

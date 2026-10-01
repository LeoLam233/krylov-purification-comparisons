#!/usr/bin/env python3
"""Hash the complete project proof/audit input, independently of build artifacts."""
from pathlib import Path
import hashlib
root = Path(__file__).resolve().parent.parent
paths = [root / 'Krylov.lean', root / 'Audit.lean', root / 'SemanticDependencies.lean'] + sorted((root / 'Krylov').glob('*.lean'))
for path in sorted(paths):
    print(hashlib.sha256(path.read_bytes()).hexdigest(), '  ', path.relative_to(root), sep='')

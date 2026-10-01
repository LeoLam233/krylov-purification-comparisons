#!/usr/bin/env python3
"""Build project modules in dependency order, one Lean process at a time.
This changes resource scheduling only. Lake still elaborates/checks every module
and maintains the normal pinned-dependency build traces.
"""
from pathlib import Path
import os
import re
import subprocess

root = Path(__file__).resolve().parent.parent
os.chdir(root)
files = {'Krylov': root / 'Krylov.lean'}
files.update({'Krylov.' + p.stem: p for p in sorted((root / 'Krylov').glob('*.lean'))})
deps = {name: [m for m in re.findall(r'^import\s+(\S+)', path.read_text(), re.M) if m in files]
        for name, path in files.items()}
seen, active, order = set(), set(), []
def visit(name):
    if name in seen:
        return
    if name in active:
        raise RuntimeError('Import cycle: ' + name)
    active.add(name)
    for dep in deps[name]:
        visit(dep)
    active.remove(name)
    seen.add(name)
    order.append(name)
visit('Krylov')
if seen != set(files):
    raise RuntimeError('Unimported proof modules: ' + ', '.join(sorted(set(files) - seen)))
for i, name in enumerate(order, 1):
    print(f'[{i}/{len(order)}] Kernel build: {name}', flush=True)
    subprocess.run(['lake', 'build', '+' + name], check=True)
print(f'PASS: {len(order)} project modules built in dependency order', flush=True)

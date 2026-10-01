#!/usr/bin/env python3
"""Reject proof holes / external-decider shortcuts in project Lean sources."""
from pathlib import Path
import re,sys
root=Path(__file__).resolve().parents[1]
for p in sorted((root/'Krylov').glob('*.lean')) + [root/'Krylov.lean']:
    s=p.read_text(encoding='utf-8')
    # Remove nested block comments and line comments before lexical scan.
    out=[];i=0;depth=0
    while i<len(s):
        if s[i:i+2]=='/-': depth+=1;i+=2
        elif depth and s[i:i+2]=='-/':depth-=1;i+=2
        elif depth:i+=1
        elif s[i:i+2]=='--':
            j=s.find('\n',i);i=len(s) if j<0 else j
        else:out.append(s[i]);i+=1
    clean=''.join(out)
    bad=re.findall(r'\b(sorry|admit|axiom|native_decide|run_tac|run_cmd|run_elab|run_meta|unsafe|extern|implemented_by|opaque|partial|elab|macro|syntax|csimp|ofReduceBool|trustCompiler)\b',clean)
    if 'skipKernelTC' in clean or 'skipTc' in clean or 'addDeclWithoutChecking' in clean:
        bad.append('kernel-check bypass option')
    if bad:print(p.name,bad);sys.exit(1)
print('SOURCE CHECK PASSED: all project proof modules and umbrella scanned for proof holes, added axioms, unsafe/oracle/external-decider and kernel-bypass constructs')

# Every deliverable proof module must be reachable from the umbrella.
mods={f"Krylov.{p.stem}" for p in (root/'Krylov').glob('*.lean')}
seen=set();todo=['Krylov']
while todo:
    m=todo.pop()
    if m in seen:continue
    seen.add(m)
    p=root/(m.replace('.','/')+'.lean')
    if p.exists():
        for imp in re.findall(r'^import\s+(Krylov(?:\.[A-Za-z0-9_]+)?)\s*$',p.read_text(),re.M):
            todo.append(imp)
missing=mods-seen
if missing:
    print('UNBUILT PROOF MODULES:',','.join(sorted(missing)))
    sys.exit(1)
print('IMPORT COVERAGE PASSED: every proof module is reachable from Krylov.lean')

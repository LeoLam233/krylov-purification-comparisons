#!/usr/bin/env python3
"""Non-vacuous negative controls for the same value-only release checker."""
from pathlib import Path
import json,subprocess,tempfile
root=Path(__file__).resolve().parents[1]
source=(root/'SemanticDependencies.lean').read_text()
start=source.index('  let requirements : List (Name × List Name) := [')
end=source.index('  let mut checked := 0',start)
control_prefix='''\ndef SemanticGateControl.onlyInType : Prop := True
theorem SemanticGateControl.typeOnlyRoot : SemanticGateControl.onlyInType := True.intro
\n'''
cases=[
 ('type-only-reference','SemanticGateControl.typeOnlyRoot','SemanticGateControl.onlyInType','VALUE_ONLY_REQUIRED_BRIDGE_MISSING'),
 ('unrelated-bridge','Krylov.CanonicalFamilySource.main_continued_cv_lower','Krylov.PerturbedSourceAPI.cubic_certificate','VALUE_ONLY_REQUIRED_BRIDGE_MISSING'),
 ('absent-root','SemanticGateControl.noSuchRoot','Krylov.PerturbedSourceAPI.mixed_canonical','Missing final release root'),
 ('absent-bridge','Krylov.PerturbedSourceAPI.cubic_certificate','SemanticGateControl.noSuchBridge','Missing required bridge')]
rows=[]
for label,r,b,expected in cases:
 probe=source[:start]+f'  let requirements : List (Name × List Name) := [(`{r},[`{b}])]\n'+source[end:]
 probe=probe.replace('set_option maxHeartbeats 0',control_prefix+'set_option maxHeartbeats 0',1)
 with tempfile.NamedTemporaryFile('w',suffix='.lean',prefix='v4-gate-control-',dir=root,delete=False) as f:
  f.write(probe);path=Path(f.name)
 try:
  p=subprocess.run(['lake','env','lean','-j2',str(path)],cwd=root,text=True,capture_output=True)
  log=p.stdout+p.stderr
  (root/'verification'/f'v4-gate-control-{label}.log').write_text(log)
  assert p.returncode!=0 and expected in log,(label,p.returncode,log)
  rows.append({'control':label,'expected':expected,'exit':p.returncode,'correctly_rejected':True})
 finally:path.unlink()
print(json.dumps({'passed':True,'scope':'negative controls; successful production matrix is checked separately','controls':rows},indent=2))

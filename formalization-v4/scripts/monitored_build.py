#!/usr/bin/env python3
"""Resumable, serial ordinary Lake build with independent process heartbeat.
This is resource/process evidence, not a proof checker or a proof shortcut.
"""
from pathlib import Path
import os,re,subprocess,json,time,sys
root=Path(__file__).resolve().parents[1];os.chdir(root)
files={'Krylov':root/'Krylov.lean'};files.update({'Krylov.'+p.stem:p for p in sorted((root/'Krylov').glob('*.lean'))})
deps={n:[m for m in re.findall(r'^import\s+(\S+)',p.read_text(),re.M) if m in files] for n,p in files.items()}
seen=set();active=set();order=[]
def visit(n):
 if n in seen:return
 if n in active:raise RuntimeError('cycle '+n)
 active.add(n)
 for d in deps[n]:visit(d)
 active.remove(n);seen.add(n);order.append(n)
visit('Krylov');assert seen==set(files)
out=root/'verification';out.mkdir(exist_ok=True)
heartbeat=out/'v4-build-heartbeat.json';start=time.time()
def snapshot(proc,module,index,elapsed):
 ps=subprocess.run(['ps','-eo','pid,ppid,etime,time,pcpu,rss,stat,args'],text=True,capture_output=True).stdout
 heartbeat.write_text(json.dumps({'timestamp_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'module':module,'index':index,'total':len(order),'module_elapsed_seconds':round(elapsed,1),'build_elapsed_seconds':round(time.time()-start,1),'lake_pid':proc.pid,'lake_exit':proc.poll(),'processes':ps},indent=2)+'\n')
for i,n in enumerate(order,1):
 print(f'[{i}/{len(order)}] Kernel build: {n}',flush=True)
 t=time.time();p=subprocess.Popen(['lake','build','+'+n]);snapshot(p,n,i,0)
 while p.poll() is None:
  time.sleep(15);snapshot(p,n,i,time.time()-t)
 snapshot(p,n,i,time.time()-t)
 if p.returncode:
  (out/'v4-monitored-build-result.json').write_text(json.dumps({'passed':False,'module':n,'exit':p.returncode,'elapsed_seconds':time.time()-start})+'\n');sys.exit(p.returncode)
 print(f'MODULE_PASS {n} elapsed_seconds={time.time()-t:.1f}',flush=True)
p=subprocess.run(['lake','build'])
(out/'v4-monitored-build-result.json').write_text(json.dumps({'passed':p.returncode==0,'built_modules':len(order),'exit':p.returncode,'elapsed_seconds':time.time()-start})+'\n')
sys.exit(p.returncode)

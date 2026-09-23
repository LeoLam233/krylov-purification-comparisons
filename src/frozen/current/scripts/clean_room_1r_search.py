"""Independent short-time 1R search; no handoff frontier lead is read."""
import json
from fractions import Fraction as F
from pathlib import Path
out=[]
for N in range(3,45):
 for a in range(1,N-1):
  for b in range(1,N-a):
   c=N-a-b
   p,q,r=F(a,N),F(b,N),F(c,N); P=p*p+q*q+r*r
   gap=2*(p-q)**2/P-2*(p+q)
   if gap>0:
    out.append({'N':N,'eigenvalues':list(map(str,(p,q,r))),'purity':str(P),'H':'[[0,1,0],[1,0,0],[0,0,0]] in rho eigenbasis','CK_t2':str(2*(p-q)**2/P),'CKI_t2':str(2*(p+q)),'gap_t2':str(gap)})
 if out: break
p=Path(__file__).resolve().parents[1]
(p/'results/clean_room_1r_search.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))

"""Exact moment derivation, independent of numerical Lanczos implementations."""
from pathlib import Path
import sympy as s, json
ROOT=Path(__file__).resolve().parents[1]
x=s.Symbol('x'); v,w,u,z=s.symbols('v w u z',positive=True)
def moment_series(M):
    def E(p):
        pol=s.Poly(s.expand(p),x)
        return s.factor(sum(c*M.get(k[0],s.S.Zero) for k,c in pol.terms()))
    ps=[];hs=[]
    out={2:s.S.Zero,4:s.S.Zero,6:s.S.Zero,8:s.S.Zero}
    for n in range(5):
        p=x**n
        for q,h in zip(ps,hs): p=s.cancel(p-E(p*q)*q/h)
        p=s.factor(p);h=E(p*p)
        ps.append(p);hs.append(h)
        if n==0:continue
        # <p exp(-ixt)>; only terms through 8-n contribute to |.|^2.
        a={k:s.factor((-s.I)**k*E(p*x**k)/s.factorial(k)) for k in range(n,9-n)}
        for k in out:
            val=0
            for i in a:
                if k-i in a: val+=a[i]*s.conjugate(a[k-i])
            out[k]+=n*val/h
    return {k:s.factor(s.cancel(val)) for k,val in out.items()}
M={0:s.S.One,2:v,4:w,6:u,8:z}
D={0:s.S.One,2:2*v,4:2*w+6*v*v,6:2*u+30*v*w,8:2*z+56*u*v+70*w*w}
cs=moment_series(M);ck=moment_series(D)
gap={k:s.factor(s.cancel(ck[k]-2*cs[k])) for k in cs}
print('symmetric CS=',cs);print('pure operator CK=',ck);print('gap=',gap)
(ROOT/'results/short_time_symmetric.json').write_text(json.dumps({'moment_symbols':{'v':'m2','w':'m4','u':'m6','z':'m8'},'CS':{k:str(vv) for k,vv in cs.items()},'CK':{k:str(vv) for k,vv in ck.items()},'gap':{k:str(vv) for k,vv in gap.items()}},indent=2))

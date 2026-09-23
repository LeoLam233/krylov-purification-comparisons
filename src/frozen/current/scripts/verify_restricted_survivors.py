"""Independent exact checks of restricted replacements; not new central targets."""
from pathlib import Path
import json
import sympy as s
ROOT=Path(__file__).resolve().parents[1]
y,h,x=s.symbols('y h x',real=True)
a=(1-y)/2; b=(1-y*y)/(2-y*y)
muS=a*h;muK=b*h
assert s.factor(b-a)==s.factor(y*(1-y)*(y+2)/(2*(2-y*y)))
kappa=(1-a*h)/(1-b*h)
assert s.factor(s.diff(kappa,h)-(b-a)/(1-b*h)**2)==0
k=s.factor(kappa.subs(h,1));assert s.simplify(k-(1+y)*(2-y*y)/2)==0
ystar=(s.sqrt(7)-1)/3
kstar=s.simplify(k.subs(y,ystar));assert s.simplify(kstar-(17+7*s.sqrt(7))/27)==0
assert s.simplify(s.diff(k,y).subs(y,ystar))==0
# k''=-1-3y<0 for 0<=y<=1; k(0)=k(1)=1.
assert s.simplify(s.diff(k,y,2)+3*y+1)==0
u,kap=s.symbols('u kap',positive=True)
cv2=(kap-u)*(u-1)/u**2
uc=2*kap/(1+kap)
assert s.simplify(s.diff(cv2,u).subs(u,uc))==0
assert s.simplify(cv2.subs(u,uc)-(kap-1)**2/(4*kap))==0
bound=s.sqrt((kstar-1)**2/(4*kstar))

# A genuinely separate direct finite-state expansion checks the symmetric t^8
# moment formula on a TERMINATING three-point state chain (no formula imported).
t=s.Symbol('t',real=True)
G=s.diag(-1,0,1); psi=s.Matrix([1,s.sqrt(8),1])/s.sqrt(10)
L=s.kronecker_product(G,s.eye(3))-s.kronecker_product(s.eye(3),G)
seed=s.kronecker_product(psi,psi)
def basis(A,v):
    qs=[];hs=[]
    for n in range(A.rows):
        q=A**n*v
        for z,z2 in zip(qs,hs):q-=z*(z.adjoint()*q)[0]/z2
        q=q.applyfunc(s.simplify);norm=s.simplify((q.adjoint()*q)[0])
        if norm==0:break
        qs.append(q);hs.append(norm)
    return qs,hs
def seriesC(A,v):
    qs,hs=basis(A,v)
    ev=sum(((-s.I*t)**k/s.factorial(k)*(A**k)*v for k in range(9)),s.zeros(A.rows,1))
    z=0
    for n,(q,hh) in enumerate(zip(qs,hs)):
        amp=(q.adjoint()*ev)[0]
        z+=n*amp*s.conjugate(amp)/hh
    return s.series(s.expand(z),t,0,10).removeO().expand(),len(qs)
CS,ns=seriesC(G,psi);CK,nk=seriesC(L,seed)
gap=s.expand(CK-2*CS)
assert ns==3 and nk==5
for j in (0,2,4,6):assert gap.coeff(t,j)==0
assert gap.coeff(t,8)==s.Rational(3,2500)
v=w=u=s.Rational(1,5)
formula=(v*u-6*v**4+9*v*v*w-4*w*w)**2/(72*(w-v*v)*(w+v*v))
assert formula==gap.coeff(t,8)
out={'all_assertions_pass':True,'qubit_ratio_range_factor':str(kstar),
     'qubit_CV_upper_bound':str(bound),'qubit_CV_upper_bound_decimal':float(bound),
     'scope':'Nonstationary qubits; r,q and Pq; any probability-weighted time average, removable recurrence limits.',
     'classification':'T2-SURVIVES (restricted byproduct, not a new central attack statement)',
     'symmetric_terminated_example':{'state_chain':ns,'operator_chain':nk,'CS':str(CS),'CK':str(CK),
         't8_gap':str(gap.coeff(t,8)),'formula_agrees':True}}
(ROOT/'results/restricted_survivors.json').write_text(json.dumps(out,indent=2))
print('Exact qubit range and CV bound PASS:',kstar,float(bound))
print('Independent direct symmetric terminating-chain t^8 coefficient PASS:',gap.coeff(t,8))

"""Hostile cross-checks for the factor-two theorem and each purification branch.

The proof is the nested-flag argument in certificates/FACTOR_TWO_THEOREM.md.
This script verifies an exact flag instance, then uses direct vector/matrix
Lanczos, a separate spectral-polynomial implementation and covariance tests.
"""
from pathlib import Path
import json
import numpy as np
import sympy as S
from scipy.linalg import expm
from numeric_krylov import direct_state,direct_operator,state_measure,difference_measure,spectral_complexity
ROOT=Path(__file__).resolve().parents[1]

# Exact independent polynomial-flag test, including non-full joint cyclic space.
G=S.diag(0,1,3); a=S.Matrix([1,1,1]);
L=S.kronecker_product(G,S.eye(3))-S.kronecker_product(S.eye(3),G)
b=S.kronecker_product(a,a)
def basis(A,seed):
    out=[];norms=[];v=seed
    for n in range(A.rows):
        v=(A**n)*seed
        for q,h in zip(out,norms):v-=((q.adjoint()*v)[0]/h)*q
        v=v.applyfunc(S.factor);h=S.factor((v.adjoint()*v)[0])
        if h==0:break
        out.append(v);norms.append(h)
    return out,norms
V,h=basis(G,a);J,k=basis(L,b)
assert len(V)==3 and len(J)==7
Ps=[v*v.adjoint()/n for v,n in zip(V,h)]
Pj=[v*v.adjoint()/n for v,n in zip(J,k)]
Pcyc=sum(Pj,S.zeros(9)); Ns=sum((i*p for i,p in enumerate(Ps)),S.zeros(3))
Nop=sum((i*p for i,p in enumerate(Pj)),S.zeros(9))
Nsum=S.kronecker_product(Ns,S.eye(3))+S.kronecker_product(S.eye(3),Ns)
Ds=[]
for n in range(6):
    pn=sum(Pj[:n+1],S.zeros(9))
    wn=sum((S.kronecker_product(Ps[i],Ps[j]) for i in range(3) for j in range(3) if i+j<=n),S.zeros(9))
    assert wn*pn==pn and pn*wn==pn
    d=wn-pn
    assert d==d.adjoint() and d*d==d
    Ds.append(d)
assert Pcyc*(Nop-Nsum)*Pcyc==Pcyc*sum(Ds,S.zeros(9))*Pcyc

rng=np.random.default_rng(20260922)
records=[]
for d in (2,3,4):
    energies=np.array([0,1,3,7][:d],float)
    raw=rng.normal(size=(d,d))+1j*rng.normal(size=(d,d))
    rho=raw@raw.conj().T+np.eye(d)/3;rho/=np.trace(rho)
    H=np.diag(energies).astype(complex)
    er,Vr=np.linalg.eigh(rho);sqrt=(Vr*np.sqrt(er))@Vr.conj().T
    psi=sqrt.ravel()
    assert np.linalg.norm(sqrt@sqrt-rho)<1e-13 and abs(np.vdot(psi,psi)-1)<1e-13
    for name,G in [('I',np.kron(H,np.eye(d))),('U*',np.kron(H,np.eye(d))-np.kron(np.eye(d),H.conj()))]:
        R=np.outer(psi,psi.conj())
        assert abs(np.trace(R@R)-1)<1e-12
        x,w=state_measure(G,psi);y,z=difference_measure(x,w)
        for t in (.37,1.13,2.71):
            cs,ps,Qs,si=direct_state(G,psi.copy(),t)
            ck,pk,Qk,ki=direct_operator(G,R,t)
            cs2=spectral_complexity(x,w,t);ck2=spectral_complexity(y,z,t)
            assert abs(cs-cs2)<2e-7 and abs(ck-ck2)<2e-7
            assert ck-2*cs>=-2e-8
            # Exact physical purification evolved in subsystem representation.
            U=expm(-1j*t*H)
            physical=np.kron(U,np.eye(d) if name=='I' else U.conj())@psi
            assert np.linalg.norm(expm(-1j*t*G)@psi-physical)<2e-12
            # Tail stochastic domination: distribution of i+j from two copies.
            pc=np.convolve(ps,ps)
            nmax=max(len(pk),len(pc))
            tails_op=np.array([pk[n+1:].sum() for n in range(nmax)])
            tails_prod=np.array([pc[n+1:].sum() for n in range(nmax)])
            assert np.min(tails_op-tails_prod)>-2e-8
            records.append(dict(d=d,branch=name,t=t,CS=cs,CK=ck,gap=ck-2*cs,
                 spectral_error=max(abs(cs-cs2),abs(ck-ck2)),state=si,operator=ki,
                 min_tail_excess=float(np.min(tails_op-tails_prod))))
        # Common complex unitary change, including the conjugate ancilla.
        Z=rng.normal(size=(d,d))+1j*rng.normal(size=(d,d));W=np.linalg.qr(Z)[0]
        HH=W@H@W.conj().T;ss=W@sqrt@W.conj().T
        GG=np.kron(HH,np.eye(d)) if name=='I' else np.kron(HH,np.eye(d))-np.kron(np.eye(d),HH.conj())
        pp=ss.ravel();RR=np.outer(pp,pp.conj())
        cst=direct_state(G,psi.copy(),.81)[0];ckt=direct_operator(G,R,.81)[0]
        assert abs(direct_state(GG,pp.copy(),.81)[0]-cst)<2e-7
        assert abs(direct_operator(GG,RR,.81)[0]-ckt)<2e-7

# Pure states, no purification conventions needed: repeated and zero energies,
# complex seeds, two-point equal weights and zero variance.
edge=[]
for E,psi in [([0,0,0],[1,2j,3]),([0,1],[1,1]),([0,1],[1,2j]),([0,0,2],[1,1j,2]),([0,1,4],[1,0,0])]:
    G=np.diag(np.array(E,float));psi=np.array(psi,complex);psi/=np.linalg.norm(psi)
    R=np.outer(psi,psi.conj());cs=direct_state(G,psi.copy(),.71)[0];ck=direct_operator(G,R,.71)[0]
    assert ck-2*cs>=-2e-10
    edge.append({'E':E,'CS':cs,'CK':ck,'gap':ck-2*cs})

# Independent direct Taylor expansion for a skewed energy distribution.
# No use of derive_short_time.py or a symbolic moment-based Lanczos oracle.
G=S.diag(0,1,3);psi=S.Matrix([1,1,1])/S.sqrt(3)
vs,hs=basis(G,psi)
# Exact power-series amplitudes to order three suffice for t^4.
t=S.Symbol('t',real=True)
def series_C(A,seed,order):
    bs,ns=basis(A,seed);evo=sum(((-S.I*t)**k/S.factorial(k)*(A**k)*seed for k in range(order+1)),S.zeros(A.rows,1))
    ans=0
    for n,(v,h) in enumerate(zip(bs,ns)):
        amp=(v.adjoint()*evo)[0]
        ans+=n*amp*S.conjugate(amp)/h
    return S.series(S.expand(ans),t,0,order+1).removeO().expand()
big=S.kronecker_product(G,S.eye(3))-S.kronecker_product(S.eye(3),G)
cs=series_C(G,psi,4);ck=series_C(big,S.kronecker_product(psi,psi),4)
mean=(psi.adjoint()*G*psi)[0];Gc=G-mean*S.eye(3)
v=(psi.adjoint()*Gc**2*psi)[0];m3=(psi.adjoint()*Gc**3*psi)[0]
assert S.simplify((ck-2*cs).coeff(t,4)-m3*m3/(2*v))==0
out={'exact_flag_test':{'state_chain':3,'operator_chain':7,'joint_ambient_dimension':9,
     'all_nested_projector_checks_pass':True,'tail_operator_identity_pass':True},
     'branch_checks':records,'edge_checks':edge,'exact_short_time':{'CS':str(cs),'CK':str(ck),'m2':str(v),'m3':str(m3),'quartic_gap':str(S.simplify((ck-2*cs).coeff(t,4)))},
     'all_assertions_pass':True,'rng_seed':20260922}
(ROOT/'results/factor_two_verification.json').write_text(json.dumps(out,indent=2))
print('Exact nested projector and tail-operator identities: PASS')
print('Independent direct vs spectral branch checks:',len(records),'PASS')
print('Complex common-unitary covariance and degenerate/stationary cases: PASS')
print('Exact skewness-controlled quartic gap:',S.simplify((ck-2*cs).coeff(t,4)))

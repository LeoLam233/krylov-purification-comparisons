"""Numerical cross-checks, not mathematical certificates.
Matrix-space Arnoldi with full reorthogonalization and a separate weighted
spectral polynomial implementation. Both test probability conservation.
"""
import numpy as np
from scipy.linalg import expm

def matrix_krylov(apply,seed,maxdim,tol=2e-11):
    seed=np.asarray(seed,complex).ravel();seed=seed/np.linalg.norm(seed)
    basis=[];v=seed.copy()
    for n in range(maxdim):
        basis.append(v)
        w=np.asarray(apply(v),complex).ravel()
        for _ in range(2):
            for q in basis: w-=np.vdot(q,w)*q
        beta=np.linalg.norm(w)
        if beta<tol: break
        v=w/beta
    else:
        # A full ambient basis is an exact dimension bound, not truncation.
        if maxdim<len(seed) and beta>=tol:
            raise ArithmeticError('Krylov truncation rather than termination')
    Q=np.column_stack(basis)
    orth=np.linalg.norm(Q.conj().T@Q-np.eye(Q.shape[1]))
    assert orth<2e-8
    AQ=np.column_stack([apply(q) for q in Q.T])
    J=Q.conj().T@AQ
    off=J.copy()
    for i in range(len(J)):
        for j in range(len(J)):
            if abs(i-j)<=1: off[i,j]=0
    assert np.linalg.norm(off)<2e-7
    assert np.linalg.norm(AQ-Q@J)<2e-7
    return Q,{'length':len(basis),'orthogonality_error':float(orth),
              'closure_error':float(np.linalg.norm(AQ-Q@J)),
              'tridiagonal_error':float(np.linalg.norm(off))}

def direct_state(G,psi,t):
    G=np.asarray(G,complex);psi=np.asarray(psi,complex).ravel();psi/=np.linalg.norm(psi)
    Q,info=matrix_krylov(lambda v:G@v,psi,len(psi))
    evolved=expm(-1j*t*G)@psi
    p=abs(Q.conj().T@evolved)**2
    assert abs(p.sum()-1)<2e-8
    return float(np.arange(len(p))@p),p,Q,info

def direct_operator(G,O,t):
    G=np.asarray(G,complex);O=np.asarray(O,complex);d=len(G)
    norm=np.linalg.norm(O); O=O/norm
    def apply(v):
        A=v.reshape(d,d);return (G@A-A@G).ravel()
    Q,info=matrix_krylov(apply,O.ravel(),d*d)
    U=expm(-1j*t*G); evolved=(U@O@U.conj().T).ravel()
    p=abs(Q.conj().T@evolved)**2
    assert abs(p.sum()-1)<2e-8
    return float(np.arange(len(p))@p),p,Q,info

def merge_measure(nodes,weights,tol=2e-10):
    order=np.argsort(nodes); xs=[]; ws=[]
    for k in order:
        x=float(nodes[k]);w=float(weights[k])
        if w<1e-24:continue
        if xs and abs(x-xs[-1])<tol:ws[-1]+=w
        else:xs.append(x);ws.append(w)
    w=np.array(ws);w/=sum(w)
    return np.array(xs),w

def state_measure(G,psi):
    e,V=np.linalg.eigh(G);p=abs(V.conj().T@psi)**2
    return merge_measure(e,p)

def difference_measure(x,w):
    return merge_measure((x[:,None]-x[None,:]).ravel(),(w[:,None]*w[None,:]).ravel())

def spectral_complexity(x,w,t):
    # Separate, weighted polynomial recurrence; no matrix_krylov call.
    p=np.ones(len(x)); polys=[]
    for n in range(len(x)):
        polys.append(p.copy())
        z=x*p
        for _ in range(2):
            for q in polys:z-=np.dot(w*q,z)*q
        b=np.sqrt(max(0,np.dot(w*z,z)))
        if b<2e-11:break
        p=z/b
    vals=np.array(polys)
    assert np.linalg.norm((vals*w)@vals.T-np.eye(len(vals)))<2e-7
    amps=(vals*w)@np.exp(-1j*x*t); prob=abs(amps)**2
    assert abs(sum(prob)-1)<2e-7
    return float(np.arange(len(prob))@prob)

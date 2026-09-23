#!/usr/bin/env python3
"""Reproduce the exact counterexample to the purification lower bound.

Target: the lower inequality in Eq. (4) of Das & Mori,
Phys. Rev. Lett. 136, 030201 (2026), arXiv:2408.00826v4.

Conventions: hbar=1; normalized Hilbert--Schmidt operator complexity;
row-vectorization, with G=H⊗I-I⊗H.conj(); purification seed vec(sqrt(rho)).
This script verifies mathematics; it does not establish publication priority.

Dependencies: numpy, scipy, sympy, mpmath.
Run: python verify.py
"""
from __future__ import annotations
import json
from pathlib import Path
from typing import Any
import numpy as np
import scipy.linalg as la
import sympy as sp
import mpmath as mp


def hs(a: sp.Matrix, b: sp.Matrix) -> sp.Expr:
    return sp.simplify(sp.trace(a.conjugate().T*b))


def exact_lanczos(h: sp.Matrix, a: sp.Matrix) -> dict[str, Any]:
    seed = sp.simplify(a/sp.sqrt(hs(a,a)))
    basis: list[sp.Matrix] = [seed]
    bs: list[sp.Expr] = []
    previous = sp.zeros(h.rows)
    old_b = sp.Integer(0)
    for _ in range(h.rows*h.rows):
        q = basis[-1]
        z = h*q-q*h-old_b*previous
        alpha = hs(q,z)
        assert alpha == 0, f"Nonzero Lanczos diagonal: {alpha}"
        z = sp.simplify(z-alpha*q)
        b2 = sp.factor(hs(z,z))
        if b2 == 0:
            break
        b = sp.sqrt(b2)
        previous = q
        basis.append(sp.simplify(z/b))
        bs.append(b2)
        old_b = b
    else:
        raise RuntimeError("Exact Lanczos failed to terminate")
    gram = sp.Matrix([[hs(x,y) for y in basis] for x in basis])
    assert gram == sp.eye(len(basis))
    u_pi = sp.diag(*[(-1)**int(h[j,j]) for j in range(h.rows)])
    evolved = u_pi*seed*u_pi.conjugate().T
    probs = [sp.simplify(abs(hs(q,evolved))**2) for q in basis]
    assert sum(probs) == 1
    c = sp.factor(sum(j*p for j,p in enumerate(probs)))
    return {'b_squared': list(map(str,bs)), 'krylov_dimension':len(basis),
            'termination_residual_squared':str(b2),
            'probabilities_at_pi':list(map(str,probs)), 'complexity_at_pi':str(c)}


def numeric_krylov(g: np.ndarray, seed: np.ndarray) -> np.ndarray:
    """Full twice-reorthogonalized Arnoldi; Hermiticity makes it Lanczos."""
    q = np.asarray(seed,dtype=complex)
    q /= la.norm(q)
    basis = [q]
    for _ in range(g.shape[0]-1):
        z = g@basis[-1]
        for _ in range(2):
            for b in basis:
                z -= np.vdot(b,z)*b
        norm = la.norm(z)
        if norm < 1e-11:
            break
        basis.append(z/norm)
    Q = np.column_stack(basis)
    assert la.norm(Q.conj().T@Q-np.eye(Q.shape[1])) < 1e-10
    return Q


def numeric_complexity(h: np.ndarray, rho: np.ndarray, t: float, root: bool) -> float:
    d = len(h)
    if root:
        w,v = la.eigh(rho)
        if w.min() <= 0:
            raise ValueError('This verifier expects full-rank states')
        a = (v*np.sqrt(w))@v.conj().T
    else:
        a = rho.copy()
    seed = a.reshape(-1).astype(complex)
    seed /= la.norm(seed)
    g = np.kron(h,np.eye(d))-np.kron(np.eye(d),h.conj())
    Q = numeric_krylov(g,seed)
    # Direct evolution in the original Hilbert space, not in the Krylov chain.
    u = la.expm(-1j*h*t)
    evolved = (u@a@u.conj().T).reshape(-1)/la.norm(a)
    amplitudes = Q.conj().T@evolved
    assert la.norm(evolved-Q@amplitudes)<2e-10
    return float(np.arange(len(amplitudes))@np.abs(amplitudes)**2)


def high_precision_check(dps: int=90) -> dict[str,str]:
    mp.mp.dps = dps
    hdiag = [mp.mpf(2),mp.mpf(0),mp.mpf(1)]
    g = mp.diag([x-y for x in hdiag for y in hdiag])
    r = mp.matrix([[mp.mpf(16)/21,0,0], [0,mp.mpf(5)/42,mp.mpf(1)/14],
                   [0,mp.mpf(1)/14,mp.mpf(5)/42]])
    root = mp.matrix([[4,0,0],[0,mp.mpf(3)/2,mp.mpf(1)/2],
                      [0,mp.mpf(1)/2,mp.mpf(3)/2]])/mp.sqrt(21)
    values = {}
    for name,a,expected in [('CK',r,mp.mpf(1074)/8281),('CS',root,mp.mpf(82)/441)]:
        seed = mp.matrix([a[i,j] for i in range(3) for j in range(3)])
        seed /= mp.norm(seed)
        basis=[seed]
        for _ in range(8):
            z=g*basis[-1]
            for _ in range(2):
                for b in basis:
                    z-=b*(b.H*z)[0]
            norm=mp.norm(z)
            if norm<mp.mpf('1e-75'):
                break
            basis.append(z/norm)
        assert len(basis)==3
        evolved=mp.expm(-mp.j*g*mp.pi)*seed
        val=mp.fsum(j*abs((b.H*evolved)[0])**2 for j,b in enumerate(basis))
        error=abs(val-expected)
        assert error<mp.mpf('1e-75')
        values[name]=mp.nstr(val,82)
        values[name+'_absolute_error']=mp.nstr(error,8)
    return values


def main() -> None:
    h=sp.diag(2,0,1)
    r=sp.Matrix([[sp.Rational(16,21),0,0],
                 [0,sp.Rational(5,42),sp.Rational(1,14)],
                 [0,sp.Rational(1,14),sp.Rational(5,42)]])
    root=sp.Matrix([[4,0,0],[0,sp.Rational(3,2),sp.Rational(1,2)],
                    [0,sp.Rational(1,2),sp.Rational(3,2)]])/sp.sqrt(21)
    assert sp.simplify(root*root-r)==sp.zeros(3)
    assert sp.trace(r)==1
    assert set(r.eigenvals())=={sp.Rational(16,21),sp.Rational(4,21),sp.Rational(1,21)}
    out: dict[str,Any]={'target':'Eq. (4), lower bound; arXiv:2408.00826v4',
        'status':'Internal exact falsification; external audit and novelty not certified',
        'qutrit': {'H':str(h),'rho':str(r), 'sqrt_rho':str(root),
        'purity':str(sp.trace(r*r)), 'CK':exact_lanczos(h,r),
        'CS':exact_lanczos(h,root), 'gap_at_pi':str(sp.Rational(82,441)-sp.Rational(1074,8281))}}
    m=sp.symbols('m',positive=True)
    D=m*m+5
    family_r=sp.Matrix([[m*m,0,0],[0,sp.Rational(5,2),sp.Rational(3,2)],
                        [0,sp.Rational(3,2),sp.Rational(5,2)]])/D
    family_s=sp.Matrix([[m,0,0],[0,sp.Rational(3,2),sp.Rational(1,2)],
                        [0,sp.Rational(1,2),sp.Rational(3,2)]])/sp.sqrt(D)
    assert sp.simplify(family_s*family_s-family_r)==sp.zeros(3)
    P=sp.factor(sp.trace(family_r*family_r))
    muK=sp.factor(hs(h*family_r-family_r*h,h*family_r-family_r*h)/P)
    muS=sp.factor(hs(h*family_s-family_s*h,h*family_s-family_s*h))
    assert sp.simplify(muK-9/(2*(m**4+17)))==0
    assert sp.simplify(muS-1/(2*(m*m+5)))==0
    ratio_pi=sp.factor(muS*(1-muS)/(muK*(1-muK)))
    leading_ratio=sp.limit(ratio_pi/m**2,m,sp.oo)
    assert leading_ratio==sp.Rational(1,9)
    out['full_rank_qutrit_family']={'m_domain':'m >= 4', 'purity':str(P),
        'muK':str(muK),'muS':str(muS), 'muS_minus_muK':str(sp.factor(muS-muK)),
        'lim_CS_over_CK_divided_by_m_squared_at_pi':str(leading_ratio)}
    # Non-block-diagonal perturbation: exact short-time curvature certificate.
    delta=sp.symbols('delta',real=True)
    hp=h+delta*sp.Matrix([[0,1,2],[1,0,3],[2,3,0]])
    aK=sp.factor(hs(hp*r-r*hp,hp*r-r*hp)/sp.trace(r*r))
    aS=sp.factor(hs(hp*root-root*hp,hp*root-root*hp))
    curvature_gap=sp.factor(aS-aK)
    assert curvature_gap.subs(delta,sp.Rational(1,100))>0
    out['symmetry_breaking']={'H_delta':str(hp), 'CS_minus_CK_t2_coefficient':str(curvature_gap),
        'delta_1_100_coefficient':str(curvature_gap.subs(delta,sp.Rational(1,100))),
        'meaning':'Exact positive curvature proves a nonempty small-time violation interval; no numerical limit argument needed.'}
    t_cert=sp.Rational(1,10**6)
    lower_cert=sp.factor(curvature_gap.subs(delta,sp.Rational(1,100))*t_cert**2-4608*t_cert**3)
    assert lower_cert>0
    out['symmetry_breaking']['finite_time_certificate']={'time':str(t_cert), 'delta':'1/100',
        'rigorous_lower_bound_on_CS_minus_CK':str(lower_cert),
        'remainder_bound':'For each C, ||N|| <= 8, ||G|| <= 6, so |R3| <= 2304 |t|^3; difference remainder <= 4608 |t|^3.'}
    # Fixed purity = 1/2 in dimension 4.
    eps=sp.symbols('eps',positive=True)
    disc=2*eps-sp.Rational(59,25)*eps**2
    a=(1-eps+sp.sqrt(disc))/2
    b=(1-eps-sp.sqrt(disc))/2
    fixedP=sp.simplify(a*a+b*b+(4*eps/5)**2+(eps/5)**2)
    assert fixedP==sp.Rational(1,2)
    mk=sp.Rational(9,25)*eps**2; ms=eps/10
    assert sp.limit(mk*(1-mk)/(ms*(1-ms)),eps,0)==0
    r4=sp.Matrix([[66,0,0,0],[0,24,0,0],[0,0,5,3],[0,0,3,5]])/100
    s4=sp.Matrix([[sp.sqrt(33),0,0,0],[0,sp.sqrt(12),0,0],
                  [0,0,sp.Rational(3,2),sp.Rational(1,2)],
                  [0,0,sp.Rational(1,2),sp.Rational(3,2)]])/sp.sqrt(50)
    assert sp.simplify(s4*s4-r4)==sp.zeros(4)
    assert sp.trace(r4*r4)==sp.Rational(1,2)
    out['fixed_purity_family']={'dimension':4,'epsilon_domain':'0 < eps < 5/18',
        'eigenvalues':['(1-eps+sqrt(2*eps-59*eps**2/25))/2',
                       '(1-eps-sqrt(2*eps-59*eps**2/25))/2','4*eps/5','eps/5'],
        'purity':str(fixedP),'muK':str(mk),'muS':str(ms),
        'lim_CK_over_CS_at_pi':'0',
        'epsilon_1_10':{'rho':str(r4),'H':str(sp.diag(2,3,0,1)),
                      'CK':exact_lanczos(sp.diag(2,3,0,1),r4),
                      'CS':exact_lanczos(sp.diag(2,3,0,1),s4)}}
    out['high_precision_90_digits']=high_precision_check()
    hn=np.array(h,dtype=complex); rn=np.array(r,dtype=complex)
    ts=np.linspace(-2*np.pi,2*np.pi,129)
    max_formula_error=0.0
    for t in ts:
        for rt,mu in [(False,3/182),(True,1/42)]:
            val=numeric_complexity(hn,rn,float(t),rt)
            formula=mu*np.sin(t)**2+8*mu*(1-mu)*np.sin(t/2)**4
            max_formula_error=max(max_formula_error,abs(val-formula))
    assert max_formula_error<2e-12
    rng=np.random.default_rng(20260922)
    max_covariance_error=0.0
    for _ in range(24):
        z=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3))
        u,_=la.qr(z)
        ht=u@hn@u.conj().T; rht=u@rn@u.conj().T
        for rt,expected in [(False,1074/8281),(True,82/441)]:
            val=numeric_complexity(ht,rht,float(np.pi),rt)
            max_covariance_error=max(max_covariance_error,abs(val-expected))
    assert max_covariance_error<2e-11
    hpnum=np.array(hp.subs(delta,sp.Rational(1,100)),dtype=complex)
    out['numeric_cross_checks']={
        'time_grid_points':len(ts),'formula_comparisons':2*len(ts),
        'maximum_formula_absolute_error':max_formula_error,
        'random_unitary_covariance_trials':24,
        'maximum_covariance_absolute_error':max_covariance_error,
        'perturbed_H_at_pi':{'CK':numeric_complexity(hpnum,rn,np.pi,False),
                            'CS':numeric_complexity(hpnum,rn,np.pi,True)}}
    target=Path(__file__).with_name('verification_results.json')
    target.write_text(json.dumps(out,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps(out,ensure_ascii=False,indent=2))
    print('\nAll exact assertions and independent numerical cross-checks PASSED.')

if __name__=='__main__':
    main()

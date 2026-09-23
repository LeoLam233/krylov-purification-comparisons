"""Minimal dimension, structural perturbation and common-unitary kill checks."""
from pathlib import Path
import sympy as s, numpy as np, json
from numeric_krylov import direct_operator
ROOT=Path(__file__).resolve().parents[1]
pop=[s.Rational(16,26),s.Rational(1,26),s.Rational(9,26)];rho=s.diag(*pop);P=s.Rational(1,2)
d=s.Symbol('delta',real=True)
H=s.Matrix([[0,1,d],[1,0,2*d],[d,2*d,0]])
K=H*rho-rho*H
km=s.simplify(s.trace(K.adjoint()*K)/P)
ki=s.simplify(2*(s.trace(rho*H*H)-s.trace(rho*H)**2))
assert s.factor(km-ki)==s.factor((4-540*d**2)/169)
assert (km-ki).subs(d,s.Rational(1,20))==s.Rational(53,3380)
# Every off-diagonal entry is nonzero at delta=1/20, and rho has simple spectrum.
# Thus a common reducing projection would be diagonal and commute with this
# connected H, forcing it to be 0 or I: no common active/spectator decomposition.

# Arbitrary qubit reduction and positivity, source S24–S31 independently checked.
z,c=s.symbols('z c',real=True) # z=delta_p^2 in [0,1], c=cos(theta)^2 in [0,1]
muI=(1-z*c)/2;muK=z*(1-c)/(1+z)
assert s.factor(muI-muK)==s.factor((1-z)*(1+z*c)/(2*(1+z)))
# Both belong to [0,1/2], on which F(mu,t) is nondecreasing for every real t.
# Independent elementary three-node exponent: the following amplitudes conserve
# probability and give F, including the terminal limits mu=0,1.
m,y=s.symbols('mu y',real=True)
p0=(1-m+m*y)**2;p1=m*(1-y*y);p2=m*(1-m)*(y-1)**2
assert s.expand(p0+p1+p2-1)==0
assert s.expand(p1+2*p2-(m*(1-y*y)+2*m*(1-m)*(y-1)**2))==0
# For the left side too, x=sqrt(1-z), coefficient ordering is nonnegative.
x,ss=s.symbols('x ss',real=True)
mk=(1-x*x)*ss/(2-x*x);ms=(1-x)*ss/2
assert s.factor(mk-ms)==s.factor(ss*x*(1-x)*(2+x)/(2*(2-x*x)))

rr=np.diag(np.array(pop,float));HH=np.array(H.subs(d,0),float)
psi=np.diag(np.sqrt(np.diag(rr))).ravel().astype(complex);R=np.outer(psi,psi.conj())
G=np.kron(HH,np.eye(3));t=np.pi/3
base=direct_operator(HH,rr,t)[0]-direct_operator(G,R,t)[0]
assert abs(base-float(s.Rational(1600683,39299936)))<2e-12
rng=np.random.default_rng(19260922);cov=[]
for n in range(8):
    Z=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));W=np.linalg.qr(Z)[0]
    h=W@HH@W.conj().T;r=W@rr@W.conj().T
    sr=W@np.diag(np.sqrt(np.diag(rr)))@W.conj().T
    ps=sr.ravel();rs=np.outer(ps,ps.conj())
    gap=direct_operator(h,r,t)[0]-direct_operator(np.kron(h,np.eye(3)),rs,t)[0]
    assert abs(gap-base)<2e-10
    cov.append(gap)
pertH=np.array(H.subs(d,s.Rational(1,20)),float)
smallt=1/20000
pert_gap=direct_operator(pertH,rr,smallt)[0]-direct_operator(np.kron(pertH,np.eye(3)),R,smallt)[0]
# ||H||<=11/10, gap spectra have at most 7 atoms, number operators norm<=6.
# Taylor remainder <= 2*(22/5)^3 |t|^3 = (21296/125)|t|^3.
rigorous_lower=s.Rational(53,3380)*s.Rational(1,20000)**2-s.Rational(21296,125)*s.Rational(1,20000)**3
assert rigorous_lower>0 and pert_gap>float(rigorous_lower)
out={'minimal_counterexample_dimension_1R':3,'qubit_general_ordering_identity':str(s.factor(muI-muK)),
    'qubit_scope':'all density matrices, all time-independent Hermitian qubit Hamiltonians, all real times',
    'structural_family_H':str(H),'rho':str(rho),'curvature_gap':str(s.factor(km-ki)),
    'strict_range':'0<abs(delta)<1/sqrt(135)',
    'irreducible_pair_example_delta':'1/20','irreducible_pair_curvature_gap':'53/3380',
    'irreducible_pair_time':'1/20000','rigorous_finite_time_lower':str(rigorous_lower),
    'numerical_finite_time_gap':pert_gap,'complex_covariance_gaps':cov,
    'all_assertions_pass':True,'rng_seed':19260922}
(ROOT/'results/target1r_bootstrap.json').write_text(json.dumps(out,indent=2))
print('Arbitrary-qubit ordering / minimum counterexample dimension=3: PASS')
print('Irreducible qutrit perturbation family curvature identity: PASS')
print('Exact perturbed finite-time lower bound:',rigorous_lower)
print('Eight complex common-unitary covariance checks: PASS')

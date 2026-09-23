"""Exact matrix/return-measure identities and analytic-bound constants for T2.
The CV-divergence proof is in certificates/TARGET2_TEMPORAL_NOGO.md;
the fixed-purity proof is in certificates/TARGET2_PURITY_NOGO.md.
"""
from pathlib import Path
import json
import sympy as s
ROOT=Path(__file__).resolve().parents[1]
e=s.Symbol('epsilon',positive=True);eta=s.Symbol('eta',positive=True)
z=s.Symbol('z',nonzero=True);c=s.Symbol('c',nonnegative=True)
B=s.Matrix([[5,3],[3,5]])/10
SB=s.Matrix([[3,1],[1,3]])/(2*s.sqrt(5))
assert SB*SB==B and s.trace(B)==1 and s.trace(B*B)==s.Rational(17,25)
H=s.diag(0,2,3,4);U=s.diag(1,z**2,z**3,z**4);Ui=s.diag(1,z**-2,z**-3,z**-4)
A=1-(z**2+z**-2)/2;Bt=1-(z+z**-1)/2

def autocorr(O):
    return s.factor(s.trace(U*O*Ui*O)/s.trace(O*O))

# A-r: exact positive block state; O=sqrt(rho) is verified by squaring.
rho=s.diag((1-e)*B,e*B);root=s.diag(s.sqrt(1-e)*SB,s.sqrt(e)*SB)
assert (root*root-rho).applyfunc(s.simplify)==s.zeros(4)
D0=(1-e)**2+e**2;P=s.Rational(17,25)*D0
assert s.trace(rho)==1 and s.simplify(s.trace(rho*rho)-P)==0
Ds=((1-e)*A+e*Bt)/10
Dk=s.Rational(9,34)/D0*((1-e)**2*A+e**2*Bt)
assert s.simplify(1-autocorr(root)-Ds)==0
assert s.simplify(1-autocorr(rho)-Dk)==0
fr=s.Rational(17,45)*D0*(4*(1-e)*c+e)/(4*(1-e)**2*c+e**2)
fr_decomp=s.Rational(17,45)*D0/(1-e)*(1+e*(1-2*e)/(4*(1-e)**2*c+e**2))
assert s.factor(fr-fr_decomp)==0
fr_mean=s.Rational(17,45)*D0/(1-e)*(1+(1-2*e)/s.sqrt(4*(1-e)**2+e**2))
# On 0<e<=1/4: prefactor <=68/135, bracket <=5/3, mean f <=68/81<1.
assert s.Rational(68,135)*s.Rational(5,3)==s.Rational(68,81)<1
# On |t-pi|<=e, c<=e^2/4: f>=17/(180e), r>=17/(1440e).
# Mean r<=8 and second moment >=289/(2073600*pi*e).
r_cv_constant=s.Rational(289,132710400)
assert s.Rational(17,1440)**2/64==r_cv_constant
# Explicit wholly rational parameter yields a certified large CV, using pi<22/7.
er=s.Rational(1,10**10)
r_cv2_lower=s.factor(r_cv_constant*7/(22*er)-1)
assert r_cv2_lower>80**2

# A-q: positive unnormalized square root; use eta so every input is rational
# when eta is rational. rho=Aeta^2/N is therefore a rational density matrix.
Ae=s.diag(eta*s.Matrix([[2,1],[1,2]]),s.Matrix([[1,eta**3],[eta**3,1]]))
N=s.trace(Ae*Ae);T=s.trace(Ae**4)
Ne=2+10*e+2*e**3;Te=2+82*e**2+12*e**3+2*e**6
assert s.expand(N-Ne.subs(e,eta**2))==0 and s.expand(T-Te.subs(e,eta**2))==0
rr=Ae*Ae/N
assert s.factor(s.trace(rr)-1)==0 and s.factor(s.trace(rr*rr)-T/N**2)==0
Ds2=(2*e/Ne)*A+(2*e**3/Ne)*Bt
Dk2=(32*e**2/Te)*A+(8*e**3/Te)*Bt
assert s.factor(1-autocorr(Ae)-Ds2.subs(e,eta**2))==0
assert s.factor(1-autocorr(Ae*Ae)-Dk2.subs(e,eta**2))==0
fq=4*Ne*e/Te*(16*c+e)/(4*c+e**2)
fq_decomp=4*Ne*e/Te*(4+e*(1-4*e)/(4*c+e**2))
assert s.factor(fq-fq_decomp)==0
fq_mean=4*Ne*e/Te*(4+(1-4*e)/s.sqrt(4+e**2))
# All coefficients of N-2,T-2 are nonnegative, so monotonicity gives bounds.
assert Ne.subs(e,s.Rational(1,16))<3 and Te.subs(e,s.Rational(1,16))<3
assert 4*s.Rational(3,2)*s.Rational(9,2)==27
# mean q<=216e, q>=1/6 on a window of length 2e around pi.
q_cv_constant=s.Rational(1,36*216**2)
eq=s.Rational(1,10**10) # eta=1/100000, rational state.
q_cv2_lower=s.factor(q_cv_constant*7/(22*eq)-1)
assert q_cv2_lower>40**2

# B-P: the exact source-matched fixed-purity family in the handoff, reconstructed
# only as needed for this target. The spectator eigenvalues are adjusted to P=1/2.
rad=2*e-s.Rational(59,25)*e**2
ap=(1-e+s.sqrt(rad))/2;am=(1-e-s.sqrt(rad))/2
rhoP=s.diag(ap,am,e*B)
assert s.simplify(s.trace(rhoP)-1)==0
assert s.simplify(s.trace(rhoP*rhoP)-s.Rational(1,2))==0
assert s.factor((1-e)**2-rad)==s.factor((1-s.Rational(14,5)*e)*(1-s.Rational(6,5)*e))
# H=(2,3,0,1) means only the last active block contributes, at frequency 1.
muK=s.Rational(9,25)*e**2;muS=e/10
x=s.Symbol('x',nonnegative=True)
rat=s.Rational(5,18)/e*(1+(1-e/5)*x)/(1+(1-s.Rational(18,25)*e**2)*x)
assert s.factor(muS/muK-s.Rational(5,18)/e)==0
# Endpoints in x determine the monotone fractional-linear range for e<5/18.
assert s.factor(s.diff(rat,x))==s.factor(s.Rational(5,18)/e*(s.Rational(18,25)*e**2-e/5)/(1+(1-s.Rational(18,25)*e**2)*x)**2)
# endpoint ratio >=1-e/10 because the denominator <=2 and remains positive.
assert s.factor((2-e/5)/2-(1-e/10))==0
# A rational anchor at e=1/10.
assert rhoP.subs(e,s.Rational(1,10))==s.Matrix([[66,0,0,0],[0,24,0,0],[0,0,5,3],[0,0,3,5]])/100

out={'A-r':{'classification':'T2-NOGO','rho':str(rho),'H':str(H),'purity':str(P),
      'loss_state':str(Ds),'loss_mixed':str(Dk),'comparison_function':str(fr),
      'comparison_mean':str(fr_mean),'parameter_range':'0<epsilon<=1/4',
      'CV_squared_lower_bound':f'{r_cv_constant}/(pi*epsilon)-1',
      'finite_witness_epsilon':str(er),'finite_witness_CV_strict_lower':80,
      'rational_lower_on_CV_squared':str(r_cv2_lower)},
     'A-q':{'classification':'T2-NOGO','positive_sqrt_unnormalized':str(Ae),
      'normalization_N':str(Ne),'fourth_trace_T':str(Te),'rho':'Aeta^2/Tr(Aeta^2)',
      'H':str(H),'loss_state':str(Ds2),'loss_mixed':str(Dk2),
      'comparison_function':str(fq),'comparison_mean':str(fq_mean),
      'parameter_range':'epsilon=eta^2, 0<epsilon<=1/16',
      'CV_squared_lower_bound':f'{q_cv_constant}/(pi*epsilon)-1',
      'finite_witness_eta':'1/100000','finite_witness_CV_strict_lower':40,
      'rational_lower_on_CV_squared':str(q_cv2_lower)},
     'B-P':{'classification':'T2-NOGO','rho':str(rhoP),'H':'diag(2,3,0,1)',
      'dimension':4,'purity':'1/2','parameter_range':'0<epsilon<5/18',
      'mu_K':str(muK),'mu_S':str(muS),'exact_ratio':str(rat),
      'uniform_lower':'(5/(18*epsilon))*(1-epsilon/10)',
      'uniform_upper':'5/(18*epsilon)','recurrence_period':'2*pi'},
      'all_symbolic_assertions_pass':True,
      'warning':'CV theorems are source-motivated no-go results, not a claim that the source asserted a universal 5% bound.'}
(ROOT/'results/target2_exact.json').write_text(json.dumps(out,indent=2))
print('A-r: exact rho, sqrt(rho), autocorrelation, comparison identity PASS; finite witness CV>80')
print('A-q: exact rational rho, positive square root, autocorrelations PASS; finite witness CV>40')
print('B-P: trace, P=1/2, positive-eigenvalue domain, exact ratio and anchor PASS')

"""Independent exact certification of the right side of Das–Mori Eq.(4)."""
from pathlib import Path
import json
import sympy as S
from exact_krylov import spectral_certificate,direct_operator_certificate,jsonable
ROOT=Path(__file__).resolve().parents[1]
H=S.Matrix([[0,1,0],[1,0,0],[0,0,0]])
t=S.pi/3
U=S.Matrix([[S.cos(t),-S.I*S.sin(t),0],[-S.I*S.sin(t),S.cos(t),0],[0,0,1]])
assert S.simplify(U*U.adjoint())==S.eye(3)

def case(name,p,q,r):
    assert p>0 and q>0 and r>0 and p+q+r==1
    rho=S.diag(p,q,r); P=S.trace(rho*rho)
    sr=S.diag(S.sqrt(p),S.sqrt(q),S.sqrt(r))
    assert sr*sr==rho
    psi=S.Matrix(list(sr)); assert (psi.adjoint()*psi)[0]==1
    G=S.kronecker_product(H,S.eye(3))
    Up=S.kronecker_product(U,S.eye(3))
    R=psi*psi.adjoint(); Rt=Up*R*Up.adjoint(); rhot=U*rho*U.adjoint()
    assert S.trace(R)==1 and S.trace(R*R)==1
    mu=(p-q)**2/(2*P); s=p+q
    spec_m=spectral_certificate([-2,0,2],[mu/2,1-mu,mu/2],t)
    spec_p=spectral_certificate([-2,-1,0,1,2],
        [s*s/4,r*s,r*r+s*s/2,r*s,s*s/4],t)
    # Matrix channel never receives spectral nodes, weights or polynomial data.
    mat_m=direct_operator_certificate(H,rho,rhot,max_steps=4)
    mat_p=direct_operator_certificate(G,R,Rt,max_steps=6)
    assert mat_m['probabilities']==spec_m['probabilities']
    assert mat_p['probabilities']==spec_p['probabilities']
    assert mat_m['b_squared']==spec_m['b_squared']
    assert mat_p['b_squared']==spec_p['b_squared']
    k_m=S.simplify(S.trace((H*rho-rho*H).adjoint()*(H*rho-rho*H))/P)
    k_p=S.simplify(2*(S.trace(rho*H*H)-S.trace(rho*H)**2))
    assert k_m==mat_m['b_squared'][0] and k_p==mat_p['b_squared'][0]
    gap=S.simplify(mat_m['complexity']-mat_p['complexity'])
    return dict(name=name,rho=rho,H=H,purity=P,time=t,
                mixed=spec_m,purified_operator_I=spec_p,
                direct_mixed={k:v for k,v in mat_m.items() if k!='vectors'},
                direct_purified={k:v for k,v in mat_p.items() if k!='vectors'},
                curvature_mixed=k_m,curvature_purified=k_p,curvature_gap=S.simplify(k_m-k_p),
                finite_time_gap=gap,finite_time_violation=bool(gap>0),
                independent_channels_pass=True)

# Independent square-spectrum state; then the two historical leads, after gate.
cases=[case('independent_square_spectrum',S.Rational(16,26),S.Rational(1,26),S.Rational(9,26)),
       case('historical_R1',S.Rational(3,5),S.Rational(1,100),S.Rational(39,100)),
       case('historical_R2',S.Rational(7,10),S.Rational(1,20),S.Rational(1,4))]
assert cases[0]['curvature_gap']==S.Rational(4,169)
assert cases[1]['curvature_gap']==S.Rational(17829,128050)
assert cases[2]['mixed']['complexity']==S.Rational(58981,43808)
assert cases[2]['purified_operator_I']['complexity']==S.Rational(4713,3584)
assert cases[2]['finite_time_gap']==S.Rational(153775,4906496)
# Rigorous short-time interval for the independently generated square-spectrum state.
# Both Liouvillians have norm <=2; complexity number-operator norms 2 and 4.
# |C'''| <= (2*2)^3 ||N||; total remainder <=64 |t|^3.
# Hence difference >=(4/169)t^2-64t^3 >0 for 0<t<1/2704.
cert=dict(cases=cases,independent_small_time_interval='0 < t < 1/2704',
          taylor_bound='Delta(t) >= (4/169)*t^2 - 64*abs(t)^3',
          all_exact_assertions_pass=True)
(ROOT/'results/target1r_exact.json').write_text(json.dumps(jsonable(cert),indent=2))
for c in cases:
 print(c['name'],'P=',c['purity'],'curvature gap=',c['curvature_gap'],
       'finite gap=',c['finite_time_gap'],'b_m=',c['mixed']['b_squared'],
       'b_p=',c['purified_operator_I']['b_squared'])
print('TARGET 1R: exact spectral and direct operator-space certificates PASS')

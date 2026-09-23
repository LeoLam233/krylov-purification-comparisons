"""Independent full-matrix checks and exact-polynomial quadrature illustrations.
The proofs do NOT depend on these numerical averages.
"""
from pathlib import Path
import json, math
import numpy as np
import sympy as s
import mpmath as mp
from scipy.integrate import quad
from numeric_krylov import direct_state,direct_operator
from exact_krylov import spectral_certificate
ROOT=Path(__file__).resolve().parents[1]
H=np.diag([0.,2.,3.,4.]);B=np.array([[5.,3.],[3.,5.]])/10
SB=np.array([[3.,1.],[1.,3.]])/(2*np.sqrt(5))

def block(A,B):
    out=np.zeros((len(A)+len(B),len(A)+len(B)))
    out[:len(A),:len(A)]=A;out[len(A):,len(A):]=B
    return out

def reduced_poly(a,b):
    """C(t)/(1-c) exactly, c=cos(t/2)^2, for weights at 0,+-1,+-2.

    All cancellations, including the common recurrence zero, are exact before
    conversion to floating point. Orthogonal polynomials are generated anew.
    """
    cert=spectral_certificate([-2,-1,0,1,2],[b/2,a/2,1-a-b,a/2,b/2],s.pi/3)
    xx=s.Symbol('x',real=True);c=s.Symbol('c',real=True);y=2*c-1
    C=0
    for n,(p,h) in enumerate(zip(cert['polynomials'],cert['norms'])):
        if n==0:continue
        if n%2:
            amp=a*p.subs(xx,1)+2*b*p.subs(xx,2)*y
            C+=n*(1-y*y)*amp**2/h
        else:
            amp=(1-a-b)*p.subs(xx,0)+a*p.subs(xx,1)*y+b*p.subs(xx,2)*(2*y*y-1)
            C+=n*amp**2/h
    pol=s.Poly(s.cancel(C/(1-c)),c)
    assert pol.degree()<=3
    assert s.simplify(pol.eval(1)-4*(a+4*b))==0
    coef=np.array([float(k) for k in pol.all_coeffs()])
    return pol,coef

records=[];poly_records=[]
for fam in ('r','q'):
    for es in (s.Rational(1,100),s.Rational(1,1000)):
        e=float(es)
        if fam=='r':
            rho=block((1-e)*B,e*B);root=block(np.sqrt(1-e)*SB,np.sqrt(e)*SB)
            D0=(1-es)**2+es**2
            aS=es/10;bS=(1-es)/10
            aK=s.Rational(9,34)*es**2/D0;bK=s.Rational(9,34)*(1-es)**2/D0
        else:
            eta=np.sqrt(e);A=block(eta*np.array([[2.,1.],[1.,2.]]),np.array([[1.,eta**3],[eta**3,1.]]))
            root=A/np.linalg.norm(A);rho=root@root
            N=2+10*es+2*es**3;T=2+82*es**2+12*es**3+2*es**6
            aS=2*es**3/N;bS=2*es/N
            aK=8*es**3/T;bK=32*es**2/T
        pS,cS=reduced_poly(aS,bS);pK,cK=reduced_poly(aK,bK)
        assert np.min(np.linalg.eigvalsh(rho))>0
        assert abs(np.trace(rho)-1)<2e-14 and np.linalg.norm(root@root-rho)<2e-14
        G=np.kron(H,np.eye(4))-np.kron(np.eye(4),H)
        for t in (.37,1.13,math.pi,math.pi+e,2*math.pi-.19):
            cs=direct_state(G,root.astype(complex).ravel(),t)[0]
            # A third representation: sqrt(rho) as a normalized matrix under [H,.].
            css=direct_operator(H,root,t)[0]
            ck=direct_operator(H,rho,t)[0]
            c=np.cos(t/2)**2
            cs_poly=(1-c)*np.polyval(cS,c);ck_poly=(1-c)*np.polyval(cK,c)
            scale=max(1e-15,cs,ck)
            assert abs(cs-css)<1e-9*scale+1e-13
            assert abs(cs-cs_poly)<2e-8*scale+1e-13
            assert abs(ck-ck_poly)<2e-8*scale+1e-13
            # Explicit normalized matrix autocorrelations, independent of Krylov.
            U=np.diag(np.exp(-1j*np.diag(H)*t))
            Ak=np.trace((U@rho@U.conj().T)@rho).real/np.trace(rho@rho)
            As=np.trace((U@root@U.conj().T)@root).real
            Ds=float(aS)*(1-np.cos(t))+float(bS)*(1-np.cos(2*t))
            Dk=float(aK)*(1-np.cos(t))+float(bK)*(1-np.cos(2*t))
            assert abs(1-As-Ds)<2e-14 and abs(1-Ak-Dk)<2e-14
            assert Ds<=cs+1e-12 and cs<=8*Ds+1e-12
            assert Dk<=ck+1e-12 and ck<=8*Dk+1e-12
            records.append({'family':fam,'epsilon':str(es),'t':t,'CS':cs,'CK':ck,
                'r':cs/ck,'q':ck/cs,'relative_poly_error':max(abs(cs-cs_poly),abs(ck-ck_poly))/scale})
        poly_records.append({'family':fam,'epsilon':str(es),'CS_reduced_poly':str(pS.as_expr()),'CK_reduced_poly':str(pK.as_expr())})

# Fixed-P family: source-defined state and operator calculations, not just the ratio formula.
purity_checks=[]
HP=np.diag([2.,3.,0.,1.]);GP=np.kron(HP,np.eye(4))-np.kron(np.eye(4),HP)
for e in (.1,.02,.002):
    rad=2*e-59*e*e/25;ap=(1-e+np.sqrt(rad))/2;am=(1-e-np.sqrt(rad))/2
    rho=block(np.diag([ap,am]),e*B);root=block(np.diag(np.sqrt([ap,am])),np.sqrt(e)*SB)
    assert abs(np.trace(rho@rho)-.5)<2e-14
    for t in (.31,1.3,math.pi,5.5):
        cs=direct_state(GP,root.astype(complex).ravel(),t)[0];ck=direct_operator(HP,rho,t)[0]
        xx=np.sin(t/2)**2
        exact_ratio=(5/(18*e))*(1+(1-e/5)*xx)/(1+(1-18*e*e/25)*xx)
        assert abs(cs/ck/exact_ratio-1)<2e-9
        purity_checks.append({'epsilon':e,'t':t,'P':float(np.trace(rho@rho)),'r_direct':cs/ck,'r_formula':exact_ratio})

# CV quadrature from exact reduced cubic polynomials. Symmetry about t=pi lets
# us integrate u=|t-pi|, using c=sin(u/2)^2 without subtraction near pi.
cv=[]
for fam in ('r','q'):
    for es in [s.Rational(1,100),s.Rational(1,1000),s.Rational(1,10000),s.Rational(1,10**6),s.Rational(1,10**10)]:
        e=float(es)
        if fam=='r':
            D0=(1-es)**2+es**2
            aS=es/10;bS=(1-es)/10
            aK=s.Rational(9,34)*es**2/D0;bK=s.Rational(9,34)*(1-es)**2/D0
        else:
            N=2+10*es+2*es**3;T=2+82*es**2+12*es**3+2*es**6
            aS=2*es**3/N;bS=2*es/N;aK=8*es**3/T;bK=32*es**2/T
        pS,cs=reduced_poly(aS,bS);pK,ck=reduced_poly(aK,bK)
        num,den=(cs,ck) if fam=='r' else (ck,cs)
        def ratio_u(u):
            c=math.sin(u/2)**2
            return float(np.polyval(num,c)/np.polyval(den,c))
        pts=[0.];p=e
        while p<math.pi:
            pts.append(p);p*=10
        pts.append(math.pi)
        means=[];errors=[]
        for power in (1,2):
            vals=[quad(lambda u:ratio_u(u)**power,lo,hi,epsabs=1e-25,epsrel=3e-10,limit=300) for lo,hi in zip(pts[:-1],pts[1:])]
            means.append(sum(a for a,b in vals)/math.pi);errors.append(sum(b for a,b in vals)/math.pi)
        mean,m2=means;var=max(0,m2-mean*mean)
        # 70-digit independent point evaluation of exact rational polynomials.
        mp.mp.dps=70
        pn=(pS if fam=='r' else pK);pd=(pK if fam=='r' else pS)
        def mp_eval(poly,x):
            y=mp.mpf('0')
            for coef in poly.all_coeffs():
                y=y*x+mp.mpf(str(s.numer(coef)))/mp.mpf(str(s.denom(coef)))
            return y
        for mult in (0,1,10):
            u=mp.mpf(str(e))*mult;c=mp.sin(u/2)**2
            exact_mp=mp_eval(pn,c)/mp_eval(pd,c)
            assert abs(ratio_u(float(u))/float(exact_mp)-1)<3e-12
        if fam=='r':assert mean<=8 and m2>=289/(2073600*math.pi*e)*(1-1e-8)
        else:assert mean<=216*e and m2>=e/(36*math.pi)*(1-1e-8)
        item={'quantity':fam,'epsilon':str(es),'mean':mean,'second_moment':m2,'standard_deviation':math.sqrt(var),
              'CV':math.sqrt(var)/mean,'peak_at_pi':ratio_u(0),'quadrature_error_estimates':errors,
              'CS_reduced_poly':str(pS.as_expr()),'CK_reduced_poly':str(pK.as_expr()),
              'status':'NUMERICAL CROSS-CHECK, not a rigorous quadrature certificate'}
        cv.append(item)
        print(f'{fam}: e={es}, mean={mean:.10g}, CV={item["CV"]:.10g}, peak={item["peak_at_pi"]:.10g}')
out={'matrix_checks':records,'fixed_purity_checks':purity_checks,'polynomial_records':poly_records,
     'CV_quadrature':cv,'all_assertions_pass':True,'note':'Exact proofs and rational witness CV lower bounds are in verify_target2_exact.py, not inferred from this quadrature.'}
(ROOT/'results/target2_numerical.json').write_text(json.dumps(out,indent=2))
print('T2 full-matrix/state/return-measure, recurrence cancellation, high-precision point checks: PASS')

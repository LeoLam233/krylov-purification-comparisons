"""Exact rational/algebraic Krylov oracles. No numerical fitting is used.

Channel A constructs monic orthogonal polynomials from a discrete measure.
Channel B constructs matrix-valued commutator Krylov vectors directly.
They share only SymPy arithmetic, not a complexity formula or recurrence data.
"""
import sympy as sp


def simp(z):
    return sp.simplify(sp.expand_complex(z))


def spectral_certificate(nodes, weights, time):
    """Return exact orthogonal polynomials, norms and finite-time probabilities."""
    nodes=list(map(sp.sympify,nodes)); weights=list(map(sp.sympify,weights))
    assert sp.simplify(sum(weights)-1)==0
    assert all(w.is_positive for w in weights)
    x=sp.Symbol('x', real=True)
    polynomials=[]; norms=[]
    def dot(p,q):
        return sp.factor(sum(w*p.subs(x,a)*q.subs(x,a) for a,w in zip(nodes,weights)))
    for n in range(len(nodes)):
        p=x**n
        # Full monomial Gram-Schmidt, not a three-term Lanczos recurrence.
        for q,h in zip(polynomials,norms): p=sp.expand(p-dot(p,q)*q/h)
        h=dot(p,p)
        assert h.is_positive
        assert all(dot(p,q)==0 for q in polynomials)
        polynomials.append(sp.factor(p)); norms.append(h)
    terminal=sp.prod(x-a for a in nodes)
    assert dot(terminal,terminal)==0
    probs=[]
    for p,h in zip(polynomials,norms):
        ar=sp.simplify(sum(w*p.subs(x,a)*sp.cos(a*time) for a,w in zip(nodes,weights)))
        ai=sp.simplify(sum(w*p.subs(x,a)*sp.sin(a*time) for a,w in zip(nodes,weights)))
        probs.append(sp.simplify((ar**2+ai**2)/h))
    assert sp.simplify(sum(probs)-1)==0
    c=sp.simplify(sum(n*p for n,p in enumerate(probs)))
    # b_n^2 = h_n/h_(n-1), a_n = <x p_n,p_n>/h_n
    return dict(nodes=nodes,weights=weights,polynomials=polynomials,norms=norms,
                a=[sp.simplify(dot(x*p,p)/h) for p,h in zip(polynomials,norms)],
                b_squared=[sp.simplify(norms[i]/norms[i-1]) for i in range(1,len(norms))],
                probabilities=probs,complexity=c,terminal=terminal)


def direct_operator_certificate(H,O,Ot,max_steps=None):
    """Unnormalized commutator Lanczos in matrix space, finite-time direct Ot.

    Probabilities divide by both the seed norm and each polynomial-vector norm.
    The direct evolution is supplied independently, not reconstructed from the
    measure used by spectral_certificate.
    """
    H=sp.Matrix(H);O=sp.Matrix(O);Ot=sp.Matrix(Ot)
    assert H==H.adjoint() and O==O.adjoint() and Ot==Ot.adjoint()
    def dot(A,B): return sp.simplify(sp.trace(A.adjoint()*B))
    def L(A): return H*A-A*H
    def ms(A): return A.applyfunc(sp.simplify)
    h0=dot(O,O)
    vs=[];hs=[];aa=[];bs=[]
    v=O
    bound=max_steps or H.rows**2
    for n in range(bound+1):
        h=dot(v,v)
        if h==0:
            assert v==sp.zeros(*v.shape)
            break
        assert h.is_positive
        for old in vs: assert dot(old,v)==0
        vs.append(v);hs.append(h)
        lv=L(v);a=sp.simplify(dot(v,lv)/h);aa.append(a)
        nxt=lv-a*v
        if n:
            b=sp.simplify(h/hs[n-1]);bs.append(b)
            nxt-=b*vs[n-1]
        v=ms(nxt)
    else: raise AssertionError('Exact chain did not terminate within expected bound')
    ps=[]
    for v,h in zip(vs,hs):
        z=dot(v,Ot)
        ps.append(sp.simplify(z*sp.conjugate(z)/(h*h0)))
    assert sp.simplify(sum(ps)-1)==0
    return dict(seed_norm_squared=h0,a=aa,b_squared=bs,norms=hs,
                probabilities=ps,complexity=sp.simplify(sum(n*p for n,p in enumerate(ps))),
                chain_length=len(vs),terminal_zero=True,vectors=vs)


def jsonable(obj):
    if isinstance(obj,dict): return {k:jsonable(v) for k,v in obj.items()}
    if isinstance(obj,(list,tuple)): return [jsonable(x) for x in obj]
    if isinstance(obj,sp.MatrixBase): return [[str(x) for x in row] for row in obj.tolist()]
    if isinstance(obj,sp.Basic): return str(obj)
    return obj

"""Paper-stage coverage, provenance, exact arithmetic, and overclaim checks.

The reviewed snapshot records the drafting agent's semantic comparison with V3.
This script verifies coverage and change detection; it does not turn that review
into an independent mathematical proof or independent human validation.
"""
from pathlib import Path
from fractions import Fraction as F
import json
import re
from integrity_check import ROOT, load_inputs, sha


def evaluate(poly, x):
    return sum((a*x**i for i, a in enumerate(poly)), F(0))


def spectral_probabilities(nodes, weights, cosines, sine_sqrt3_coefficients):
    polys, norms, probabilities = [], [], []
    for degree in range(len(nodes)):
        p = [F(0)] * degree + [F(1)]
        for q, norm in zip(polys, norms):
            overlap = sum((w*evaluate(p, x)*evaluate(q, x) for x,w in zip(nodes,weights)), F(0))
            for i, qi in enumerate(q):
                p[i] -= overlap*qi/norm
        norm = sum((w*evaluate(p,x)**2 for x,w in zip(nodes,weights)), F(0))
        assert norm > 0
        a = sum((w*evaluate(p,x)*c for x,w,c in zip(nodes,weights,cosines)), F(0))
        b = sum((w*evaluate(p,x)*s for x,w,s in zip(nodes,weights,sine_sqrt3_coefficients)), F(0))
        probabilities.append((a*a+3*b*b)/norm)
        polys.append(p); norms.append(norm)
    assert sum(probabilities) == 1
    return probabilities, [norms[i]/norms[i-1] for i in range(1,len(norms))]


def exact_checks(v3):
    tests=[]
    def record(name, condition, detail):
        assert condition, name
        tests.append({'name':name,'status':'PASS','detail':detail})
    def complexity(probs):
        return sum((i*p for i,p in enumerate(probs)),F(0))
    source=json.loads(v3['current_final/Krylov_remaining_attack/results/target1r_exact.json'])['cases'][0]
    for name, nodes, cosines, sine in [
        ('mixed',[-2,0,2],[F(-1,2),F(1),F(-1,2)],[F(-1,2),F(0),F(1,2)]),
        ('purified_operator_I',[-2,-1,0,1,2],[F(-1,2),F(1,2),F(1),F(1,2),F(-1,2)],
         [F(-1,2),F(-1,2),F(0),F(1,2),F(1,2)])]:
        weights=list(map(F,source[name]['weights']))
        probs,bsq=spectral_probabilities(list(map(F,nodes)),weights,cosines,sine)
        record('right_'+name+'_all_probabilities',probs==list(map(F,source[name]['probabilities'])),[str(p) for p in probs])
        record('right_'+name+'_lanczos',bsq==list(map(F,source[name]['b_squared'])),[str(p) for p in bsq])
        record('right_'+name+'_complexity',complexity(probs)==F(source[name]['complexity']),str(complexity(probs)))
    gap=F(source['mixed']['complexity'])-F(source['purified_operator_I']['complexity'])
    record('right_finite_gap',gap==F(1600683,39299936)>0,str(gap))
    for name,mu,expected in [('mixed',F(3,182),[F(7744,8281),F(0),F(537,8281)]),
                              ('spread',F(1,42),[F(400,441),F(0),F(41,441)])]:
        probs,_=spectral_probabilities([F(-1),F(0),F(1)],[mu/2,1-mu,mu/2],
                                      [F(-1),F(1),F(-1)],[F(0)]*3)
        record('left_'+name+'_all_probabilities',probs==expected,[str(p) for p in probs])
    record('left_finite_gap',F(82,441)-F(1074,8281)==F(4192,74529)>0,str(F(4192,74529)))
    left_eigen=[F(16,21),F(4,21),F(1,21)]
    right_eigen=[F(16,26),F(1,26),F(9,26)]
    record('left_trace_rank_purity',min(left_eigen)>0 and sum(left_eigen)==1 and sum(x*x for x in left_eigen)==F(13,21),'all eigenvalues positive; trace 1; P=13/21')
    record('right_trace_rank_purity',min(right_eigen)>0 and sum(right_eigen)==1 and sum(x*x for x in right_eigen)==F(1,2),'all eigenvalues positive; trace 1; P=1/2')
    curvature_m=2*(right_eigen[0]-right_eigen[1])**2/F(1,2)
    curvature_i=2*(right_eigen[0]+right_eigen[1])
    record('right_curvature_and_interval',curvature_m==F(225,169) and curvature_i==F(221,169) and (curvature_m-curvature_i)/64==F(1,2704),'225/169, 221/169, exact threshold 1/2704')
    d=F(1,20); t=F(1,20000)
    curvature=(4-540*d*d)/169
    lower=curvature*t*t-F(21296,125)*t**3
    record('perturbation_curvature_and_finite_bound',curvature==F(53,3380) and lower==F(378247,21125000000000000)>0,str(lower))
    record('main_CV_constant',F(289,2073600)/(8**2)==F(289,132710400),'second-moment lower coefficient / mean upper squared')
    record('reciprocal_CV_constant',F(1,36)/(216**2)==F(1,1679616),'second-moment lower coefficient / mean upper squared')
    e=F(1,10**10)
    record('main_finite_CV_gt80',F(289,132710400)*F(7,22)/e-1>80**2,'epsilon=10^-10; pi<22/7')
    record('reciprocal_finite_CV_gt40',F(1,1679616)*F(7,22)/e-1>40**2,'eta=1/100000; epsilon=eta^2')
    anchor=[F(66,100),F(24,100),F(8,100),F(2,100)]
    record('fixed_purity_anchor',min(anchor)>0 and sum(anchor)==1 and sum(x*x for x in anchor)==F(1,2),'positive eigenvalues; trace 1; P=1/2')
    record('m_family_at_4',F(1,2*(4**2+5))==F(1,42) and F(9,2*(4**4+17))==F(3,182),'m=4 matches lower witness weights')
    return tests


def main():
    b,v=load_inputs()
    paper=ROOT/'paper'
    snapshot=json.loads((paper/'checks/REVIEWED_CONTENT.json').read_text())
    assert snapshot['authority'].endswith('aaebb0e5b0768746bbd0c1eccb1fd128534680c54c8377de90e0c58365c29401')
    texts={p.relative_to(paper).as_posix():p.read_text(encoding='utf-8') for p in [paper/'main.tex',*sorted((paper/'sections').glob('*.tex'))]}
    assert set(texts)=={r['path'] for r in snapshot['section_files']}, 'Review must cover main.tex and every section'
    for row in snapshot['section_files']:
        assert sha(texts[row['path']].encode())==row['sha256'], 'Changed since semantic review: '+row['path']
    displays={}; statements={}; literal_checks=[]
    for file,text in texts.items():
        for m in re.finditer(r'\\begin\{equation\}(.*?)\\end\{equation\}',text,re.S):
            label=re.search(r'\\label\{([^}]+)\}',m[1]).group(1)
            assert label not in displays
            displays[label]=m[0]
        for m in re.finditer(r'\\begin\{(theorem|proposition|corollary|lemma)\}(.*?)\\end\{\1\}',text,re.S):
            label=re.search(r'\\label\{([^}]+)\}',m[2]).group(1)
            assert label not in statements
            statements[label]=m[0]
    assert set(displays)=={r['label'] for r in snapshot['displays']}
    assert set(statements)=={r['label'] for r in snapshot['theorems']}
    for records,observed in [(snapshot['displays'],displays),(snapshot['theorems'],statements)]:
        for row in records:
            assert sha(observed[row['label']].encode())==row['sha256'],row['label']
            for src in row['sources']:
                assert sha(v[src['path']])==src['sha256'],src['path']
            assert row['status']=='REVIEWED_MATCHES_V3'
    for row in snapshot['displays']:
        source_text='\n'.join(v[src['path']].decode('utf-8',errors='replace') for src in row['sources'])
        numeric_text=re.sub(r'\\frac([0-9])([0-9])',r'\1 / \2',displays[row['label']])
        integers=sorted(set(re.findall(r'\d+',numeric_text)))
        # Additional typo screen, not a semantic formula-equality test.
        absent=[s for s in integers if int(s)>=10 and not re.search(r'(?<!\d)'+s+r'(?!\d)',source_text)]
        assert not absent, (row['label'],'numeric literals absent from mapped V3 sources',absent)
        literal_checks.append({'label':row['label'],'status':'PASS'})
    for q in snapshot['quantifier_inventory']:
        assert texts[q['file']].splitlines()[q['line']-1]==q['text']
    maptext=(paper/'CLAIM_SOURCE_MAP.md').read_text()
    for label in statements:
        assert label in maptext,label+' missing in source map'
    joined='\n'.join(texts.values())
    plain=re.sub(r'%[^\n]*','',joined)
    collapsed=re.sub(r'\s+',' ',plain).lower()
    forbidden=[r'all three conjectures are false',r'conjecture[ ~]*2 is (?:false|disproved)',
               r'first[ -]ever',r'first counterexample',r'independently externally validated',
               r'independent human validation has been (?:obtained|performed|completed)']
    hits=[p for p in forbidden if re.search(p,collapsed)]
    assert not hits,hits
    for n in ['268435456','2359296','2985984']:
        assert n not in joined,'Nonauthoritative clean-room coefficient in manuscript'
    assert '\\frac{289}{132710400\\pi\\eps}' in joined
    assert '\\frac1{1679616\\pi\\eps}' in joined
    assert '\\left(1-\\frac\\eps{10}\\right)' in joined
    labels=re.findall(r'\\label\{([^}]+)\}',joined)
    assert len(labels)==len(set(labels)), 'Duplicate LaTeX label'
    refs=re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',joined)
    assert not (set(refs)-set(labels)), 'Undefined internal reference'
    bib=(paper/'references.bib').read_text()
    keys=set(re.findall(r'@\w+\{([^,]+),',bib))
    cites=set(k for s in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',joined) for k in s.split(','))
    assert cites==keys and len(keys)==5,(cites,keys)
    required=['main.tex','main.pdf','references.bib','CLAIM_SOURCE_MAP.md','NOTATION_MAP.md',
              'BIBLIOGRAPHY_PROVENANCE.md','PROPOSED_NONAUTHORITATIVE_IMPROVEMENTS.md',
              'AI_ASSISTANCE_DISCLOSURE_TODO.md','BUILD.md']
    for name in required: assert (paper/name).is_file(),name
    result={'status':'PASS','integrity_authority':snapshot['authority'],
            'display_coverage':len(displays),'formal_statement_coverage':len(statements),
            'quantifier_scope_trigger_lines_reviewed':len(snapshot['quantifier_inventory']),
            'parameter_domains_reviewed':snapshot['parameter_review'],
            'reviewed_files_unchanged':True,'mapped_v3_sources_hash_verified':True,
            'display_integer_literal_screen':literal_checks,
            'exact_arithmetic_checks':exact_checks(v),
            'forbidden_overclaim_hits':hits,'nonauthoritative_constants_absent':True,
            'citation_keys':sorted(keys),'undefined_source_citations':[],
            'unconditional_infinite_dimensional_claim':'NONE; theorem explicitly finite; negative scope mentions reviewed',
            'required_outputs_present':required,
            'semantic_review_limit':snapshot['review_method']}
    (paper/'checks/PAPER_CHECK_REPORT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(f'PAPER CHECKS PASS: {len(displays)} displays, {len(statements)} formal statements, {len(snapshot["quantifier_inventory"])} scope lines, {len(result["exact_arithmetic_checks"])} exact arithmetic checks, 5 citations.')


if __name__=='__main__':
    main()

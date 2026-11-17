# External computation reproduction source

The managed Lean workspace accepts research documentation rather than executable Python uploads. The following complete listings document the external computations; they are not Lean source and are not executed by the repository build. For local reproduction, copy each listing into the named file beside the retained JSON inputs. The dependencies and commands are recorded in README.md.

## spectral_correction_experiment.py

```python
"""Independent reproduction of the selected CRT paper's diagonal correction.

Floating-point optimization is a diagnostic, never a uniform or Lean theorem.
The saved decimal coefficients are subsequently interpreted as exact rationals.
"""
import json
import sys
from pathlib import Path
import numpy as np
import scipy.linalg as la
from scipy.optimize import brentq
from scipy.special import roots_legendre
import mpmath as mp
from sympy import primerange, mobius, totient


def finite_data(x):
    p = np.array(list(primerange(1, x + 1)), dtype=int)
    d = np.array([n for n in range(1, x + 1) if mobius(n) != 0])
    Y = p[None, :] * (d[:, None] % p[None, :] == 0) - 1
    X = np.column_stack([np.ones(len(d)), Y])
    a = np.prod(1 - 1 / p)
    weights = np.array([a / int(totient(int(n))) for n in d])
    D1 = np.r_[1, p - 1]
    M = np.diag(D1) - X.T @ (weights[:, None] * X)
    pairs = np.array([(i,j) for i in range(len(p)) for j in range(i+1,len(p))])
    C = Y[:, pairs[:,0]] * Y[:, pairs[:,1]]
    D2 = (p[pairs[:,0]]-1)*(p[pairs[:,1]]-1)
    H = np.sum(np.log(p)**2)
    g = Y @ np.log(p)
    g[0] += H
    v = la.solve(M, X.T @ (weights*g), assume_a='pos')
    return dict(x=x,p=p,d=d,Y=Y,X=X,weights=weights,M=M,pairs=pairs,C=C,D2=D2,H=H,g=g,v=v)


def columns(data, ts, zetas):
    p,Y,X,w,M,C,ij = [data[k] for k in ['p','Y','X','weights','M','C','pairs']]
    az = np.exp(np.log(p)[:,None]*(.5+1j*ts[None,:]))-1
    K = np.prod(1 + Y[:,:,None]*az[None,:,:]/(p[None,:,None]-1),axis=1)
    full = np.vstack([np.ones(len(ts)),az])
    k = full - X.T @ (w[:,None]*K)
    rho = w[:,None]*(X @ la.solve(M,k,assume_a='pos')-K)
    N = data['H'] + zetas*(np.log(p)@az + data['g']@rho)
    L = zetas[None,:]*(az[ij[:,0],:]*az[ij[:,1],:] + C.T@rho)
    return N,L.T


def zeta_grid(ts):
    return np.array([complex(mp.zeta(mp.mpc('.5',-float(t)))) for t in ts])


def run(xs, out, block=(1.,4.)):
    mp.mp.dps=35
    lo,hi=block
    nodes,weights=roots_legendre(120 if hi>4 else 80)
    ts=(hi+lo)/2+(hi-lo)/2*nodes
    weights=(hi-lo)/2*weights/(np.pi*(ts**2+.25))
    validate=np.linspace(lo,hi,1601 if hi>4 else 801)
    zz,zv=zeta_grid(ts),zeta_grid(validate)
    reports=[]
    for x in xs:
        data=finite_data(x)
        N,L=columns(data,ts,zz)
        scale=x*x*np.log(x)
        A=L/np.sqrt(data['D2'])[None,:]
        A=np.vstack([A.real*np.sqrt(weights)[:,None],A.imag*np.sqrt(weights)[:,None]])
        b=-np.r_[N.real*np.sqrt(weights),N.imag*np.sqrt(weights)]
        U,s,Vh=la.svd(A,full_matrices=False)
        rhs=U.T@b
        def trial(mu): return s*rhs/(s*s+mu)
        def budget(mu): return np.sum(trial(mu)**2)
        lower=1e-25
        if budget(lower)<=scale:
            mu=lower
        else:
            upper=1.
            while budget(upper)>scale: upper*=10
            mu=brentq(lambda a:budget(a)-scale,lower,upper,xtol=1e-25)
        coeff=(Vh.T@trial(mu))/np.sqrt(data['D2'])
        Nv,Lv=columns(data,validate,zv)
        residual=Nv+Lv@coeff
        integrate=getattr(np,'trapezoid',np.trapz)
        norm=lambda y:float(integrate(abs(y)**2/(np.pi*(validate**2+.25)),validate)/scale)
        report=dict(x=x,block=list(block),prime_count=len(data['p']),pair_count=len(coeff),
                    cutoff_scale=scale,uncorrected=norm(Nv),corrected=norm(residual),
                    diagonal_energy=float(np.sum(data['D2']*coeff**2)/scale),
                    multiplier=mu,smallest_sampled_singular_value=float(s[-1]),
                    classification=f'floating-point diagnostic; independent {len(validate)}-node validation',
                    coefficients=[format(float(v),'.17g') for v in coeff])
        reports.append(report)
        print({k:v for k,v in report.items() if k!='coefficients'},flush=True)
        Path(out).write_text(json.dumps(reports,indent=2)+'\n')


if __name__=='__main__':
    run([int(x) for x in sys.argv[1:]] or [53,97,199], 'spectral_correction_diagnostics.json')
```

## certify_spectral_block.py

```python
"""External Arb certificate for a continuous diagonal-pair Mellin block.

Not a Lean-kernel certificate. Optimizer decimals are exact rational inputs.
All subsequent calculations use rigorous FLINT/Arb balls, including matrix
inversion and analytic integration. The integrand uses N(t)N(-t), not complex
conjugation at a complex integration argument.
Source: highest viability RH.pdf, equations (44), (62), (72), (73).
"""
import json
import argparse
import hashlib
from fractions import Fraction
from pathlib import Path
from flint import arb, acb, arb_mat, ctx, __version__
from sympy import primerange, mobius, totient


def certify(record, digits=50, tolerance='1e-10', upper_bound='1/10000',
            input_name='spectral_correction_diagnostics.json', integration_block=None):
    ctx.dps=digits
    x=record['x']
    optimization_block=record.get('block',[1,4])
    block=optimization_block if integration_block is None else integration_block
    primes=list(primerange(1,x+1))
    head=[d for d in range(1,x+1) if mobius(d)!=0]
    pairs=[(i,j) for i in range(len(primes)) for j in range(i+1,len(primes))]
    assert len(pairs)==len(record['coefficients'])
    rational_coeff=[Fraction(c)*Fraction(9999,10000) for c in record['coefficients']]
    as_arb=lambda q:arb(f'{q.numerator}/{q.denominator}')
    coeff=[as_arb(q) for q in rational_coeff]
    p_arb=[arb(p) for p in primes]
    logs=[p.log() for p in p_arb]
    H=sum((v*v for v in logs),arb(0))
    haar=Fraction(1)
    for p in primes: haar*=Fraction(p-1,p)
    weight_q=[haar/Fraction(int(totient(d))) for d in head]
    weights=[as_arb(q) for q in weight_q]
    Y=[[p*int(d%p==0)-1 for p in primes] for d in head]
    X=[[1]+row for row in Y]
    rank=len(primes)+1
    Mq=[[Fraction(([1]+[p-1 for p in primes])[i] if i==j else 0)
         -sum((weight_q[k]*X[k][i]*X[k][j] for k in range(len(head))),Fraction(0))
         for j in range(rank)] for i in range(rank)]
    # Exact rational LDL pivots prove positive definiteness of the free Gram.
    L=[[Fraction(int(i==j)) for j in range(rank)] for i in range(rank)]
    piv=[]
    for j in range(rank):
        pivot=Mq[j][j]-sum(L[j][k]**2*piv[k] for k in range(j))
        assert pivot>0
        piv.append(pivot)
        for i in range(j+1,rank):
            L[i][j]=(Mq[i][j]-sum(L[i][k]*L[j][k]*piv[k] for k in range(j)))/pivot
    M=arb_mat([[as_arb(q) for q in row] for row in Mq])
    g=[sum((logs[i]*row[i] for i in range(len(primes))),arb(0))
       +(H if d==1 else 0) for d,row in zip(head,Y)]
    m=[g[k]+sum((coeff[q]*row[i]*row[j] for q,(i,j) in enumerate(pairs)),arb(0))
       for k,row in enumerate(Y)]
    rhs=arb_mat([[sum((weights[k]*X[k][i]*m[k] for k in range(len(head))),arb(0))]
                 for i in range(rank)])
    u=M.solve(rhs)
    headcoeff=[weights[k]*(m[k]+sum((X[k][i]*u[i,0] for i in range(rank)),arb(0)))
               for k in range(len(head))]
    scale=arb(x*x)*arb(x).log()
    energy=sum((coeff[q]**2*(primes[i]-1)*(primes[j]-1)
                for q,(i,j) in enumerate(pairs)),arb(0))/scale
    assert energy<1, f'Budget not certified: {energy}'
    def numerator(z):
        az=[(z*lp).exp()-1 for lp in logs]
        gamma=u[0,0]+sum(((logs[i]+u[i+1,0])*az[i] for i in range(len(primes))),acb(0))
        gamma+=sum((coeff[q]*az[i]*az[j] for q,(i,j) in enumerate(pairs)),acb(0))
        for row,hc in zip(Y,headcoeff):
            K=acb(1)
            for i,p in enumerate(primes): K*=1+row[i]*az[i]/(p-1)
            gamma-=hc*K
        return H+(1-z).zeta()*gamma
    def integrand(t, analytic):
        # This is a meromorphic extension in t, with no variable branch cuts.
        z=acb(arb('1/2'))+acb(0,1)*t
        zm=acb(arb('1/2'))-acb(0,1)*t
        return numerator(z)*numerator(zm)/(arb.pi()*(t*t+arb('1/4'))*scale)
    result=acb.integral(integrand,arb(str(block[0])),arb(str(block[1])),
                        rel_tol=arb(tolerance),abs_tol=arb(tolerance),
                        eval_limit=100000,depth_limit=30)
    assert result.is_finite(), str(result)
    assert result.imag.contains(0), str(result)
    assert result.real>0, str(result)
    assert result.real<arb(upper_bound), str(result)
    out=dict(x=x,block=block,optimization_block=optimization_block,
        arithmetic='FLINT/Arb ball arithmetic',python_flint=__version__,
        digits=digits,integration_tolerance=tolerance,head_atoms=len(head),
        first_chaos_rank=rank,pair_columns=len(pairs),
        free_gram_positive_definite_exact=True,
        diagonal_energy_ratio=str(energy),continuous_residual_ratio=str(result.real),
        certified_inequalities=['diagonal energy < x^2 log(x)',
                                f'0 < continuous {block} residual < ({upper_bound}) * x^2 log(x)'],
        coefficient_scaling='9999/10000',
        coefficient_input=f'17-digit decimals in {input_name}, interpreted as exact rationals',
        coefficients_sha256=hashlib.sha256(json.dumps(record['coefficients'],separators=(',',':')).encode()).hexdigest(),
        scope='finite cutoff only; external computational certificate, not Lean-kernel or uniform evidence')
    return out


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cutoffs',type=int,nargs='*')
    parser.add_argument('--input',default='spectral_correction_diagnostics.json')
    parser.add_argument('--output',default='spectral_correction_arb_certificates.json')
    parser.add_argument('--bound',default='1/10000')
    parser.add_argument('--digits',type=int,default=50)
    parser.add_argument('--block',type=float,nargs=2,help='Evaluate the same coefficients on another interval')
    args=parser.parse_args()
    selected=set(args.cutoffs) or {53,97,199}
    reports=[]
    for r in json.loads(Path(args.input).read_text()):
        if r['x'] in selected:
            v=certify(r,digits=args.digits,upper_bound=args.bound,input_name=args.input,
                      integration_block=args.block)
            reports.append(v)
            print(json.dumps(v),flush=True)
            Path(args.output).write_text(json.dumps(reports,indent=2)+'\n')
```

## test_spectral_correction_exact.py

```python
"""Exact-rational regression for the compressed projected-pair calculation.

Enumerate the full Boolean cube at small cutoffs, independently of the
compressed production formula. This is an external algebra test, not Lean.
Logarithms and p**z-1 are replaced by arbitrary rational symbols/values;
the identities are polynomial or rational and do not require transcendental
evaluation. All assertions are exact SymPy rational equalities/inequalities.
"""
from itertools import product
from sympy import Matrix, Rational as Q, primerange, prod


def check(x):
    primes = list(primerange(1, x + 1))
    pairs = [(i,j) for i in range(len(primes)) for j in range(i+1,len(primes))]
    atoms = [prod(p for p,b in zip(primes,bits) if b) for bits in product([0,1],repeat=len(primes))]
    weights = [prod(Q(1,p) if d%p==0 else Q(p-1,p) for p in primes) for d in atoms]
    W = Matrix.diag(*weights)
    X = Matrix([[1]+[p*int(d%p==0)-1 for p in primes] for d in atoms])
    C = Matrix([[(primes[i]*int(d%primes[i]==0)-1)*(primes[j]*int(d%primes[j]==0)-1)
                 for i,j in pairs] for d in atoms])
    head = Matrix.diag(*[int(d<=x) for d in atoms])
    free = Matrix.eye(len(atoms))-head
    D1 = Matrix.diag(1,*[p-1 for p in primes])
    D2 = Matrix.diag(*[(primes[i]-1)*(primes[j]-1) for i,j in pairs])
    assert sum(weights)==1 and X.T*W*X==D1
    assert C.T*W*C==D2 and X.T*W*C==Matrix.zeros(len(primes)+1,len(pairs))
    M = X.T*W*free*X
    assert M==D1-X.T*W*head*X and M.is_positive_definite
    Minv = M.inv()
    logs = Matrix([Q(i+1,i+3) for i in range(len(primes))])
    H = (logs.T*logs)[0]
    S = X[:,1:]*logs
    g = S+Matrix([H if d==1 else 0 for d in atoms])
    v = Minv*X.T*W*head*g
    phi = S+X*v-head*(g+X*v)
    prescribed = Matrix([0]+[(p-1)*logs[i] for i,p in enumerate(primes)])
    assert X.T*W*phi==prescribed
    assert head*phi==Matrix([-H if d==1 else 0 for d in atoms])
    coeff = Matrix([Q((-1)**q,q+3) for q in range(len(pairs))])
    pair_value = C*coeff
    r = free*(pair_value+X*Minv*X.T*W*head*pair_value)
    assert head*r==Matrix.zeros(len(atoms),1)
    assert X.T*W*r==Matrix.zeros(len(primes)+1,1)
    assert (phi.T*W*r)[0]==0
    er = (r.T*W*r)[0]
    e_diag = (coeff.T*D2*coeff)[0]
    assert 0<=er<=e_diag
    assert ((phi+r).T*W*(phi+r))[0]==(phi.T*W*phi)[0]+er
    az = [Q(i+2,2*i+5) for i in range(len(primes))]
    K = Matrix([prod(1+Q(int(X[k,i+1]),primes[i]-1)*az[i] for i in range(len(primes)))
                for k in range(len(atoms))])
    full = Matrix([1]+az)
    assert X.T*W*K==full
    assert C.T*W*K==Matrix([az[i]*az[j] for i,j in pairs])
    k = full-X.T*W*head*K
    rho = head*W*(X*Minv*k-K)
    original_gamma = (logs.T*Matrix(az))[0]+(g.T*rho)[0]
    assert original_gamma==(phi.T*W*K)[0]
    m = g+pair_value
    u = Minv*X.T*W*head*m
    compressed = u[0]+sum((logs[i]+u[i+1])*az[i] for i in range(len(primes)))
    compressed += sum(coeff[q]*az[i]*az[j] for q,(i,j) in enumerate(pairs))
    compressed -= ((m+X*u).T*W*head*K)[0]
    assert compressed==((phi+r).T*W*K)[0]
    assert compressed==original_gamma+sum(coeff[q]*az[i]*az[j] for q,(i,j) in enumerate(pairs))+(pair_value.T*rho)[0]
    return dict(cutoff=x,atoms=len(atoms),pairs=len(pairs),assertions='all exact rational assertions passed')


if __name__=='__main__':
    for x in [7,11,13]:
        print(check(x),flush=True)
```

## assemble_spectral_certificates.py

```python
"""Combine adjacent certified blocks for exactly the same correction.

Uses interval additivity, established analytically for the continuous
integrand. This is external certificate bookkeeping, not a Lean proof.
"""
import json
import argparse
from pathlib import Path
from flint import arb,ctx


def assemble(pairs,output):
    ctx.dps=50
    reports=[]
    for low_path,high_path in pairs:
        low={r['x']:r for r in json.loads(Path(low_path).read_text())}
        high={r['x']:r for r in json.loads(Path(high_path).read_text())}
        assert low.keys()==high.keys()
        for x,a in low.items():
            b=high[x]
            assert a['block']==[0,16] and b['block']==[16,64]
            for key in ['coefficients_sha256','coefficient_scaling','coefficient_input']:
                assert a[key]==b[key]
            total=arb(a['continuous_residual_ratio'])+arb(b['continuous_residual_ratio'])
            energy=arb(a['diagonal_energy_ratio'])
            assert energy<1 and 0<total<arb('1/20')
            reports.append(dict(x=x,block=[0,64],same_correction_verified=True,
                combined_residual_ratio=str(total),diagonal_energy_ratio=str(energy),
                coefficients_sha256=a['coefficients_sha256'],
                coefficient_scaling=a['coefficient_scaling'],coefficient_input=a['coefficient_input'],
                input_certificates=[low_path,high_path],
                certified_inequalities=['diagonal energy < x^2 log(x)',
                    '0 < continuous [0,64] residual < (1/20) * x^2 log(x)'],
                symmetric_interpretation='Equals the [-64,64] contribution with weight 1/(2*pi*(t^2+1/4))',
                scope='finite cutoff; external ball arithmetic and interval additivity; no uniform or tail claim'))
    Path(output).write_text(json.dumps(reports,indent=2)+'\n')
    for r in reports:
        print(r,flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--include397',action='store_true')
    args=parser.parse_args()
    pairs=[
        ('spectral_correction_low_extended_arb_certificates.json',
         'spectral_correction_out_of_window_arb_certificates.json')]
    if args.include397:
        pairs.append(('spectral_correction_cutoff397_arb_certificates.json',
                      'spectral_correction_cutoff397_out_of_window_arb_certificates.json'))
    assemble(pairs,'spectral_correction_combined_arb_certificates.json')
```

## requirements.txt

```text
numpy==2.3.5
scipy==1.17.0
sympy==1.14.0
mpmath==1.3.0
python-flint==0.9.0
```

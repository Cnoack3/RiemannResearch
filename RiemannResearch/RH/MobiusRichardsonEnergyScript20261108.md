# Reproducible reciprocal-energy experiment

This is an external arithmetic calculation, not a Lean kernel certificate. Save the following Python block as `mobius_richardson_energy_experiment.py`. The `--certificate-only` mode uses the Python standard library and exact integer arithmetic; the optional diagnostic mode requires NumPy.

```python
"""Signed full-Q energy experiment. Floating rows are not interval-certified.
The n=2 comparison uses separate exact-integer outward enclosures.
"""
import argparse, json, math, time
from fractions import Fraction
from pathlib import Path

def mobius(N):
    mu=[1]*(N+1); primes=[True]*(N+1)
    primes[0]=primes[1]=False
    for p in range(2,N+1):
        if primes[p]:
            for k in range(p,N+1,p): mu[k]*=-1
            for k in range(p*p,N+1,p): primes[k]=False
            for k in range(p*p,N+1,p*p): mu[k]=0
    mu[0]=0
    return mu

def floating(n,T,family='Richardson'):
    import numpy as np
    tic=time.time(); N=n**(3*n); mu=mobius(N)
    indices=np.array([m for m in range(2,N+1) if mu[m]],dtype=np.int64)
    r=indices.astype(np.longdouble)**(-np.longdouble(1)/n)
    a=np.array([mu[m] for m in indices],dtype=np.longdouble)*((2*r-r*r) if family=='Richardson' else r)
    charge=(a/indices).sum(dtype=np.longdouble)
    endpoint=a*(1-1/indices.astype(np.longdouble))
    U=max(endpoint[endpoint>0].sum(),-endpoint[endpoint<0].sum())
    values=np.full(T+1,-charge,dtype=np.longdouble); values[0]=0
    for m,c in zip(indices,a): values[m::m]+=c
    np.cumsum(values,out=values)
    energy=np.longdouble(0); recip=np.longdouble(0)
    Z=np.longdouble(math.pi)**2/6
    for start in range(1,T+1,500000):
        stop=min(T+1,start+500000)
        k=np.arange(start,stop,dtype=np.longdouble); v=values[start:stop]
        energy+=np.sum(v*v/(Z*k*k),dtype=np.longdouble)
        recip+=np.sum((v-1)**2/(Z*k*k*(k+1)**2),dtype=np.longdouble)
    return {'family':family,'n':n,'N':N,'T':T,
      'prefix_energy':float(energy),'energy_tail_budget':float(U*U/(Z*T)),
      'reciprocal_error_sq':float(recip),'reciprocal_tail_budget':float((U+1)**2/(3*Z*T**3)),
      'signed_range_bound':float(U),'seconds':time.time()-tic}

def ceildiv(a,b): return -((-a)//b)

def outward_decimal(x,digits,upper=False):
    D=10**digits
    q=ceildiv(x.numerator*D,x.denominator) if upper else x.numerator*D//x.denominator
    return f'{q//D}.{q%D:0{digits}d}'

def exact_n2(family,T=200000,Zcut=100000,scale_bits=80,N_override=None):
    """All arithmetic producing rational interval endpoints uses Python integers.
    a_m=mu(m)/sqrt(m) for first_order; mu(m)*(2/sqrt(m)-1/m) for Richardson.
    The actual physical vector is -sum a_m frac(k/m).
    """
    tic=time.time(); S=1<<scale_bits; N=N_override if N_override is not None else (16 if family=='first_order' else 64)
    mu=mobius(N); interval=[]
    for m in range(2,N+1):
        if not mu[m]: continue
        q=math.isqrt((S*S)//m)
        qp=q if q*q*m==S*S else q+1
        assert q*q*m <= S*S <= qp*qp*m
        if family=='first_order': lo,hi=q,qp
        else: lo,hi=2*q-ceildiv(S,m),2*qp-S//m
        if mu[m]<0: lo,hi=-hi,-lo
        interval.append((m,lo,hi))
    Clo=sum(lo//m for m,lo,hi in interval)
    Chi=sum(ceildiv(hi,m) for m,lo,hi in interval)
    dlo=[0]*(T+1); dhi=[0]*(T+1)
    posU=0; negU=0
    for m,lo,hi in interval:
        for k in range(m,T+1,m): dlo[k]+=lo; dhi[k]+=hi
        if lo>0: posU+=ceildiv(hi*(m-1),m)
        elif hi<0: negU+=ceildiv((-lo)*(m-1),m)
        else: raise AssertionError('coefficient sign interval not separated')
    U=max(posU,negU)
    flo=fhi=0; elo=ehi=rlo=rhi=0
    for k in range(1,T+1):
        flo+=dlo[k]; fhi+=dhi[k]
        vlo=flo-k*Chi; vhi=fhi-k*Clo
        assert vlo<=vhi
        sl=0 if vlo<=0<=vhi else min(vlo*vlo,vhi*vhi)
        sh=max(vlo*vlo,vhi*vhi)
        den=S*k*k
        elo+=sl//den; ehi+=ceildiv(sh,den)
        vlo-=S; vhi-=S
        sl=0 if vlo<=0<=vhi else min(vlo*vlo,vhi*vhi)
        sh=max(vlo*vlo,vhi*vhi)
        den*=((k+1)*(k+1))
        rlo+=sl//den; rhi+=ceildiv(sh,den)
    Zlo=sum(S//(k*k) for k in range(1,Zcut+1))+S//(Zcut+1)
    Zhi=sum(ceildiv(S,k*k) for k in range(1,Zcut+1))+ceildiv(S,Zcut)
    ELo=Fraction(elo,Zhi); EHi=Fraction(ehi,Zlo)+Fraction(U*U,S*Zlo*T)
    RLo=Fraction(rlo,Zhi); RHi=Fraction(rhi,Zlo)+Fraction((U+S)**2,3*S*Zlo*T**3)
    return {'family':family,'n':2,'N':N,'T':T,'scale_bits':scale_bits,'zeta_series_cutoff':Zcut,
      'complete_energy_lower_rational':str(ELo),'complete_energy_upper_rational':str(EHi),
      'complete_energy_lower_float_for_display':float(ELo),
      'complete_energy_upper_float_for_display':float(EHi),
      'complete_energy_outward_decimal':[outward_decimal(ELo,12),outward_decimal(EHi,12,True)],
      'complete_reciprocal_error_sq_lower_rational':str(RLo),
      'complete_reciprocal_error_sq_upper_rational':str(RHi),
      'complete_reciprocal_error_sq_lower_float_for_display':float(RLo),
      'complete_reciprocal_error_sq_upper_float_for_display':float(RHi),
      'complete_reciprocal_error_sq_outward_decimal':[outward_decimal(RLo,15),outward_decimal(RHi,15,True)],
      'pointwise_bound_upper_rational':str(Fraction(U,S)),
      'seconds':time.time()-tic}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate-only',action='store_true',help='Skip floating diagnostics; uses only the Python standard library.')
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    out={'floating_status':'external long-double; no rounding certification',
         'integer_status':'exact integer outward rational enclosures plus proved analytic integral tails; external calculation, not Lean',
         'floating':[],'integer':[]}
    if not args.certificate_only:
        for n,T,family in [(2,1000000,'Richardson'),(3,30000000,'Richardson'),(3,30000000,'first_order_same_cutoff')]:
            r=floating(n,T,family);out['floating'].append(r);print(json.dumps(r),flush=True)
    for family,N in [('first_order',16),('first_order',64),('Richardson',64)]:
        r=exact_n2(family,N_override=N);out['integer'].append(r);print(json.dumps(r),flush=True)
    for i in [0,1]:
        assert Fraction(out['integer'][i]['complete_energy_upper_rational']) < Fraction(out['integer'][2]['complete_energy_lower_rational'])
        assert Fraction(out['integer'][2]['complete_reciprocal_error_sq_upper_rational']) < Fraction(out['integer'][i]['complete_reciprocal_error_sq_lower_rational'])
    out['exact_comparison']={'Richardson_n2_energy_strictly_larger_than_both_first_order_cutoffs':True,
      'Richardson_n2_reciprocal_error_strictly_smaller_than_both_first_order_cutoffs':True}
    with args.output.open('w') as f: json.dump(out,f,indent=2)
```

# Pareto-first finite certificate reproduction

These numerical instances are external exact-rational audits, not Lean kernel-replayed arithmetic. The associated general certification theorems are in QParetoPrimorialForcing and FiniteProjectionForcingCertificate. Save the following code as a Python file, install NumPy if necessary, and run it. The proposed coefficients use NumPy; acceptance uses rational arithmetic, positive LDL pivots, full infinite-tail intervals, and normal-residual budgets.

```python
#!/usr/bin/env python3
"""Exact rational finite-stage certificates for the Pareto-first agenda.

The numerical candidate solves are suggestions only. Acceptance uses Fraction
arithmetic, a rational LDL positivity check, complete infinite-tail enclosures,
and full normal-residual budgets. This executable audit is external evidence;
it is not a Lean kernel replay of the numerical instances.
"""
from fractions import Fraction as F
from math import isqrt
import json
from pathlib import Path
import numpy as np

def add(a,b): return a[0]+b[0], a[1]+b[1]
def neg(a): return -a[1], -a[0]
def sub(a,b): return add(a,neg(b))
def scale(c,a): return (c*a[0],c*a[1]) if c>=0 else (c*a[1],c*a[0])
def center(a): return (a[0]+a[1])/2
def dot_intervals(c,b):
    ans=(F(0),F(0))
    for x,y in zip(c,b): ans=add(ans,scale(x,y))
    return ans
def matvec(G,c): return [dot_intervals(c,row) for row in G]
def quadratic(G,c): return dot_intervals(c,matvec(G,c))
def solve(G,b):
    a=np.array([[float(center(x)) for x in row] for row in G])
    z=np.array([float(center(x)) for x in b])
    return [F(round(float(x)*10**9),10**9) for x in np.linalg.solve(a,z)]
def sqrt_upper(x):
    assert x>=0
    d=10**9
    q=isqrt(x.numerator*d*d//x.denominator)
    if q*q*x.denominator < x.numerator*d*d: q+=1
    y=F(q,d)
    assert y*y>=x
    return y
def normal_budget(G,b,c,lam):
    delta=[sub(a,z) for a,z in zip(matvec(G,c),b)]
    bound=sum((max(abs(lo),abs(hi))**2 for lo,hi in delta),F(0))/lam
    return delta,bound
def check_ldl(A):
    n=len(A); L=[[F(int(i==j)) for j in range(n)] for i in range(n)]
    d=[]
    for i in range(n):
        d.append(A[i][i]-sum((L[i][k]**2*d[k] for k in range(i)),F(0)))
        assert d[i]>0
        for j in range(i+1,n):
            L[j][i]=(A[j][i]-sum((L[j][k]*L[i][k]*d[k] for k in range(i)),F(0)))/d[i]
    return d

def certify(period,N):
    assert N%period==0
    m=[d for d in range(2,period+1) if period%d==0]
    q=len(m)
    gp=[[F(0) for _ in m] for _ in m]
    jj=[[F(0) for _ in m] for _ in m]
    b=[F(0) for _ in m]; d=[F(0) for _ in m]
    for k in range(1,N+1):
        g=[F(k%x,x) for x in m]; p=F(1,k*(k+1)); j=p/k
        for i in range(q):
            b[i]+=p*g[i]; d[i]+=j*g[i]
            for h in range(i+1):
                gp[i][h]+=p*g[i]*g[h]; jj[i][h]+=j*g[i]*g[h]
    for i in range(q):
        for h in range(i):
            gp[h][i]=gp[i][h]; jj[h][i]=jj[i][h]
    vals=[[F(k%x,x) for k in range(1,period+1)] for x in m]
    def p_enclose(head,a):
        mean=sum(a,F(0))/period; maximum=max(a)
        radius=F(period)*maximum/((N+1)*(N+2))
        middle=mean/(N+1)
        return head+max(F(0),middle-radius),head+min(maximum/(N+1),middle+radius)
    def j_enclose(head,a): return head,head+max(a)/(N+1)**2
    G=[[p_enclose(gp[i][h],[x*y for x,y in zip(vals[i],vals[h])])
        for h in range(q)] for i in range(q)]
    J=[[j_enclose(jj[i][h],[x*y for x,y in zip(vals[i],vals[h])])
        for h in range(q)] for i in range(q)]
    B=[p_enclose(b[i],vals[i]) for i in range(q)]
    D=[j_enclose(d[i],vals[i]) for i in range(q)]
    mineig=float(np.linalg.eigvalsh(np.array([[float(v) for v in row] for row in gp]))[0])
    lam=F(max(1,int(mineig*10**10/2)),10**10)
    ldl=check_ldl([[gp[i][h]-lam*(i==h) for h in range(q)] for i in range(q)])
    c=solve(G,B)
    delta1,e1sq=normal_budget(G,B,c,lam)
    Z=[sub(x,y) for x,y in zip(D,matvec(J,c))]
    t=solve(G,Z)
    delta2,e2sq=normal_budget(G,Z,t,lam)
    trialP=add(sub((F(1),F(1)),scale(2,dot_intervals(c,B))),quadratic(G,c))
    errP=(max(F(0),trialP[0]-e1sq),min(F(1),trialP[1]))
    forcing_upper=(sqrt_upper(max(F(0),quadratic(G,t)[1]))+
                   sqrt_upper(e1sq)+sqrt_upper(e2sq))**2
    GQ=[[add(G[i][h],J[i][h]) for h in range(q)] for i in range(q)]
    BQ=[add(x,y) for x,y in zip(B,D)]
    cq=solve(GQ,BQ)
    deltaQ,eQsq=normal_budget(GQ,BQ,cq,lam)
    zhead=sum((F(1,k*k) for k in range(1,N+1)),F(0))
    zeta=(zhead+F(1,N+1),zhead+F(1,N))
    trialQ=add(sub(zeta,scale(2,dot_intervals(cq,BQ))),quadratic(GQ,cq))
    errQ=(max(F(0),(trialQ[0]-eQsq)/zeta[1]),min(F(1),trialQ[1]/zeta[0]))
    result=dict(period=period,head=N,dictionary=m,
        complete_gram=G,reciprocal_gram=J,complete_source=B,reciprocal_source=D,
        coercivity_lower=lam,head_ldl_pivots=ldl,
        pareto_trial=c,forcing_trial=t,q_trial=cq,
        first_normal_intervals=delta1,first_defect_energy_upper=e1sq,
        forcing_normal_intervals=delta2,forcing_defect_energy_upper=e2sq,
        q_normal_intervals=deltaQ,q_defect_energy_upper=eQsq,
        complete_pareto_error_interval=errP,complete_q_error_interval=errQ,
        forcing_energy_upper=forcing_upper)
    print(json.dumps(dict(period=period,head=N,dimension=q,
        P_error=[float(x) for x in errP],Q_error=[float(x) for x in errQ],
        forcing_energy_upper=float(forcing_upper),lambda_lower=float(lam),
        first_solve_error=float(sqrt_upper(e1sq)),
        second_solve_error=float(sqrt_upper(e2sq))),sort_keys=True),flush=True)
    return result

def floor_grid(x):
    return F(x.numerator*10**15//x.denominator,10**15)
def ceil_grid(x):
    return -floor_grid(-x)
def compact(record):
    out={}
    for k,v in record.items():
        if k in ("complete_gram","reciprocal_gram"):
            out[k]=[[(floor_grid(a),ceil_grid(b)) for a,b in row] for row in v]
        elif k in ("complete_source","reciprocal_source","first_normal_intervals",
                   "forcing_normal_intervals","q_normal_intervals"):
            out[k]=[(floor_grid(a),ceil_grid(b)) for a,b in v]
        elif k.endswith("_interval"):
            out[k]=(floor_grid(v[0]),ceil_grid(v[1]))
        elif k.endswith("_upper"):
            out[k]=ceil_grid(v)
        elif k=="head_ldl_pivots":
            out["positive_head_ldl_pivot_lower_bounds"]=[floor_grid(x) for x in v]
            assert all(x>0 for x in out["positive_head_ldl_pivot_lower_bounds"])
        else: out[k]=v
    return out

if __name__=="__main__":
    records=[certify(6,600),certify(30,1800)]
    payload={"status":"external exact-rational audit; numerical instances not kernel replayed",
             "method":"complete periodic Pareto tails; complete reciprocal tails; rational LDL; two full normal residuals",
             "serialization":"interval endpoints rounded outward to denominator 10^15; all audits performed before rounding",
             "records":[compact(r) for r in records]}
    path=Path(__file__).with_name("ParetoFirstFiniteCertificates20261112.json")
    path.write_text(json.dumps(payload,default=str,indent=2)+"\n")
```

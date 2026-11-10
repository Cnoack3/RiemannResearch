# Reproducible full-conductor oscillation experiments

Requires Python 3, NumPy, and SciPy. Run the script below from a writable directory.
These are external calculations, not Lean or interval certificates.
The fixed modulus is 2; every divisor conductor is retained.

```python
"""Complete-period floating-point experiments; no Hilbert-tail truncation.

All results are external numerical evidence, not Lean/interval certificates.
P(n)=1/(n(n+1)); Q(n)=1/(zeta(2)*n*n); g_q(n)=(n mod q)/q.
"""
import json
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.special import digamma, polygamma, zeta
from scipy.spatial.distance import pdist

Z2 = np.pi**2 / 6

def periodic_weights(R):
    a = np.arange(1, R + 1, dtype=float)
    p = (digamma((a+1)/R)-digamma(a/R))/R
    s2 = polygamma(1, a/R)/R**2
    s3 = zeta(3, a/R)/R**3
    q = s2/Z2
    d = s2-p  # sum P(n)/n over the residue class
    d2 = s3-s2+p  # sum P(n)/n^2
    return p, q, d, d2

def experiment(R, cutoff, fixed_modulus=2):
    qs = np.array([q for q in range(2, R+1) if R % q == 0])
    a = np.arange(1, R+1)
    A = (a[:,None] % qs[None,:])/qs[None,:]
    p,q,w1,w2 = periodic_weights(R)
    GP = A.T @ (p[:,None]*A)
    GQ = A.T @ (q[:,None]*A)
    GD = A.T @ (w1[:,None]*A)
    GD2 = A.T @ (w2[:,None]*A)
    hp, hq = A.T @ p, A.T @ q
    cp, cq = np.linalg.solve(GP,hp), np.linalg.solve(GQ,hq)
    rp, rq, delta = 1-A@cp, 1-A@cq, A@(cq-cp)
    ep, eq = p @ rp**2, q @ rq**2
    C = GD2-GD@np.linalg.solve(GP,GD)
    C = (C+C.T)/2
    eig,V = np.linalg.eigh(C)
    # Roundoff may make a mathematically PSD Schur complement slightly negative.
    feature = np.linalg.solve(GQ,A.T).T @ (V*np.sqrt(np.maximum(eig,0)))
    omega=0.0; max_screened=0.0; maximizing_pair=None
    gcd=int(np.gcd(R,fixed_modulus))
    for b in range(gcd):
        ix=np.flatnonzero(a % gcd == b)
        di=delta[ix]
        val=float(np.max(di)-np.min(di))
        if val > omega:
            omega=val
            maximizing_pair=[int(a[ix[np.argmax(di)]]),int(a[ix[np.argmin(di)]])]
        if len(ix)>1:
            max_screened=max(max_screened,float(np.max(pdist(feature[ix]))))
    # The complete matched signed identity in coefficient form.
    signed = np.linalg.solve(GQ,A.T@(w1*rp))/Z2
    # Actual matched finite displacement: retain endpoint and signed coefficients.
    def physical(n):
        return float(((n % qs)/qs) @ (cq-cp))
    L,t,k=60,4,1
    terms=[[int(q0),float(-coeff)] for q0,coeff in zip(qs,cq-cp)
           if q0 <= k*L+t and L % q0 and (k*L)%q0+t%q0 >= q0]
    endpoint=physical(k*L)
    carry_sum=sum(v for _,v in terms)
    actual_difference=physical(k*L+t)-physical(t)
    assert abs(actual_difference-endpoint-carry_sum)<1e-12
    head_omega=0.0; head_screened=0.0
    for b in range(gcd):
        ix=np.flatnonzero((a % gcd == b) & (a <= cutoff))
        if len(ix): head_omega=max(head_omega,float(np.ptp(delta[ix])))
        if len(ix)>1: head_screened=max(head_screened,float(np.max(pdist(feature[ix]))))
    return dict(period=R,cutoff=cutoff,dimension=len(qs),fixed_modulus=fixed_modulus,
       omega=omega,maximizing_pair=maximizing_pair,
       residual_P_squared=float(ep),residual_Q_squared=float(eq),
       displacement_sup=float(np.max(np.abs(delta))),
       screened_kernel_diameter=max_screened,
       cauchy_bound=float(np.sqrt(ep)*max_screened/Z2),
       head_omega=head_omega,
       head_cauchy_bound=float(np.sqrt(ep)*head_screened/Z2),
       actual_carry_test=dict(L=L,t=t,k=k,endpoint=endpoint,terms=terms,
           signed_sum=carry_sum,difference=actual_difference),
       coefficient_l1_bound=float(np.sum(np.abs(cq-cp))),
       normal_P_defect=float(np.max(np.abs(A.T@(p*rp)))),
       normal_Q_defect=float(np.max(np.abs(A.T@(q*rq)))),
       signed_identity_defect=float(np.max(np.abs(signed-(cq-cp)))),
       schur_min_eigenvalue=float(eig[0]),
       gram_Q_condition=float(np.linalg.cond(GQ)),
       weights_P_mass=float(sum(p)),weights_Q_mass=float(sum(q)))

def mobius(q):
    k=0; p=2
    while p*p<=q:
        if q%p==0:
            q//=p; k+=1
            if q%p==0: return 0
        p+=1
    if q>1: k+=1
    return (-1)**k

def carry(f,L,t,k):
    N=k*L+t
    terms=[]
    for q in range(1,N+1):
        if L%q and (k*L)%q+t%q >= q:
            b=sum(mobius(q//a)*(f(a)-f(a-1)) for a in range(1,q+1) if q%a==0)
            if b: terms.append([q,b])
    return dict(L=L,t=t,k=k,endpoint=f(k*L),terms=terms,
       signed_sum=sum(v for q,v in terms),difference=f(k*L+t)-f(t))

if __name__ == '__main__':
    rows=[experiment(R,M) for R,M in [(2,2),(6,3),(12,4),(60,5),(420,7),(840,8),(2520,9)]]
    for row in rows:
        assert row['normal_P_defect'] < 1e-10
        assert row['normal_Q_defect'] < 1e-10
        assert row['signed_identity_defect'] < 1e-10
        assert abs(row['weights_P_mass']-1)<1e-12
        assert abs(row['weights_Q_mass']-1)<1e-12
        assert row['schur_min_eigenvalue'] > -1e-10
        assert row['omega'] <= row['cauchy_bound']+1e-10
        assert row['head_omega'] <= row['head_cauchy_bound']+1e-10
    exact_tests=0
    for f in [lambda n:Fraction(n%8,8), lambda n:Fraction(n.bit_count())]:
        for L in [2,6,60]:
            for t in [1,4,7]:
                for k in [0,1,2]:
                    r=carry(f,L,t,k)
                    assert r['difference']==r['endpoint']+r['signed_sum']
                    exact_tests+=1
    binary_normal_tests=[]
    for J in [2,4,8]:
        R=2**J; a=np.arange(1,R+1)
        F=sum((a%(2**j))/(2**j) for j in range(1,J+1))
        p,q,_,_=periodic_weights(R); g2=(a%2)/2
        binary_normal_tests.append(dict(J=J,
            P_target_one_normal_defect=float(p@((1-F)*g2)),
            Q_target_one_normal_defect=float(q@((1-F)*g2))))
    counterexamples={
       'binary_digit_sum_carry':carry(lambda n:n.bit_count(),2,1,7),
       'escaping_prime_power':carry(lambda n:(n%8)/8,60,4,1),
       'endpoint_required':carry(lambda n:(n%8)/8,60,1,1),
       'binary_fixed_modulus_2':[
           dict(J=j,pair=[2**j-1,1],difference=j-1,
                norm_tail_P_upper=(2+np.sqrt(2))*2**(-j/2)) for j in [2,4,8,16,32]]}
    out={'status':'external floating-point evidence; not interval certified',
         'stages':rows,'counterexamples':counterexamples,
         'exact_rational_carry_checks':exact_tests,
         'binary_approximants_fail_target_one_normal_equations':binary_normal_tests}
    Path(__file__).with_name('finite_oscillation_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
```

## Recorded results

```json
{
  "status": "external floating-point evidence; not interval certified",
  "stages": [
    {
      "period": 2,
      "cutoff": 2,
      "dimension": 1,
      "fixed_modulus": 2,
      "omega": 0.0,
      "maximizing_pair": null,
      "residual_P_squared": 0.3068528194400547,
      "residual_Q_squared": 0.25000000000000006,
      "displacement_sup": 0.0,
      "screened_kernel_diameter": 0.0,
      "cauchy_bound": 0.0,
      "head_omega": 0.0,
      "head_cauchy_bound": 0.0,
      "actual_carry_test": {
        "L": 60,
        "t": 4,
        "k": 1,
        "endpoint": 0.0,
        "terms": [],
        "signed_sum": 0,
        "difference": 0.0
      },
      "coefficient_l1_bound": 0.0,
      "normal_P_defect": 0.0,
      "normal_Q_defect": 0.0,
      "signed_identity_defect": 0.0,
      "schur_min_eigenvalue": 0.022423473489825083,
      "gram_Q_condition": 1.0,
      "weights_P_mass": 1.0,
      "weights_Q_mass": 1.0000000000000002
    },
    {
      "period": 6,
      "cutoff": 3,
      "dimension": 3,
      "fixed_modulus": 2,
      "omega": 0.015435699639868497,
      "maximizing_pair": [
        2,
        6
      ],
      "residual_P_squared": 0.07829325400232257,
      "residual_Q_squared": 0.05476694337026222,
      "displacement_sup": 0.023332365812998725,
      "screened_kernel_diameter": 0.45165734858047113,
      "cauchy_bound": 0.07682857135131121,
      "head_omega": 0.005768703890608979,
      "head_cauchy_bound": 0.06894260403176691,
      "actual_carry_test": {
        "L": 60,
        "t": 4,
        "k": 1,
        "endpoint": 0.0,
        "terms": [],
        "signed_sum": 0,
        "difference": 0.0
      },
      "coefficient_l1_bound": 0.036997735876737936,
      "normal_P_defect": 4.163336342344337e-17,
      "normal_Q_defect": 3.8899840178926656e-17,
      "signed_identity_defect": 1.5157146371347352e-15,
      "schur_min_eigenvalue": 0.00044006987696445723,
      "gram_Q_condition": 13.327586346026695,
      "weights_P_mass": 0.9999999999999999,
      "weights_Q_mass": 1.0000000000000002
    },
    {
      "period": 12,
      "cutoff": 4,
      "dimension": 5,
      "fixed_modulus": 2,
      "omega": 0.024296588281405768,
      "maximizing_pair": [
        8,
        6
      ],
      "residual_P_squared": 0.05726192213030233,
      "residual_Q_squared": 0.040239959148642535,
      "displacement_sup": 0.02943611597610236,
      "screened_kernel_diameter": 0.5531331793265798,
      "cauchy_bound": 0.08046632669286616,
      "head_omega": 0.022240178858599607,
      "head_cauchy_bound": 0.07686437428687555,
      "actual_carry_test": {
        "L": 60,
        "t": 4,
        "k": 1,
        "endpoint": 0.0,
        "terms": [],
        "signed_sum": 0,
        "difference": 0.0
      },
      "coefficient_l1_bound": 0.10982572294319498,
      "normal_P_defect": 1.1275702593849246e-16,
      "normal_Q_defect": 6.915415578399592e-17,
      "signed_identity_defect": 3.3063829452117943e-15,
      "schur_min_eigenvalue": 4.756184376633621e-05,
      "gram_Q_condition": 46.92367528404553,
      "weights_P_mass": 1.0,
      "weights_Q_mass": 1.0000000000000004
    },
    {
      "period": 60,
      "cutoff": 5,
      "dimension": 11,
      "fixed_modulus": 2,
      "omega": 0.04864667078033625,
      "maximizing_pair": [
        19,
        27
      ],
      "residual_P_squared": 0.03331466434309238,
      "residual_Q_squared": 0.022733293839730797,
      "displacement_sup": 0.026493425184127645,
      "screened_kernel_diameter": 1.091601448772892,
      "cauchy_bound": 0.12112487151301557,
      "head_omega": 0.024877455909606834,
      "head_cauchy_bound": 0.06405094900876174,
      "actual_carry_test": {
        "L": 60,
        "t": 4,
        "k": 1,
        "endpoint": 0.0,
        "terms": [],
        "signed_sum": 0,
        "difference": 0.0
      },
      "coefficient_l1_bound": 0.2484367339113381,
      "normal_P_defect": 1.511919929531036e-16,
      "normal_Q_defect": 5.770666063054097e-17,
      "signed_identity_defect": 1.4546523707803516e-14,
      "schur_min_eigenvalue": 3.3560564428741374e-07,
      "gram_Q_condition": 389.37429496948727,
      "weights_P_mass": 1.0000000000000002,
      "weights_Q_mass": 0.9999999999999999
    },
    {
      "period": 420,
      "cutoff": 7,
      "dimension": 23,
      "fixed_modulus": 2,
      "omega": 0.12241304051555885,
      "maximizing_pair": [
        258,
        220
      ],
      "residual_P_squared": 0.022253370428196022,
      "residual_Q_squared": 0.014673609332859118,
      "displacement_sup": 0.06493469683197187,
      "screened_kernel_diameter": 2.6273798640786405,
      "cauchy_bound": 0.23827159434306003,
      "head_omega": 0.024587601534326833,
      "head_cauchy_bound": 0.0515026702184676,
      "actual_carry_test": {
        "L": 60,
        "t": 4,
        "k": 1,
        "endpoint": -0.013162312196405299,
        "terms": [
          [
            7,
            -0.028810058795373683
          ],
          [
            21,
            0.027433905424951527
          ]
        ],
        "signed_sum": -0.0013761533704221562,
        "difference": -0.01453846556682745
      },
      "coefficient_l1_bound": 0.6175509016770845,
      "normal_P_defect": 1.7357229748545672e-16,
      "normal_Q_defect": 1.6505622823376198e-16,
      "signed_identity_defect": 4.925573837688546e-14,
      "schur_min_eigenvalue": 9.470996015815657e-10,
      "gram_Q_condition": 3752.75494112851,
      "weights_P_mass": 1.0000000000000009,
      "weights_Q_mass": 1.0000000000000002
    },
    {
      "period": 840,
      "cutoff": 8,
      "dimension": 31,
      "fixed_modulus": 2,
      "omega": 0.14051448675884876,
      "maximizing_pair": [
        320,
        520
      ],
      "residual_P_squared": 0.021916088144068115,
      "residual_Q_squared": 0.014431688950549906,
      "displacement_sup": 0.07311764574520106,
      "screened_kernel_diameter": 3.3794985033706597,
      "cauchy_bound": 0.30414822247443485,
      "head_omega": 0.025894806133677173,
      "head_cauchy_bound": 0.05324156903858896,
      "actual_carry_test": {
        "L": 60,
        "t": 4,
        "k": 1,
        "endpoint": -0.018227030523754132,
        "terms": [
          [
            7,
            -0.027339347800424907
          ],
          [
            8,
            -0.0004241018467605884
          ],
          [
            21,
            0.026982319613556377
          ]
        ],
        "signed_sum": -0.0007811300336291183,
        "difference": -0.019008160557383236
      },
      "coefficient_l1_bound": 0.8504944112971095,
      "normal_P_defect": 7.052713956194525e-16,
      "normal_Q_defect": 5.310394712263215e-16,
      "signed_identity_defect": 1.1991796444732472e-13,
      "schur_min_eigenvalue": 1.1795816268215562e-10,
      "gram_Q_condition": 9023.058112456063,
      "weights_P_mass": 1.0000000000000007,
      "weights_Q_mass": 0.9999999999999987
    },
    {
      "period": 2520,
      "cutoff": 9,
      "dimension": 47,
      "fixed_modulus": 2,
      "omega": 0.16465487535316292,
      "maximizing_pair": [
        1544,
        1356
      ],
      "residual_P_squared": 0.019745728890380447,
      "residual_Q_squared": 0.012890163030660588,
      "displacement_sup": 0.08527016078247414,
      "screened_kernel_diameter": 5.008204730595958,
      "cauchy_bound": 0.4278289453568233,
      "head_omega": 0.022762723576205804,
      "head_cauchy_bound": 0.053349000694836834,
      "actual_carry_test": {
        "L": 60,
        "t": 4,
        "k": 1,
        "endpoint": -0.012568753252070209,
        "terms": [
          [
            7,
            -0.027997707046477083
          ],
          [
            8,
            -0.0012044489347194653
          ],
          [
            9,
            0.008289626697761685
          ],
          [
            21,
            0.03277841702790418
          ],
          [
            63,
            -0.016082819160847445
          ]
        ],
        "signed_sum": -0.004216931416378125,
        "difference": -0.016785684668448365
      },
      "coefficient_l1_bound": 1.4857139108467656,
      "normal_P_defect": 7.110755036020554e-16,
      "normal_Q_defect": 6.67282973786722e-16,
      "signed_identity_defect": 5.378163192570895e-13,
      "schur_min_eigenvalue": 4.349961109216628e-12,
      "gram_Q_condition": 32510.240690350452,
      "weights_P_mass": 1.0000000000000027,
      "weights_Q_mass": 0.9999999999999996
    }
  ],
  "counterexamples": {
    "binary_digit_sum_carry": {
      "L": 2,
      "t": 1,
      "k": 7,
      "endpoint": 3,
      "terms": [],
      "signed_sum": 0,
      "difference": 3
    },
    "escaping_prime_power": {
      "L": 60,
      "t": 4,
      "k": 1,
      "endpoint": 0.5,
      "terms": [
        [
          8,
          -1.0
        ]
      ],
      "signed_sum": -1.0,
      "difference": -0.5
    },
    "endpoint_required": {
      "L": 60,
      "t": 1,
      "k": 1,
      "endpoint": 0.5,
      "terms": [],
      "signed_sum": 0,
      "difference": 0.5
    },
    "binary_fixed_modulus_2": [
      {
        "J": 2,
        "pair": [
          3,
          1
        ],
        "difference": 1,
        "norm_tail_P_upper": 1.7071067811865475
      },
      {
        "J": 4,
        "pair": [
          15,
          1
        ],
        "difference": 3,
        "norm_tail_P_upper": 0.8535533905932737
      },
      {
        "J": 8,
        "pair": [
          255,
          1
        ],
        "difference": 7,
        "norm_tail_P_upper": 0.21338834764831843
      },
      {
        "J": 16,
        "pair": [
          65535,
          1
        ],
        "difference": 15,
        "norm_tail_P_upper": 0.013336771728019902
      },
      {
        "J": 32,
        "pair": [
          4294967295,
          1
        ],
        "difference": 31,
        "norm_tail_P_upper": 5.209676456257774e-05
      }
    ]
  },
  "exact_rational_carry_checks": 54,
  "binary_approximants_fail_target_one_normal_equations": [
    {
      "J": 2,
      "P_target_one_normal_defect": 0.05485307163968446,
      "Q_target_one_normal_defect": 0.06960503863326979
    },
    {
      "J": 4,
      "P_target_one_normal_defect": -0.07183377029403908,
      "Q_target_one_normal_defect": -0.04461654974618959
    },
    {
      "J": 8,
      "P_target_one_normal_defect": -0.13480883302546218,
      "Q_target_one_normal_defect": -0.09508603919623394
    }
  ]
}
```

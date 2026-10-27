# Complete-tail squarefree moment diagnostics

Companion to SquarefreeMomentBudgetResearch20261027.md. These scripts were run
with Python, NumPy and SciPy. The interval scripts validate the floating-point
candidates with outward-rounded Decimal bounds. They are computer-assisted
certificates, not Lean kernel proofs. Save the following Python blocks using
the displayed filenames in one directory; run each as `python filename.py`.
The complete progression-tail justification is in the research memorandum.

## q_squarefree_complete_moments.py

```python
"""Diagnostic only: actual squarefree Q projections with complete periodic tails.

No physical tail is truncated when constructing G, K, or the reported moments.
Double precision special functions/linear solves are numerical evidence, not
Lean proofs or interval certificates. Dependencies: NumPy, SciPy.
"""
import json
from math import lcm, pi, log

import numpy as np
from scipy.linalg import solve
from scipy.special import digamma, polygamma

ZETA_TWO = pi**2 / 6


def squarefree(n):
    return all(n % (d * d) for d in range(2, int(n**0.5) + 1))


def residue_weights(period):
    """Complete weights for n=a+kL, 1<=a<=L, k>=0."""
    a = np.arange(1, period + 1, dtype=float)
    q = polygamma(1, a / period) / (ZETA_TWO * period**2)
    qb = q + (digamma(a / period) - digamma((a + 1) / period)) / (
        ZETA_TWO * period
    )
    return a, q, qb


def pair(d, e):
    a, q, qb = residue_weights(lcm(d, e))
    g = (a % d) / d * (a % e) / e
    return q @ g, qb @ g


def experiment(cutoff):
    conductors = [d for d in range(2, cutoff + 1) if squarefree(d)]
    G = np.array([[pair(d, e)[0] for e in conductors] for d in conductors])
    K = np.array([[pair(d, e)[1] for e in conductors] for d in conductors])
    v, s = [], []
    for d in conductors:
        a, q, qb = residue_weights(d)
        g = (a % d) / d
        v.append(q @ g)
        s.append(qb @ g)
    v, s = np.array(v), np.array(s)
    c = solve(G, v, assume_a="pos")
    beta = solve(G, s - K @ c, assume_a="pos")
    period = lcm(*conductors)
    moments = {kappa: 0.0 for kappa in (1, 10, 100, 300, 1000)}
    max_correction, correction_site, max_raw, raw_site = 0.0, 0, 0.0, 0
    for start in range(1, period + 1, 100000):
        a = np.arange(start, min(period + 1, start + 100000), dtype=float)
        q = polygamma(1, a / period) / (ZETA_TWO * period**2)
        b = sum(coef * (a % d) / d for coef, d in zip(beta, conductors))
        residual = 1 - sum(coef * (a % d) / d for coef, d in zip(c, conductors))
        raw = np.abs(residual) / (a + 1)
        for kappa in moments:
            moments[kappa] += float(q @ np.exp(kappa * np.abs(b)))
        i, j = np.argmax(np.abs(b)), np.argmax(raw)
        if abs(b[i]) > max_correction:
            max_correction, correction_site = float(abs(b[i])), int(a[i])
        if raw[j] > max_raw:
            max_raw, raw_site = float(raw[j]), int(a[j])
    head = np.arange(1, 101, dtype=float)
    bh = sum(coef * (head % d) / d for coef, d in zip(beta, conductors))
    head_moment = float(np.sum(np.exp(np.abs(bh)) / (ZETA_TWO * head**2)))
    output = {
        "conductor_cutoff": cutoff,
        "repository_stage": cutoff - 1,
        "conductors": conductors,
        "period": period,
        "residual_energy": float(1 - v @ c),
        "correction_energy": float(beta @ G @ beta),
        "correction_mean": float(v @ beta),
        "gram_condition_number": float(np.linalg.cond(G)),
        "complete_moments": moments,
        "head_100_moment_kappa_1": head_moment,
        "omitted_tail_100_kappa_1": moments[1] - head_moment,
        "max_correction": max_correction,
        "correction_max_site": correction_site,
        "max_raw_smoothed_residual": max_raw,
        "raw_max_site": raw_site,
        "optimizer_coefficients": [float(x) for x in c],
        "correction_coefficients": [float(x) for x in beta],
    }
    if correction_site:
        output["kappa_10000_log_lower_correction_moment"] = (
            10000 * max_correction - log(ZETA_TWO) - 2 * log(correction_site)
        )
        output["kappa_10000_log_upper_raw_moment"] = 10000 * max_raw
    return output


if __name__ == "__main__":
    import sys

    cutoffs = [int(arg) for arg in sys.argv[1:]] or [2, 3, 5, 7, 10, 13, 14, 17]
    for cutoff in cutoffs:
        print(json.dumps(experiment(cutoff), sort_keys=True), flush=True)
```

## q_squarefree_interval_certificate.py

```python
"""Directed-decimal certificate for failure of raw-to-projected Jensen at H=17.

This is a computer-assisted certificate, not a Lean kernel check. All complete
Gram entries are enclosed using rational sums and elementary integral tails.
For positive convex f on [K,infinity), the trapezoidal error per unit interval
is (1/2) integral t(1-t) f''(K+j+t) dt, hence between zero and
(1/8) integral f''. For f(t)=(a+Lt)^(-p), its tail sum is therefore between
I+f(K)/2 and I+f(K)/2+p*L/(8*x^(p+1)), where x=a+KL and
I=1/(L*(p-1)*x^(p-1)). For the B weight use S3-S4 <= SB <= S3.

Normalization zeta(2) cancels from both normal systems. No special function
is used for interval Gram entries. NumPy/SciPy only choose approximate inverse
and coefficient candidates; the interval residual check validates those.
"""
from decimal import Decimal as D, Context, ROUND_FLOOR, ROUND_CEILING
from functools import lru_cache
from math import lcm
import json
import numpy as np
from q_squarefree_complete_moments import experiment, pair, ZETA_TWO

LOW = Context(prec=45, rounding=ROUND_FLOOR)
HIGH = Context(prec=45, rounding=ROUND_CEILING)
K_TERMS = 1000


class I:
    def __init__(self, lo, hi=None):
        self.lo, self.hi = D(str(lo)), D(str(lo if hi is None else hi))
    def __add__(self, other):
        if not isinstance(other, I): other = I(other)
        return I(LOW.add(self.lo, other.lo), HIGH.add(self.hi, other.hi))
    __radd__ = __add__
    def __neg__(self): return I(self.hi.copy_negate(), self.lo.copy_negate())
    def __sub__(self, other): return self + (-other if isinstance(other, I) else -I(other))
    def __rsub__(self, other): return I(other) - self
    def __mul__(self, other):
        if not isinstance(other, I): other = I(other)
        pairs = [(x,y) for x in (self.lo,self.hi) for y in (other.lo,other.hi)]
        return I(min(LOW.multiply(x,y) for x,y in pairs), max(HIGH.multiply(x,y) for x,y in pairs))
    __rmul__ = __mul__
    def __truediv__(self, other):
        if not isinstance(other, I): other = I(other)
        assert other.lo > 0
        return self * I(LOW.divide(D(1),other.hi), HIGH.divide(D(1),other.lo))
    def abs_upper(self): return max(self.lo.copy_abs(),self.hi.copy_abs())


def tail_power(a, L, p):
    x = a + K_TERMS * L
    center = I(1) / I(L*(p-1)*x**(p-1)) + I(1) / I(2*x**p)
    err = I(p*L) / I(8*x**(p+1))
    return I(center.lo, (center+err).hi)


@lru_cache(None)
def weights(L):
    w, b = [], []
    for a in range(1,L+1):
        wl=wh=bl=bh=D(0)
        for k in range(K_TERMS):
            n=a+k*L
            den=D(n*n)
            wl=LOW.add(wl, LOW.divide(D(1),den))
            wh=HIGH.add(wh, HIGH.divide(D(1),den))
            denb=D(n*n*(n+1))
            bl=LOW.add(bl, LOW.divide(D(1),denb))
            bh=HIGH.add(bh, HIGH.divide(D(1),denb))
        s2,s3,s4=tail_power(a,L,2),tail_power(a,L,3),tail_power(a,L,4)
        w.append(I(wl,wh)+s2)
        b.append(I(bl,bh)+I((s3-s4).lo,s3.hi))
    return w,b


def entries(d,e=None):
    L=d if e is None else lcm(d,e)
    w,b=weights(L)
    g=I(0);h=I(0)
    for a in range(1,L+1):
        factor=I(a%d)/I(d) if e is None else I((a%d)*(a%e))/I(d*e)
        g+=w[a-1]*factor;h+=b[a-1]*factor
    return g,h


def matvec(A,v):return [sum((a*x for a,x in zip(row,v)),I(0)) for row in A]
def norm_inf_vector(v):return max(x.abs_upper() for x in v)
def norm_inf_matrix(A):
    return max(sum((I(x.abs_upper()) for x in row),I(0)).hi for row in A)


def main():
    numerical=experiment(17)
    ds=numerical['conductors'];size=len(ds)
    c=[I(x) for x in numerical['optimizer_coefficients']]
    beta=[I(x) for x in numerical['correction_coefficients']]
    G=[];B=[]
    for d in ds:
        grow=[];brow=[]
        for e in ds:
            g,b=entries(d,e);grow.append(g);brow.append(b)
        G.append(grow);B.append(brow)
    v,s=map(list,zip(*(entries(d) for d in ds)))
    numerical_G=np.array([[pair(d,e)[0]*ZETA_TWO for e in ds] for d in ds])
    A=[[I(float(x)) for x in row] for row in np.linalg.inv(numerical_G)]
    AG=[[sum((A[i][k]*G[k][j] for k in range(size)),I(0)) for j in range(size)] for i in range(size)]
    defect=[[I(int(i==j))-AG[i][j] for j in range(size)] for i in range(size)]
    eps=norm_inf_matrix(defect)
    assert eps<1
    inverse_bound=(I(norm_inf_matrix(A))/(I(1)-I(eps))).hi
    residual_c=[x-y for x,y in zip(v,matvec(G,c))]
    error_c=(I(inverse_bound)*I(norm_inf_vector(residual_c))).hi
    residual_b=[x-y-z for x,y,z in zip(s,matvec(B,c),matvec(G,beta))]
    error_b=(I(inverse_bound)*(I(norm_inf_vector(residual_b))+I(norm_inf_matrix(B))*I(error_c))).hi
    # All physical legal atoms have absolute value <=1, so coefficient errors
    # give global pointwise errors size*error_c and size*error_b.
    global_c_error=(I(size)*I(error_c)).hi
    global_b_error=(I(size)*I(error_b)).hi
    site=296581
    b_at_site=sum((coef*I(site%d)/I(d) for coef,d in zip(beta,ds)),I(0))
    correction_lower=(b_at_site-I(global_b_error)).lo
    # Numerically maximizing candidates are not used to upper bound raw rB.
    # Check all n<1000 with rational interval arithmetic. For n>=1000 use
    # |r(n)| <= 1+sum|c_d|+global_c_error and division by n+1.
    raw_upper=D(0)
    for n in range(1,1000):
        residual=I(1)-sum((coef*I(n%d)/I(d) for coef,d in zip(c,ds)),I(0))
        bound=((I(residual.abs_upper())+I(global_c_error))/I(n+1)).hi
        raw_upper=max(raw_upper,bound)
    rough=I(1)+sum((I(x.abs_upper()) for x in c),I(0))+I(global_c_error)
    raw_upper=max(raw_upper,(rough/I(1001)).hi)
    # zeta(2)<2 implies Q(site)>1/(2*site^2). To prove moment separation
    # avoid logarithms: e^x >= x^m/m!, so e^36>2*site^2 (m=20 suffices).
    gap=(I(10000)*(I(correction_lower)-I(raw_upper))).lo
    from math import factorial
    assert correction_lower > D("0.0455")  # 91/2000
    assert raw_upper < D("0.0417")  # 417/10000
    assert 36**20 > 2*site**2*factorial(20)
    assert gap>36
    print(json.dumps({
        'precision':45,'tail_terms_per_residue':K_TERMS,
        'approx_inverse_defect_inf_upper':str(eps),
        'inverse_inf_norm_upper':str(inverse_bound),
        'optimizer_coefficient_error_upper':str(error_c),
        'correction_coefficient_error_upper':str(error_b),
        'correction_at_296581_lower':str(correction_lower),
        'raw_smoothed_residual_global_abs_upper':str(raw_upper),
        'kappa10000_pointwise_exponent_gap_lower':str(gap),
        'rounded_correction_lower_strict':'91/2000',
        'rounded_raw_upper_strict':'417/10000',
        'exp36_exceeds_2n_squared_via_term20':True,
        'strict_complete_Jensen_failure_certified':True,
    },indent=2))


if __name__=='__main__':main()
```

## q_squarefree_martingale_obstruction.py

```python
"""Interval proof that consecutive canonical corrections do not preserve mean.

At cutoff2 (stage1), r1 is the even indicator, Br1 is supported on even n,
and g2 is supported on odd n; therefore b1=0 exactly. At cutoff3 (stage2)
this script certifies sum b2(n)/n^2<0. Consequently no filtration can make
the full canonical sequence (b_N) a Q-integrable martingale.
This is a directed-arithmetic certificate, not Lean-verified code.
"""
import json
import numpy as np
from q_squarefree_complete_moments import experiment, pair, ZETA_TWO
from q_squarefree_interval_certificate import (
    I, entries, matvec, norm_inf_matrix, norm_inf_vector,
)


def main():
    numerical = experiment(3)
    ds = numerical["conductors"]
    c = [I(x) for x in numerical["optimizer_coefficients"]]
    beta = [I(x) for x in numerical["correction_coefficients"]]
    G, B = [], []
    for d in ds:
        row = [entries(d, e) for e in ds]
        G.append([x for x, y in row])
        B.append([y for x, y in row])
    v, s = map(list, zip(*(entries(d) for d in ds)))
    candidate = np.linalg.inv(np.array([
        [pair(d, e)[0] * ZETA_TWO for e in ds] for d in ds
    ]))
    A = [[I(float(x)) for x in row] for row in candidate]
    AG = [[sum((A[i][k] * G[k][j] for k in range(2)), I(0))
           for j in range(2)] for i in range(2)]
    defect = [[I(int(i == j)) - AG[i][j] for j in range(2)] for i in range(2)]
    eps = norm_inf_matrix(defect)
    assert eps < 1
    inv = (I(norm_inf_matrix(A)) / (I(1) - I(eps))).hi
    ec = (I(inv) * I(norm_inf_vector([x-y for x,y in zip(v, matvec(G,c))]))).hi
    rb = [x-y-z for x,y,z in zip(s, matvec(B,c), matvec(G,beta))]
    eb = (I(inv) * (I(norm_inf_vector(rb)) + I(norm_inf_matrix(B))*I(ec))).hi
    candidate_mean = sum((x*y for x,y in zip(v,beta)), I(0))
    mean_error = (sum((I(x.abs_upper()) for x in v),I(0))*I(eb)).hi
    lo = (candidate_mean-I(mean_error)).lo
    hi = (candidate_mean+I(mean_error)).hi
    assert hi < 0
    print(json.dumps({
        "conductor_cutoff": 3,
        "repository_stage": 2,
        "unnormalized_correction_mean_lower": str(lo),
        "unnormalized_correction_mean_upper": str(hi),
        "negative_Q_correction_mean_certified": True,
        "previous_stage_correction_zero": "analytic parity identity",
        "martingale_mean_preservation_fails": True,
    }, indent=2))


if __name__ == "__main__":
    main()
```

## Recorded output: q_squarefree_interval_certificate.json

```json
{
  "precision": 45,
  "tail_terms_per_residue": 1000,
  "approx_inverse_defect_inf_upper": "3.153678083925605155267257273607268056E-9",
  "inverse_inf_norm_upper": "330.919247822358116506516831165300429968313196",
  "optimizer_coefficient_error_upper": "1.07437841417906242425628211837657780880125043E-8",
  "correction_coefficient_error_upper": "0.00000189500651541787965317514439384270854120815735",
  "correction_at_296581_lower": "0.0455053435113065103276563301941009832275350253",
  "raw_smoothed_residual_global_abs_upper": "0.0416626228373991092533199548273495394573016315",
  "kappa10000_pointwise_exponent_gap_lower": "38.4272067390740107433637536675144377023339380",
  "rounded_correction_lower_strict": "91/2000",
  "rounded_raw_upper_strict": "417/10000",
  "exp36_exceeds_2n_squared_via_term20": true,
  "strict_complete_Jensen_failure_certified": true
}
```

## Recorded output: q_squarefree_martingale_obstruction.json

```json
{
  "conductor_cutoff": 3,
  "repository_stage": 2,
  "unnormalized_correction_mean_lower": "-0.00384696173931535945215470644940173003472073315",
  "unnormalized_correction_mean_upper": "-0.00384695980180041922748260242141155639788449471",
  "negative_Q_correction_mean_certified": true,
  "previous_stage_correction_zero": "analytic parity identity",
  "martingale_mean_preservation_fails": true
}
```

## Recorded output: q_squarefree_complete_moments.jsonl

```json
{"complete_moments": {"1": 1.0000000000000002, "10": 1.0000000000000002, "100": 1.0000000000000002, "300": 1.0000000000000002, "1000": 1.0000000000000002}, "conductor_cutoff": 2, "conductors": [2], "correction_coefficients": [0.0], "correction_energy": 0.0, "correction_max_site": 0, "correction_mean": 0.0, "gram_condition_number": 1.0, "head_100_moment_kappa_1": 0.9939510240173952, "max_correction": 0.0, "max_raw_smoothed_residual": 0.3333333333333333, "omitted_tail_100_kappa_1": 0.006048975982605009, "optimizer_coefficients": [2.0], "period": 2, "raw_max_site": 2, "repository_stage": 1, "residual_energy": 0.2499999999999999}
{"complete_moments": {"1": 1.0044005991047427, "10": 1.04496367216946, "100": 1.5633707247432103, "300": 3.991412984747599, "1000": 165.7011787394518}, "conductor_cutoff": 3, "conductors": [2, 3], "correction_coefficients": [-0.013869280160934203, 0.007835887527833138], "correction_energy": 2.0895029860324437e-05, "correction_max_site": 3, "correction_mean": -0.002338671712213222, "gram_condition_number": 4.918862978859144, "head_100_moment_kappa_1": 0.9983307303511326, "kappa_10000_log_lower_correction_moment": 66.65147592486406, "kappa_10000_log_upper_raw_moment": 1428.5714285714284, "max_correction": 0.0069346400804671015, "max_raw_smoothed_residual": 0.14285714285714285, "omitted_tail_100_kappa_1": 0.0060698687536100415, "optimizer_coefficients": [1.1342801694285147, 1.3851208395422638], "period": 6, "raw_max_site": 6, "repository_stage": 2, "residual_energy": 0.06868528248534755}
{"complete_moments": {"1": 1.0055577332120702, "10": 1.057214552273289, "100": 1.7800584792147265, "300": 6.322500517667397, "1000": 1243.814921187597}, "conductor_cutoff": 5, "conductors": [2, 3, 5], "correction_coefficients": [0.010243554937636604, 0.007368188196925516, -0.003684675242928049], "correction_energy": 3.547951164378278e-05, "correction_max_site": 5, "correction_mean": 0.005441023408891838, "gram_condition_number": 9.98213566887784, "head_100_moment_kappa_1": 0.9994838407352632, "kappa_10000_log_lower_correction_moment": 96.62245320701417, "kappa_10000_log_upper_raw_moment": 1175.1124312445709, "max_correction": 0.010033902933435312, "max_raw_smoothed_residual": 0.11751124312445708, "omitted_tail_100_kappa_1": 0.006073892476807008, "optimizer_coefficients": [0.9752201286242151, 0.9422975612247525, 0.8871064906440018], "period": 30, "raw_max_site": 6, "repository_stage": 4, "residual_energy": 0.02723690103609644}
{"complete_moments": {"1": 1.0073754128485726, "10": 1.076658052874006, "100": 2.173110821975686, "300": 14.312934559308557, "1000": 5338551.36161527}, "conductor_cutoff": 7, "conductors": [2, 3, 5, 6, 7], "correction_coefficients": [0.012150758187861528, 0.013772187206940947, 0.013229616104037835, -0.03585343656223349, 0.008531667939339424], "correction_energy": 6.23756804321269e-05, "correction_max_site": 139, "correction_mean": 0.005976338535013837, "gram_condition_number": 41.88529992047845, "head_100_moment_kappa_1": 1.0012748790437138, "kappa_10000_log_lower_correction_moment": 215.50421702615392, "kappa_10000_log_upper_raw_moment": 630.751843673165, "max_correction": 0.022587086519488604, "max_raw_smoothed_residual": 0.0630751843673165, "omitted_tail_100_kappa_1": 0.006100533804858754, "optimizer_coefficients": [0.9759983336459286, 0.9523771598921541, 0.7581402072154925, -0.44791974744569074, 0.6704298617938311], "period": 210, "raw_max_site": 10, "repository_stage": 6, "residual_energy": 0.017257969990562727}
{"complete_moments": {"1": 1.0073217384837843, "10": 1.0761167684996238, "100": 2.170263434725771, "300": 15.116451182525516, "1000": 11432245.40962516}, "conductor_cutoff": 10, "conductors": [2, 3, 5, 6, 7, 10], "correction_coefficients": [0.011956601819297499, 0.0133520440803882, 0.016299452863139115, -0.03465397230884621, 0.01240411233066572, -0.010835749025565647], "correction_energy": 6.224241627826673e-05, "correction_max_site": 196, "correction_mean": 0.005811431456565862, "gram_condition_number": 49.310481689211485, "head_100_moment_kappa_1": 1.0012208569277203, "kappa_10000_log_lower_correction_moment": 207.88132726386462, "kappa_10000_log_upper_raw_moment": 626.4513672587416, "max_correction": 0.02189352568847964, "max_raw_smoothed_residual": 0.06264513672587416, "omitted_tail_100_kappa_1": 0.00610088155606392, "optimizer_coefficients": [0.9759469806031379, 0.9516882029824095, 0.7658321890492396, -0.4454127241679405, 0.6781037926441521, -0.02327700099261411], "period": 210, "raw_max_site": 10, "repository_stage": 9, "residual_energy": 0.01724870442984039}
{"complete_moments": {"1": 1.0075304707263948, "10": 1.0783767077967017, "100": 2.228345532004519, "300": 20.75954718013593, "1000": 279663389.6288436}, "conductor_cutoff": 13, "conductors": [2, 3, 5, 6, 7, 10, 11, 13], "correction_coefficients": [0.009984150716422932, 0.014076443732372098, 0.01745217021056165, -0.03168398603485217, 0.016062910152418203, -0.02391893278268832, 0.012654279860209516, -0.004396302562326382], "correction_energy": 6.58451027659719e-05, "correction_max_site": 10933, "correction_mean": 0.006416037312532908, "gram_condition_number": 118.02896434173266, "head_100_moment_kappa_1": 1.0014241965239, "kappa_10000_log_lower_correction_moment": 310.61602471738064, "kappa_10000_log_upper_raw_moment": 476.8868896465876, "max_correction": 0.032971280705472034, "max_raw_smoothed_residual": 0.047688688964658756, "omitted_tail_100_kappa_1": 0.006106274202494877, "optimizer_coefficients": [0.9865781064891251, 0.954238958227115, 0.8102239675857996, -0.5445609405419983, 0.5951804817279617, -0.43396048261510795, 0.4451268903640542, 0.18787174358600056], "period": 30030, "raw_max_site": 13, "repository_stage": 12, "residual_energy": 0.01401690119029153}
{"complete_moments": {"1": 1.0068004602541092, "10": 1.070566095513072, "100": 2.068954621938307, "300": 17.414367674106835, "1000": 4433968692.140789}, "conductor_cutoff": 14, "conductors": [2, 3, 5, 6, 7, 10, 11, 13, 14], "correction_coefficients": [0.00881022870818432, 0.013727702881258021, 0.017036386456169752, -0.03303077636638162, 0.015551983509678466, -0.023180671382830243, 0.014146808123178903, 0.013866223909083686, -0.02088060071112912], "correction_energy": 5.502239407320948e-05, "correction_max_site": 21736, "correction_mean": 0.005400967991854669, "gram_condition_number": 183.02648364622925, "head_100_moment_kappa_1": 1.0006870851516843, "kappa_10000_log_lower_correction_moment": 356.08687000141146, "kappa_10000_log_upper_raw_moment": 445.37271143172006, "max_correction": 0.03765580206060946, "max_raw_smoothed_residual": 0.044537271143172005, "omitted_tail_100_kappa_1": 0.006113375102424934, "optimizer_coefficients": [0.988108916057169, 0.9501400675433271, 0.8077969221593935, -0.5784153605387126, 0.6966440341195484, -0.4155983724013854, 0.48178000514752867, 0.4582582639772361, -0.4348707648202879], "period": 30030, "raw_max_site": 19, "repository_stage": 13, "residual_energy": 0.012866478639107282}
{"complete_moments": {"1": 1.006610578479691, "10": 1.0685476825969111, "100": 2.048044191631037, "300": 44.23438301582984, "1000": 3977395642305.2593}, "conductor_cutoff": 17, "conductors": [2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17], "correction_coefficients": [0.009076785692863501, 0.01241894863504366, 0.015879770895828225, -0.03196744212619234, 0.01668196331452335, -0.02262402331086054, 0.014162482912832636, 0.014192312271763569, -0.018406076592808292, -0.013215875704610391, 0.011502508164052395], "correction_energy": 5.237216584470417e-05, "correction_max_site": 296581, "correction_mean": 0.005392793575171107, "gram_condition_number": 267.65912528497296, "head_100_moment_kappa_1": 1.0004968972105932, "kappa_10000_log_lower_correction_moment": 429.56403423270046, "kappa_10000_log_upper_raw_moment": 416.62616928317834, "max_correction": 0.0455261885829761, "max_raw_smoothed_residual": 0.04166261692831783, "omitted_tail_100_kappa_1": 0.006113681269097837, "optimizer_coefficients": [0.9859202577437653, 0.9582223594896019, 0.837471476391925, -0.6068949499436487, 0.6950047707012276, -0.4420908552877887, 0.4544540451975205, 0.44384924974416023, -0.3960159543139133, -0.32343577170020205, 0.38951080164402874], "period": 510510, "raw_max_site": 19, "repository_stage": 16, "residual_energy": 0.011674270791175667}
```

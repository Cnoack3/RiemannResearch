# Reproducible parity-convolution interval computation

External computation, not Lean kernel verification. Save the Python source block as
parity_gram_certificates.py and run `python parity_gram_certificates.py`.
The recorded run used NumPy 2.3.5 and SciPy 1.17.0. The companion JSON retains
rational coefficients and directed interval bounds. A lower endpoint applies
only to its chosen approximant, not to the optimal residual.

```python
"""External interval certificates for actual parity-convolution approximants.

All intervals use directed Decimal rounding. The infinite residue-class
sums use an explicit integral-test tail, not a cutoff interpreted as a norm.
Floating linear algebra only selects rational coefficients; the certificate
re-evaluates that fixed vector independently and does not trust the solve.
The finite residue reduction and Machin identity are mathematical inputs,
not Lean-checked by this script. No infinite-stage convergence is claimed.
"""
from decimal import Decimal, Context, ROUND_FLOOR, ROUND_CEILING
from functools import lru_cache
from math import lcm
import json
import numpy as np
from scipy.special import polygamma

DOWN = Context(prec=60, rounding=ROUND_FLOOR)
UP = Context(prec=60, rounding=ROUND_CEILING)

class I:
    def __init__(self, lo, hi=None):
        self.lo = Decimal(lo)
        self.hi = self.lo if hi is None else Decimal(hi)
    def __add__(self, b):
        b = b if isinstance(b, I) else I(b)
        return I(DOWN.add(self.lo, b.lo), UP.add(self.hi, b.hi))
    __radd__ = __add__
    def __neg__(self):
        return I(self.hi.copy_negate(), self.lo.copy_negate())
    def __sub__(self, b):
        return self + -(b if isinstance(b, I) else I(b))
    def __mul__(self, b):
        b = b if isinstance(b, I) else I(b)
        pairs = [(a,c) for a in (self.lo,self.hi) for c in (b.lo,b.hi)]
        return I(min(DOWN.multiply(a,c) for a,c in pairs),
                 max(UP.multiply(a,c) for a,c in pairs))
    __rmul__ = __mul__
    def __truediv__(self, b):
        b = b if isinstance(b, I) else I(b)
        assert not b.lo <= 0 <= b.hi
        return self * I(DOWN.divide(Decimal(1),b.hi), UP.divide(Decimal(1),b.lo))
    def __pow__(self, n):
        out = I(1)
        for _ in range(n): out = out * self
        return out
    def pair(self):
        return [str(self.lo),str(self.hi)]

def rat(n,d):
    return I(DOWN.divide(Decimal(n),Decimal(d)),UP.divide(Decimal(n),Decimal(d)))

def atan_inverse(q, terms=100):
    assert terms % 2 == 0
    total = sum((rat((-1)**k, (2*k+1)*q**(2*k+1)) for k in range(terms)), I(0))
    next_term = rat(1, (2*terms+1)*q**(2*terms+1))
    return total + I(0,next_term.hi)

PI = 16*atan_inverse(5) - 4*atan_inverse(239)
ZETA2 = PI**2 / 6
TARGET_NORM = 9*PI**2 / 1024
TAIL_TERMS = 128

@lru_cache(None)
def residue_weight(period, residue):
    """Enclose sum_{m>=0} 1/(residue+period*m)^2, 1<=residue<=period."""
    assert 1 <= residue <= period
    head = sum((rat(1,(residue+period*m)**2) for m in range(TAIL_TERMS)), I(0))
    y = residue+period*TAIL_TERMS
    integral = rat(1,period*y)
    first = rat(1,y*y)
    return head + I(integral.lo, UP.add(integral.hi,first.hi))

@lru_cache(None)
def gram_interval(j,k):
    period = lcm(j,k)
    return sum((rat((r%j)*(r%k),j*k)*residue_weight(period,r)
                for r in range(1,period+1)), I(0)) / ZETA2

@lru_cache(None)
def rhs_interval(j):
    odds = range(1,2*j,2)
    return sum((rat((r*s)%j,j)*residue_weight(2*j,r)*residue_weight(2*j,s)
                for r in odds for s in odds), I(0)) / (4*ZETA2)

def gram_float(j,k):
    period = lcm(j,k)
    r = np.arange(1,period+1,dtype=float)
    return np.sum((r%j)/j*(r%k)/k*polygamma(1,r/period)/period**2)/(np.pi**2/6)

def rhs_float(j):
    r = np.arange(1,2*j,2,dtype=float)
    w = polygamma(1,r/(2*j))/(2*j)**2
    return np.sum((np.outer(r,r)%j)/j*np.outer(w,w))/(4*(np.pi**2/6))

def certify(n):
    conductors = list(range(2,n+1))
    g = np.array([[gram_float(j,k) for k in conductors] for j in conductors])
    b = np.array([rhs_float(j) for j in conductors])
    cfloat = np.linalg.solve(g,b)
    decimal_coefficients = [format(x,'.12f') for x in cfloat]
    c = [I(x) for x in decimal_coefficients]
    e = TARGET_NORM
    for i,j in enumerate(conductors):
        e = e - 2*c[i]*rhs_interval(j)
        for t,k in enumerate(conductors):
            e = e + c[i]*c[t]*gram_interval(j,k)
    return {
        'N':n,
        'conductors':conductors,
        'rational_coefficients_decimal':decimal_coefficients,
        'numerical_condition_number_2':float(np.linalg.cond(g)),
        'numerical_optimal_residual_squared':float(9*np.pi**2/1024-b@cfloat),
        'chosen_approximant_residual_squared_interval':e.pair(),
        'certified_upper_bound_on_optimal_residual_squared':str(e.hi),
        'interpretation':'Interval is for the fixed rational vector, not a lower bound on the optimum.'
    }

if __name__ == '__main__':
    result = {
        'status':'external interval computation; not Lean kernel verification',
        'method':'finite residue sums; integral-test tails; directed Decimal rounding',
        'residue_tail_terms':TAIL_TERMS,
        'pi_interval':PI.pair(),
        'q_target_norm_squared_interval':TARGET_NORM.pair(),
        'systems':[certify(n) for n in [2,4,8,16]],
        'infinite_stage_conclusion':'none; membership and zero residual limit remain open'
    }
    print(json.dumps(result,indent=2))
```

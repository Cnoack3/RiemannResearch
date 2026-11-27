# Choosing the mean section and testing the sign of screened parity

Let $P(n)=1/[n(n+1)]$ for $n\ge1$, let $V$ be the closed legal space, and let $M$ be the closed span of the mixed packets. Write $\lambda=\log 2$, $x=J_2/\lambda$, and $g=x-P_M^P x$.

## Which splitting detects RH?

A section of the restricted Pareto mean $\mathbb E_P:V\to\mathbb R$ has the form $s(a)=a(g+m)$ for one $m\in M$. Its squared operator norm satisfies
$$
 \|s\|^2-1=\|g-\mathbf1_H\|_P^2+\|m\|_P^2.
$$
Indeed $s(1)-g\in\ker(\mathbb E_P|_V)=M$, $g\perp M$, and $\mathbb E_P[g]=1$. Thus $g$ is the unique shortest lift of $1$, and the original mean has a contractive section exactly under RH. The projection $P_V:M^{\perp_P}\to\mathbb Rg$ always has an isometric section, the inclusion. The centered snake boundary at $1$ is $[g-\mathbf1_H]$ in $\ker\mathbb E_P/M$, with norm exactly $\|g-\mathbf1_H\|_P$. [Metric lifting](MixedConductorMetricLifting.lean) · [Centered boundary](CenteredMeanSnake.lean)

## A finite sign test

Let $M_L$ be the span of mixed packets through conductor $L$, $g_L=x-P_{M_L}^P x$, and $t^-=\max(-t,0)$. These $g_L$ converge to $g$ in $L^2(P)$. For any integer sequence $K(L)\to\infty$, put
$$
 D_L=\sum_{n=1}^{K(L)} \frac{g_L(n)^-}{n(n+1)}.
$$
The negative-part map is 1-Lipschitz. Cauchy–Schwarz bounds the negative mass omitted after $K$ by $\|g_L\|_P/\sqrt{K+1}$ because the omitted probability is $1/(K+1)$. In particular,
$$
 |D_L-\mathbb E_P[g^-]|\le
 \|g_L-g\|_P+\frac{\|g_L\|_P}{\sqrt{K(L)+1}},\qquad
 \|g_L\|_P\le\|x\|_P=1/\sqrt{\lambda}.
$$
It follows that $D_L\to\mathbb E_P[g^-]$. Each positive site has positive mass; hence a zero limit makes $g(n)\ge0$ for every $n\ge1$. The one-sided rigidity theorem then gives $g=\mathbf1_H$. Conversely RH makes $g=\mathbf1_H$, so the limit is zero.

A second equivalent test is pointwise: for each fixed positive $n$, there are arbitrarily large $L$ with $g_L(n)\ge0$. The good cutoffs can depend on $n$. Coordinate convergence gives $g(n)\ge0$ in this case; under RH every such coordinate converges to $1$. [Sign and section theorems](ScreenedParityNegativeMass.lean) · [One-sided rigidity](ScreenedParityOneSided.lean)

The same norm enclosure bounds the remaining scalar directly, since
$$
 0\le\mathbb E_P[g^-]=(\mathbb E_P[|g|]-1)/2\le(\|g\|_P-1)/2.
$$
The period-5040 trial gives $\mathbb E_P[g^-]<0.01005$; the stronger numerical enclosure below gives $\mathbb E_P[g^-]<0.001274$. The value zero remains to be proved.

The unconditional coordinate bound
$$
 (g(n)-1)^2\le [n(n+1)-1](\|g\|_P^2-1)
$$
and the period-5040 bound $\|g\|_P^2<1000/961$ already force $g(n)>0$ for $1\le n\le4$. The stronger conductor-8192 enclosure implies $\|g\|_P^2<1.0051$, hence positivity through $n=13$ and $g(10)>1/4$. This stronger numerical conclusion uses the independent integer replay of the full rounded head, together with the Lean implication. [Coordinate estimate](ScreenedParityPhysicalBounds.lean) · [Conductor-8192 evidence](../THEOREM_CATALOG_MIXED_CONDUCTOR_CRT_20261109.md#conductor-8192-enclosure-of-the-normalized-projection)

## A negative finite projection

At cutoff $12$ the mixed conductors are $6,10,12$. Let $G_{ij}=\langle J_i,J_j\rangle_P$, $d_i=\langle J_i,J_2\rangle_P$ for these three indices and $b=G^{-1}d$. Then $\lambda g_{12}=J_2-b_6J_6-b_{10}J_{10}-b_{12}J_{12}$. An exact rational enclosure gives
$$
 0.059<b_{12}<0.061,\qquad 0.007<3b_6+4b_{12}<0.013 .
$$
In the order $J_2,J_6,J_{10},J_{12}$ the rows at sites $10$ and $30$ are $(0,3,0,4)$ and $(0,0,0,4)$. Thus $g_{12}(10)<0$, $g_{12}(30)<0$, and the diagonal sum with $K(12)=12$ is already positive. At cutoff 10 both fitted coefficients belong to $(-1/4,0)$. Each of the two packet entries is nonnegative at the even sites and at least $-1$ at the odd sites. Thus $g_{10}$ is nonnegative on its full period. In particular $D_{10}=0<D_{12}$ for the diagonal heads. Finite screening does not preserve positivity at every stage, and this negative-mass statistic is not monotone decreasing.

The following standalone Python 3 certificate uses integer and rational arithmetic. For every Gram entry it rounds the signed summands downward through $N$ at fixed scale, bounds the total rounding error by $N$ units, and bounds the remaining tail between the extreme products in one period times $1/(N+1)$. The determinant is affine in each of its nine entries, so its extrema on their interval box occur at corners. The lower determinant is positive. Cramer's rule gives the stated sign and coefficient bounds. This is an external arithmetic verification.

~~~python
"""Exact sign certificate for screening parity against conductors 6, 10 and 12."""
from fractions import Fraction as Q
from itertools import product
from functools import cache

N = 12_000
SCALE = 10**12


def row(n):
    parity = n % 2
    return (parity, n%6 - n%3 - parity, n%10 - n%5 - parity,
            n%12 - n%6 - n%4 + parity)


period = [row(n) for n in range(60)]


@cache
def entry(i, j):
    products = [r[i]*r[j] for r in period]
    total = sum((SCALE * products[n%60]) // (n*(n+1)) for n in range(1, N+1))
    tail_mass = Q(1, N+1)
    return (Q(total, SCALE) + min(products)*tail_mass,
            Q(total + N, SCALE) + max(products)*tail_mass)


def det3(a):
    x, y, z, u, v, w, r, s, t = a
    return x*(v*t-w*s) - y*(u*t-w*r) + z*(u*s-v*r)


def det_bounds(cols):
    # A determinant is affine in each entry separately.
    corners = product(*(entry(i, j) for i in (1, 2, 3) for j in cols))
    values = [det3(a) for a in corners]
    return min(values), max(values)


def two_bounds(cols):
    corners = product(*(entry(i, j) for i in (1, 2) for j in cols))
    determinants = [a*d - b*c for a, b, c, d in corners]
    return min(determinants), max(determinants)


two_lo, two_hi = two_bounds((1, 2))
assert two_lo > 0
# Each fitted coefficient is between -1/4 and 0.
for cols in ((0, 2), (1, 0)):
    a, b = two_bounds(cols)
    assert -two_lo/4 < a <= b < 0
# Even sites have two nonnegative packet entries; odd sites have entries >= -1.
assert all(r[1] >= -r[0] and r[2] >= -r[0] for r in period)

lo, hi = det_bounds((1, 2, 3))
num_lo, num_hi = det_bounds((1, 2, 0))
assert lo > 0 and num_lo > 0
assert Q(59, 1000) < num_lo / hi <= num_hi / lo < Q(61, 1000)
assert row(30) == (0, 0, 0, 4)
num6_lo, num6_hi = det_bounds((0, 2, 3))
# Both coefficients have the same positive denominator.
assert 3*num6_lo + 4*num_lo > Q(7, 1000)*hi
assert 3*num6_hi + 4*num_hi < Q(13, 1000)*lo
assert row(10) == (0, 3, 0, 4)
# Earlier conductor-8192 evidence gives rho > 0.66151243224796.
# Use an exact lower bound on log(2) from 2*atanh(1/3).
rho = Q(66151243224796, 10**14)
lower_log = 2*sum(Q(1,(2*j+1)*3**(2*j+1)) for j in range(20))
assert 1/lower_log - rho**2 < Q(10051,10000)
assert 109*Q(51,10000) < Q(9,16)
assert (13*14-1)*Q(51,10000) < 1
print("0.059 < b12 < 0.061; 0.007 < 3*b6+4*b12 < 0.013; g12(10) and g12(30) are negative.")
~~~

The open estimate is $D_L\to0$, even for the single choice $K(L)=L$. The tower gives convergence to the full negative mass. Establishing the value of that limit would prove RH.

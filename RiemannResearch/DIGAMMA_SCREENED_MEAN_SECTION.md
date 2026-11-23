# Computing the screened section along the Pareto ladder

Let $H=L^2(P)$ with $P(k)=1/[k(k+1)]$ on the positive integers. Write
$r_d(k)=k\bmod d$ and $J_q=\sum_{d\mid q}\mu(q/d)r_d$, where $\mu$ is the Möbius
function. Let $V$ be the closed span of the packets $J_q$, $q\ge2$, and $M$ the closed span
of mixed packets, those with at least two distinct prime divisors. Write
$\mathbf1$ for the ambient constant. In the upper row of the mean ladder the
orthogonal mean-one section sends $1$ to $u=(I-P_M)J_2/\log 2$. The lower
row has the section $1\mapsto\mathbf1$. At any stage with denominator
$S\subseteq M$, the connecting map sends $1$ to the class of the centered
upper lift. Passing through the canonical double-quotient isomorphism gives
$[u-\mathbf1]\in\mathbf1^\perp/M$.

## From the recurrence to the full vector

For $q,s\ge2$ take $L=\operatorname{lcm}(q,s)$ and
$h(r)=J_q(r)J_s(r)$. The mass of the class $r$, $1\le r\le L$, is
$$
W_L(r)=\frac{\psi((r+1)/L)-\psi(r/L)}{L}.
$$
Summing $h(r)W_L(r)$ by parts gives
$$
G_{qs}=-\frac1L\sum_{r=1}^L (h(r)-h(r-1))\psi(r/L).
$$
Indeed $h(L)=h(0)=0$. For a general periodic profile the same computation
has the additional term $h(0)$, because
$\psi(1+1/L)-\psi(1/L)=L$. This term matters for the squared residual.
[Digamma recurrence, NIST DLMF 5.5.2](https://dlmf.nist.gov/5.5.E2)

For the conductors $2,\ldots,N$ let $G_N$ be this matrix,
$\mu_q=\Lambda(q)$, $x_q(k)=J_q(k)$, $c_N=G_N^{-1}\mu$, and
$m_N=\mu^\top c_N$. The packet family is linearly independent and
$m_N>0$ for $N\ge2$. Its projection of $\mathbf1$ is
$p_N=\sum_q(c_N)_qJ_q$. Dividing by its mean gives the finite lift
$U_N=p_N/m_N$. The Hilbert projections tend to $P_V\mathbf1$, and
$P_V\mathbf1=(1-E)u$, where $E=\|\mathbf1-P_V\mathbf1\|_P^2<1$.
In particular,
$$
u(k)=\lim_{N\to\infty}\frac{x(k)^\top G_N^{-1}\mu}{\mu^\top G_N^{-1}\mu},
\qquad \|u\|_P^2=\lim_{N\to\infty}\frac1{\mu^\top G_N^{-1}\mu}.
$$

For the common period $L_N=\operatorname{lcm}(1,\ldots,N)$ put
$h_N(r)=(1-U_N(r))^2$ and
$A_N=L_N^{-1}\sum_{r=1}^{L_N}(h_N(r)-h_N(r-1))\psi(r/L_N)$.
Here the sequence of packet values at zero is zero, so $h_N(0)=1$.
Tracing the finite lift through any quotient stage and using orthogonality gives
$$
1-A_N=\|U_N-\mathbf1\|_P^2
     =\|u-\mathbf1\|_P^2+\|U_N-u\|_P^2.
$$
In fact $A_N=2-1/m_N$, hence $A_N\to1-\|u-\mathbf1\|_P^2$. Showing that this limit is $1$
would prove the ambient boundary vanishes.

## The two-prime calculation

Write $a=\log2$, $b=\log3$, and $c=\pi/(3\sqrt3)$. For $J_2J_3$ only
the classes $1$ and $5$ modulo $6$ contribute, with values $1$ and $2$.
Reflection and duplication reduce $W_6(1)+2W_6(5)$ to $a+b/2-c$.
The other two Gram entries are $a$ and $2b-c$. Since
$J_p=P_MJ_p+(\log p)u$ for each prime,
$$
\|u\|_P^2=
\frac{a+b/2-c-\langle P_MJ_2,P_MJ_3\rangle_P}{ab}.
$$
Since $\langle u,\mathbf1\rangle_P=\|\mathbf1\|_P^2=1$, the deficit has an exact sign and size,
$$
a+b/2-c-ab-\langle P_MJ_2,P_MJ_3\rangle_P=ab\,\|u-\mathbf1\|_P^2.
$$
The remaining arithmetic inequality is $\langle P_MJ_2,P_MJ_3\rangle_P\ge a+b/2-c-ab$.
It would force the squared norm on the right to vanish.

## An unconditional enclosure for the first coordinate

Let $Q=I-P_V$ and $z_k=\mathbf1_{\{k\}}/P(k)-\mathbf1$.
The rank-one identity for $P_V\mathbf1$ gives
$(1-E)(u(k)-1)=-\langle Q\mathbf1,Qz_k\rangle_P$. Polarization yields,
for every real $t$,
$$
4t(1-E)(u(k)-1)=\|Q(t\mathbf1-z_k)\|_P^2-\|Q(t\mathbf1+z_k)\|_P^2 .
$$
The two norms are distances in $H/V$. To bound them, any finite legal trials
are allowed. At $k=1$ and $t=2$ the two targets are
$3\mathbf1-2\mathbf1_{\{1\}}$ and $\mathbf1+2\mathbf1_{\{1\}}$.
Let $e_0,e_+,e_-$ bound the respective squared errors for
$\mathbf1$, $\mathbf1+2\mathbf1_{\{1\}}$, and $3\mathbf1-2\mathbf1_{\{1\}}$.
If $e_0<1$, the resulting bounds are
$$
1-\frac{e_+}{8(1-e_0)}\le u(1)\le1+\frac{e_-}{8(1-e_0)}.
$$

Möbius inversion gives $r_d=\sum_{q\mid d}J_q$, so each finite residue trial lies in $V$.
Rounded residue coefficients of conductors $2,\ldots,200$ give
$e_0<0.0090431$, $e_+<0.1227351$, and $e_-<0.0185615$.
The certificate sums the first five million positive sites using integer
rounding upwards. It bounds the complete remaining tail by the squared
maximum residual divided by $5{,}000{,}001$. All coefficients, thresholds
and comparisons in the checker are rational. The resulting enclosure is
$$
0.98451<u(1)<1.00235.
$$
The quotient identities and the implication from the three errors are Lean
theorems. The numerical endpoint comparisons use the separate exact-arithmetic
checker below. [Lean declarations](RH/CenteredMeanDigammaSection.lean)

## A finite section takes a negative value

One way to try to prove that $u=\mathbf1$ is to show all finite normalized sections
are nonnegative and take their sitewise limit. The finite sign assertion fails already
for conductors $2,\ldots,11$. In fact $U_{11}(9856)<-1/20$.

Work in the raw residue basis, and put $x(k)=(r_d(k))_{d=2}^{11}$.
Let $G=\mathbb E_P[x x^\top]$ and $B=\sum_{k=1}^{10}P(k)x(k)x(k)^\top$.
The $10$ by $10$ residue evaluation matrix $A=(r_d(k))_{1\le k\le10,\,2\le d\le11}$
is invertible, as checked by the explicit columns of its inverse below. Thus
$G\succeq B\succ0$. For a rational trial $v(k)=x(k)^\top c$ define
$g=\mathbb E_P[x(1-v)]$. The normal equations for $p_{11}=P_{V_{11}}\mathbf1$ give
$p_{11}(k)-v(k)=x(k)^\top G^{-1}g$. By Cauchy–Schwarz for $G^{-1}$ and
$G^{-1}\preceq B^{-1}$, at $x=x(9856)$ we have
$$
|p_{11}(9856)-v(9856)|^2\le
(x^\top B^{-1}x)\,\|g\|_\infty^2\sum_{ij}|(B^{-1})_{ij}|.
$$
The two matrix factors are $9932/75$ and $15776/225$, whose product is less
than $97^2$. The trial below gives $v(9856)=-29691/250000$ and
$\|g\|_\infty\le1822720525829/4000040000000000$. Hence $p_{11}(9856)<-1/20$.
Dividing by $m_{11}\in(0,1]$ preserves the upper bound. The sign of the limiting
coordinate $u(9856)$ remains undetermined by this calculation.

## Exact rational certificate

Run this Python 3 program to reproduce the three squared-error bounds, both
first-coordinate endpoints, and the upper bound for the squared norm of $u$.

```python
"""Exact Pareto enclosures for the first site of the screened mean section.

Each table gives integer coefficients of the raw residues k mod d, d = 2,...,200,
in millionths. Digamma Gram solves selected the coefficients. The verification
below uses only integer arithmetic and rational inequalities.
"""

from array import array
from fractions import Fraction

HEAD = 5_000_000
SCALE = 10**6
GRID = 10**18

ONE_COEFFICIENTS = tuple(map(int, """
479029 317360 19147 172705 -124147 113307 1111 1194 -65731 64091 -5354 52929 -43386 -40760
-2069 37663 -1183 32733 -5424 -24727 -23662 24999 -214 78 -19592 -878 -1457 19423 13784 16010
1389 -16564 -11927 -14263 2032 14564 -14674 -12232 2192 11380 8794 9037 -1269 -291 -8607 8877
236 347 888 -8801 -1573 9148 1504 -8017 730 -6699 -7973 7005 386 6972 -5689 -290 -399 -6824
8103 6544 -2447 -7135 5113 5309 -1905 4923 -4811 157 566 -4319 4077 4529 1801 160 -4750 3722
766 -4756 -2258 -5071 212 4648 686 -4047 490 -4169 -2582 -3388 -289 4200 60 -245 2804 1067
2469 2098 -109 2465 -3223 1835 -895 1266 2145 -2759 -348 2270 4080 -1435 767 142 -3343 -2070
975 19 -2349 -1703 -852 50 -30 1875 684 -1858 2138 1772 -693 -1582 -2797 354 821 1827 2429
1775 567 -1128 -1788 -1355 709 -2181 -1990 163 -120 1141 -561 919 -73 169 1919 -1021 825 1312
-1640 -1560 -1229 -1470 -223 1214 -184 1739 -1134 909 -286 -57 1458 -715 -358 1648 2297 -3 32
-863 -2130 1428 -235 1077 1650 -1507 -379 -1410 1792 -1005 -443 -115 1712 1145 196 1335 -1723
1158 -681 738 -382 938 -4394
""".split()))

PLUS_COEFFICIENTS = tuple(map(int, """
2388856 946059 -398121 479720 -653704 311000 -1062 -16408 -330957 174164 100262 144981
-217564 -120309 -7981 102593 5656 87632 43765 -73895 -117609 68965 376 19 -98521 -3710 38190
49638 77489 44225 2801 -49718 -62221 -37447 6254 39408 -64281 -37022 7408 27970 51085 22539
17244 1263 -42793 23303 345 1434 2165 -25782 13509 24524 4044 -23006 1802 -18116 -34400 18804
-13298 19683 -30744 1473 960 -19696 38072 18235 2522 -23364 25495 14816 -6658 11778 -23575
-246 10394 -11257 23553 12507 5415 1749 -20570 10704 -8459 -13004 -13531 -14423 1040 13124
1509 -12033 7186 -13201 -13539 -7824 -126 12575 53 435 10049 1450 13011 4124 287 4990 -12590
4299 -1945 1592 10588 -6394 -1149 3955 14809 -2896 6574 772 -12321 -4134 2199 -537 -10576
-3405 3473 137 -1472 3229 1006 -3384 10131 3500 -8153 -2706 -10637 1038 3064 3986 12125 3691
-3882 -2453 -8031 -2452 2640 -4350 -7912 9 4271 1342 -843 1896 -305 406 7265 -1799 -2834 3220
-6908 -3972 -3571 -3159 -950 2469 3631 4487 -5930 1418 -591 240 6946 -1937 2298 3205 8921
-314 13 -1968 -7929 3086 -1148 2147 7145 -3711 -964 -3514 8131 -2314 1491 -184 6207 2597 183
2622 -7122 2873 -1719 1410 -1728 1804 -14878
""".split()))

MINUS_COEFFICIENTS = tuple(map(int, """
-472741 323382 474709 211100 157114 142229 5506 21182 68035 82199 -121679 66737 44018 -42732
-294 48059 -10390 43298 -65460 -25014 22960 31031 -1233 294 20153 199 -44018 28053 -22354
19814 2755 -16538 14515 -19604 1875 18850 5585 -11907 1359 17549 -15911 13608 -22321 -2426
8363 12205 598 -48 1385 -9423 -19803 12069 1970 -9062 1120 -8678 2507 9214 14843 8206 7989
-2633 -2555 -7598 -5660 7942 -12312 -5175 -5042 6421 -962 7916 4332 876 -8130 -6017 -7246
5609 1789 -1110 1570 4185 11524 -6020 4499 -5861 -193 5467 1235 -4157 -5227 -3476 3213 -5729
-1030 4224 187 -1416 1167 2819 -3137 4266 -722 4872 -304 3041 -1635 3472 -2008 -4642 -241
5124 1513 -2844 -3505 -204 -1050 -4146 1702 614 1179 -3409 -6882 61 1352 4270 1732 -4050
-1580 3586 5381 -3624 -552 379 221 3321 -2409 3409 6148 -2060 879 -2967 195 -4376 -49 643
-4751 3220 -1401 1778 14 271 412 -2286 6132 2028 347 -2266 -1344 -2720 58 2387 -4367 2470
1395 2219 -552 -470 -1115 -925 -3731 3386 268 303 115 -1483 -591 2624 207 2163 -543 -2318
-552 -2125 -962 -1707 -3264 -275 640 1982 601 2717 231 1759 -1006 1544 200 1947 -2699
""".split()))

def squared_error_upper(coefficients, constant, first_site_shift):
    """Bound the squared distance to constant + first_site_shift times delta_1."""
    assert len(coefficients) == 199 and GRID % SCALE**2 == 0
    differences = array("q", [sum(coefficients)]) * (HEAD + 1)
    lower = upper = 0
    for d, coefficient in enumerate(coefficients, start=2):
        amplitude = coefficient * (d - 1)
        lower += min(0, amplitude)
        upper += max(0, amplitude)
        jump = coefficient * d
        for k in range(d, HEAD + 1, d):
            differences[k] -= jump

    units = trial = 0
    multiplier = GRID // SCALE**2
    for k in range(1, HEAD + 1):
        trial += differences[k]
        target = constant + (first_site_shift if k == 1 else 0)
        residual = SCALE * target - trial
        denominator = k * (k + 1)
        units += (residual**2 * multiplier + denominator - 1) // denominator

    tail_max = max(abs(SCALE * constant - lower), abs(SCALE * constant - upper))
    tail = Fraction(tail_max**2, SCALE**2 * (HEAD + 1))
    return Fraction(units, GRID) + tail


if __name__ == "__main__":
    error_one = squared_error_upper(ONE_COEFFICIENTS, 1, 0)
    error_plus = squared_error_upper(PLUS_COEFFICIENTS, 1, 2)
    error_minus = squared_error_upper(MINUS_COEFFICIENTS, 3, -2)
    assert error_one < 1
    denominator = 8 * (1 - error_one)
    lower = 1 - error_plus / denominator
    upper = 1 + error_minus / denominator
    assert lower > Fraction(98451, 100000)
    assert upper < Fraction(100235, 100000)
    assert 1 / (1 - error_one) < Fraction(100913, 100000)
    print("Squared error upper bounds", error_one, error_plus, error_minus)
    print("Lower bound for u(1)", lower)
    print("Upper bound for u(1)", upper)
    print("Upper bound for the squared norm", 1 / (1 - error_one))
```

### Checking the finite sign calculation

The integer sum uses lower rounding at each of the first 100,000 sites. Adding one grid unit per site bounds the opposite rounding error. The omitted Pareto mass is exactly $1/100001$.

```python
from fractions import Fraction as F

ds = range(2, 12)
coeff = [460076, 297398, 36474, 147131, -81296, 78158, 3716, 11815, -41654, 42668]
scale, grid, head = 10**6, 10**12, 100_000
totals = [0] * len(ds)
for k in range(1, head + 1):
    x = [k % d for d in ds]
    residual = scale - sum(c*r for c, r in zip(coeff, x))
    weight_den = scale * k * (k + 1)
    for i, r in enumerate(x):
        totals[i] += residual * r * grid // weight_den
bound = scale + sum(abs(c)*(d-1) for d, c in zip(ds, coeff))
eps = max(max(abs(F(t, grid)), abs(F(t + head, grid))) +
          F((d-1)*bound, scale*(head+1)) for d, t in zip(ds, totals))

# The j-th column of A inverse fits the point indicator at j on sites 1,...,10.
def inverse_column(j):
    f = [int(k == j) for k in range(11)]
    beta = {}
    for d in range(2, 11):
        earlier = sum(e*b for e, b in beta.items() if d % e == 0)
        beta[d] = (F(f[1] - f[d] + f[d-1]) - earlier) / d
    beta[11] = f[1] - sum(beta.values())
    assert all(sum(beta[d]*(k % d) for d in ds) == f[k] for k in range(1, 11))
    return [beta[d] for d in ds]

cols = [inverse_column(j) for j in range(1, 11)]
winv = [j*(j+1) for j in range(1, 11)]
x = [9856 % d for d in ds]
xx = sum(w*sum(v*r for v, r in zip(col, x))**2 for col, w in zip(cols, winv))
bb = sum(abs(sum(w*col[i]*col[j] for col, w in zip(cols, winv)))
         for i in range(10) for j in range(10))
assert xx == F(9932, 75) and bb == F(15776, 225) and xx*bb < 97**2
trial = F(sum(c*r for c, r in zip(coeff, x)), scale)
assert trial + 97*eps < -F(1, 20)
print('Trial at site 9856, error bound for each normal equation', trial, eps)
```

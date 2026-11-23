# Detecting the mixed-conductor descent with one packet

Use the Pareto weight $P(n)=1/[n(n+1)]$ for $n\ge1$, the residue $r_d(n)=n\bmod d$, the packet $J_q=\sum_{d\mid q}\mu(q/d)r_d$, and the scaled dilation $T_m f(n)=m f(\lfloor n/m\rfloor)$, with the packets anchored at zero. Let $a=\log 2$, $K_B=\mathrm{span}\{J_q:2\le q\le B,\ q\text{ has at least two distinct prime divisors}\}$, $M=\overline{\bigcup_B K_B}$, and $Q_B=I-P_{K_B}$. All projections use the Pareto inner product. The finite fit is $t_B=Q_BJ_2/a$ and its limit is $u=(I-P_M)J_2/a$.

## The energy in the ambient exact sequence

The centered connecting map sends $1$ to $[u-\mathbf1]\in\mathbf1^\perp/M$. Its representative $u-\mathbf1$ is orthogonal to $M$. Put $D_B=\|Q_B(J_2-a\mathbf1)\|^2$ and $F=a^2\|u-\mathbf1\|^2$. Orthogonality gives the exact equality
$$
D_B=F+a^2\|t_B-u\|^2.
$$
Because $t_B$ lies in a finite legal span and $u$ lies outside every such span, $D_B>F$ for every $B$. The fits converge to $u$, so $D_B\downarrow F$. For each $B$ and $c>0$, eventually $D_N-F<c(D_B-F)$. There are infinitely many $k$ with $D_{k+1}<D_k$. These statements and the finite-window bound in the next section are declared in `RH/MixedConductorStrictDescent.lean`.

With $g_k=(D_k-D_{k+1})/D_k$, the exact product is $D_N=D_0\prod_{k<N}(1-g_k)$. The project proves $0\le g_k<1$ and $F=0\iff\sum_k g_k=\infty$. When $F=0$ the ambient connecting map vanishes, $\mathbf1\in V$, and the established discrete Hilbert-space criterion yields RH. The strict decreases above also occur in the scalar example $D_k=1+2^{-k}$, where the product has positive limit. The unresolved estimate for this descent is divergence of the relative gains. For the classical discrete approximation criterion, see [Bagchi, Theorem 1](https://arxiv.org/abs/math/0607733).

## A fixed mixed packet detects every finite fit

Write $y=T_mJ_6$. The divisor formula gives
$$
T_mJ_q=\sum_{d\mid m,\ (q,m/d)=1}J_{qd}.
$$
For mixed $q$ every summand has mixed conductor at most $qm$. For $N=\max(B,6m)$, $y\in K_N$. Conductor six is mixed, so $\langle y,\mathbf1\rangle=0$. Nested orthogonal projections give
$$
D_B-D_N=\|(P_{K_N}-P_{K_B})J_2\|^2,\qquad
a^2|\langle t_B,y\rangle|^2\le (D_B-D_N)\,m\|J_6\|^2.
$$
Indeed $Q_B(J_2-a\mathbf1)=a(t_B-\mathbf1)$, and the component beyond $K_N$ pairs to zero with $y$. The norm identity $\|T_mJ_6\|^2=m\|J_6\|^2$ completes Cauchy–Schwarz. The Lean bound covers every mixed $q$.

**Period transform.** For a bounded $L$-periodic sequence $v$ on the nonnegative integers put
$$
F_v(x)=\frac{\sum_{r=0}^{L-1} v(r)x^r}{\sum_{r=0}^{L-1}x^r},
\qquad G_v(t)=F_v(e^{-t}),\qquad W(s)=\frac1{e^s+1}.
$$
For $L\mid m$, the period transform evaluates both pairings.
$$
A_m(v):=\langle v,T_mJ_2\rangle=\int_0^\infty G_v(s/m)W(s)\,ds,
\qquad \langle v,T_mJ_6\rangle=A_{3m}(v)-A_m(v).
$$
For the first identity insert $1/[n(n+1)]=\int_0^1 (1-x)x^{n-1}\,dx$. Only the blocks $n=jm+r$ with $j$ odd and $0\le r<m$ contribute. On each block $v(jm+r)=v(r)$ and $\sum_{r<m}v(r)x^r=F_v(x)(1-x^m)/(1-x)$. Summing $x^{jm}$ over odd $j\ge1$ leaves $m x^{m-1}F_v(x)/(1+x^m)$ in the integral. Substitute $x^m=e^{-s}$. All interchanges hold by absolute convergence since $v$ is bounded and $m$ is fixed. The second identity follows from $T_3J_2=J_2+J_6$ and $T_mT_3=T_{3m}$.

**First nonconstant term.** If $v$ is nonconstant, $G_v(t)=G_v(0)+b_rt^r+O_v(t^{r+1})$ with $b_r\ne0$ and $1\le r\le L-1$. Indeed the polynomial $\sum_{j<L}(v(j)-F_v(1))x^j$ is nonzero, vanishes at 1, and has degree at most $L-1$. Its order of vanishing is preserved by the denominator and by $x=e^{-t}$. Let $\mu_j=\int_0^\infty s^j W(s)\,ds$, which is finite and strictly positive. Boundedness of $G_v$ and its expansion at zero give $|G_v(t)-G_v(0)|\le C_v t^r$ for every $t\ge0$. Dominated convergence now gives
$$
\lim_{m\to\infty,\ L\mid m}m^r\langle v,T_mJ_6\rangle
=b_r(3^{-r}-1)\mu_r\ne0.
$$
Every $t_B$ has a period divisible by all the conductors used, vanishes at a positive multiple of this period, and has Pareto mean one. It is therefore nonconstant. Every sufficiently large multiple $m$ of its period gives a strict gain by conductor $\max(B,6m)$.

## A finite choice of the detecting dilation

Write the actual finite fit in the **raw** residue basis as $v=\sum_{d\in S}c_dr_d$ with distinct $d\ge2$. Coefficients in the project's normalized basis $r_d/d$ must be divided by $d$ here. For a period divisible by $d$, summing the finite geometric progression and differentiating gives
$$
G_{r_d}(t)=\frac1{e^t-1}-\frac d{e^{dt}-1}.
$$
The constant term is $(d-1)/2$. For $j\ge1$ the coefficient of $t^{2j-1}$ in $G_v$ is
$$
b_{2j-1}=-\frac{B_{2j}}{(2j)!}\sum_{d\in S}c_d(d^{2j}-1).
$$
If $v\ne0$, one of the first $|S|$ sums is nonzero. Subtract consecutive vanishing sums, starting with exponent zero. The resulting equations have coefficients $c_d(d^2-1)$ on the distinct Vandermonde nodes $d^2$, so invertibility forces every $c_d=0$. Thus the first $r$ is odd and $r\le 2|S|-1$. The nonzero finite moment for the actual fit is formalized in `fixedTwoTrial_exists_residue_moment`. The transform identity, its analytic estimates and the following explicit choice are proved here on paper. The Bernoulli generating function and the signs of its even coefficients are given in [DLMF §24.2(i)](https://dlmf.nist.gov/24.2#i).

Let $j$ be the first nonzero index, $r=2j-1$, and set
$$
C_v=\frac{|B_{2j+2}|}{(2j+2)!}\sum_{d\in S}|c_d|(1+d^{2j+2}).
$$
For all $t\ge0$,
$$
|G_v(t)-G_v(0)-b_rt^r|\le C_v t^{r+2}.
$$
To see the global bound, use $1/(e^t-1)=1/t-1/2+2t\sum_{n\ge1}(t^2+4\pi^2 n^2)^{-1}$. Finite geometric division in $t^2/(4\pi^2n^2)$ bounds the remainder of each summand by its next term in absolute value, also when the ratio exceeds one. The summed next coefficient is $|B_{2j+2}|/(2j+2)!$ by the expansion at zero. At $dt$ multiplication by $d$ supplies $d^{2j+2}$. Apply the triangle inequality to the residue sum. The partial fraction identity is [DLMF 4.36.3](https://dlmf.nist.gov/4.36.E3).

Integration at scales $1/m$ and $1/(3m)$ gives
$$
\left|m^r\langle v,T_mJ_6\rangle-b_r(3^{-r}-1)\mu_r\right|
\le \frac{C_v(1+3^{-(r+2)})\mu_{r+2}}{m^2}.
$$
In particular any positive multiple of the period with
$$
m^2>\frac{2C_v(1+3^{-(r+2)})\mu_{r+2}}{|b_r|(1-3^{-r})\mu_r}
$$
gives $|\langle v,T_mJ_6\rangle|>|b_r|(1-3^{-r})\mu_r/(2m^r)$. This supplies a finite choice of a successful mixed test from the coefficients of $v$. For one fixed fit, the squared correlation divided by $\|T_mJ_6\|^2$ has order $m^{-2r-1}$. Contributions from different test directions require their mutual Gram matrix before they can be added.

## The parity constant

For $v=J_2$ the period is two and $G_v(t)=1/(1+e^t)$. For every positive even $m$, $\langle J_2,T_mJ_6\rangle>0$. More precisely,
$$
0\le\frac{\pi^2}{72}-m\langle J_2,T_mJ_6\rangle
\le\frac{91\pi^4}{77760m^2}.
$$
In fact $G_v(t/3)-G_v(t)=(\tanh(t/2)-\tanh(t/6))/2$. The difference between $t/6$ and this expression equals $\tfrac12\int_{t/6}^{t/2}\tanh^2 z\,dz$ and lies between zero and $13t^3/648$, since $0\le\tanh z\le z$ for $z\ge0$. Integrate with $t=s/m$. The alternating exponential expansion gives $\mu_1=\pi^2/12$ and $\mu_3=7\pi^4/120$. Absolute summability after integration holds for both moments. Wolfram numerical integrations for $m=20,60,180$ give $0.1367943695222$, $0.1370461926222$, $0.1370743207830$, respectively, for the scaled correlation.

## The squared error of the entire conductor-six orbit

Let $O_6=\overline{\mathrm{span}}\{T_mJ_6:m\ge1\}$ and define a physical sequence $h$ by $h(0)=0$ and
$$
h(n)=\mathbf1_{\bigcup_{j\ge0}[3^j,2\cdot3^j)}(n)\quad(n\ge1).
$$
Thus $h(n)$ records whether the first base-three digit is 1. It satisfies $h=e_1+T_3h/3$, where $e_1$ is the indicator of site 1. Dilation preserves the Pareto mean, $\mathbb E_P[e_1]=1/2$, and $h^2=h$. Consequently $\mathbb E_P[h]=3/4$, and $w=h-(3/4)\mathbf1$ has squared norm $3/16$.

For every $f\in H$, $(T_3f)(1)=0$ and $\langle T_3f,T_3h\rangle=3\langle f,h\rangle$. Pairing the displayed decomposition of $h$ with $T_3f$ gives $\langle T_3f,w\rangle=\langle f,w\rangle$. Since $T_mJ_6=(T_3-I)T_mJ_2$, continuity gives $w\perp O_6$.

The sites 1, 3 and 5 alone contribute $1/2+1/12+1/30=37/60$ to $\langle J_2,h\rangle$. All remaining contributions are nonnegative. With $e=J_2-(\log2)\mathbf1$ and $\log2<347/500$ we obtain
$$
\langle e,w\rangle\ge\frac{37}{60}-\frac34\log2>\frac{577}{6000}.
$$
Thus for **every** $x\in O_6$, Cauchy–Schwarz gives
$$
\|e-x\|^2\ge\frac{|\langle e,w\rangle|^2}{3/16}
>\frac{49}{1000}.
$$
The rational trial below achieves $D_{120}<39/1000<49/1000$. In particular $O_6$ is a proper subspace of $M$. The ability of $T_mJ_6$ to detect each finite fit coexists with this positive distance from its own closed span. The same witness annihilates every mixed packet of conductor $3^a r$ with $a\ge1$, $r>1$ and $3\nmid r$. Indeed the divisor identity for the residues gives $J_{3^ar}=(T_3-I)T_{3^{a-1}}J_r$ by Möbius inversion. This larger family and all its dilations obey the same lower bound. In particular, permitting mixed conductors coprime to three at cutoff 120 lowers the optimal squared error by more than $1/100$ from the optimum using only mixed conductors divisible by three. The ternary witness, its exact norm, the pairing for all such conductors and the closed orbit bound are formalized in `RH/TernaryMixedOrbitObstruction.lean`.

Conductor ten supplies a specific missing vector. The identity $J_{10}=T_5J_2-J_2$ gives $J_{10}\le5$. At sites $1,3,4,5$, the indicator $h$ equals one and $J_{10}$ takes the values $-1,-1,0,4$. The contribution of those four sites to $\langle 5-J_{10},h\rangle$ is $227/60$. Positivity of the remaining contributions and $\mathbb E_P[J_{10}]=0$ give
$$
\langle J_{10},w\rangle=\langle J_{10},h\rangle\le 5(3/4)-227/60=-1/30.
$$
It follows directly that $J_{10}\notin O_6$ and $\mathrm{dist}(J_{10},O_6)^2\ge4/675$.

For a proof using one tested direction $y_k$ at each successive **full mixed** cutoff $B_k$, write $s_k=|\langle Q_{B_k}e,y_k\rangle|^2/(D_{B_k}\|y_k\|^2)$, with value zero at $y_k=0$. For $y_k\in K_{B_{k+1}}$ and $B_{k+1}\ge B_k$, Cauchy–Schwarz gives $s_k\le(D_{B_k}-D_{B_{k+1}})/D_{B_k}$. A divergent series of these tested fractions forces the boundary to vanish. Each $Q_{B_k}$ uses every mixed packet available through $B_k$. The proof in `boundary_eq_zero_of_block_correlation_shares` also covers variable mixed test directions.

## An exact upper bound for the window through conductor 120

The certificate below uses a fixed rational trial $v=J_2+\sum_{q\text{ mixed}}c_qJ_q$. The optimal projection property gives $D_{120}\le\|v-a\mathbf1\|^2=\mathbb E_P[v^2]-a^2$, because $\mathbb E_P[v]=a$. For $n\le4{,}000{,}000$, round each nonnegative weighted square **up** on the grid $10^{-14}\mathbb Z$. For the remaining sites bound $10^5v(n)$ between the sums of the individual period minima and maxima. The remaining Pareto mass is exactly $1/4{,}000{,}001$. Use the first six terms of the positive series for $2\operatorname{arctanh}(1/3)$ to bound $\log2$ from below. The calculation gives
$$
D_{120}\le
\frac{80554138549668225866802612362773}
     {2067314988181517838225000000000000}
<\frac{39}{1000}.
$$
The integer head sum is $51925842277348$ grid units and the bounds on $10^5v$ are $-2390923$ and $2530047$. The fraction is approximately $0.038965585317275$. The coefficients were selected by a floating-point Gram solve. The reported bound uses only the following independent, standalone integer and rational calculation. This numerical certificate runs in Python and is separate from the Lean checks.

```python
from array import array
from fractions import Fraction

# Coefficients of packets in 100000 v, with v = J_2 plus mixed packets.
coeff = {
    2:100000, 6:12400, 10:9277, 12:-2983, 14:8376, 15:-3531, 18:6392,
    20:-1129, 21:-2863, 22:5529, 24:-884, 26:4606, 28:-500, 30:3821,
    33:-2450, 34:4098, 35:-2078, 36:-1386, 38:4372, 39:-1464, 40:-717,
    42:2558, 44:68, 45:-10, 46:3693, 48:49, 50:2904, 51:-1560, 52:3,
    54:2182, 55:-1142, 56:55, 57:-938, 58:3254, 60:-913, 62:2015,
    63:-810, 65:-1163, 66:1429, 68:-420, 69:-1607, 70:1827, 72:-962,
    74:2465, 75:-1014, 76:-681, 77:-1197, 78:1524, 80:-1196, 82:1964,
    84:-1411, 85:-849, 86:2711, 87:-1278, 88:-366, 90:1156, 91:-1468,
    92:-363, 93:-1235, 94:2621, 95:-1005, 96:-680, 98:2047, 99:-989,
    100:-777, 102:932, 104:-691, 105:-756, 106:2286, 108:-1167,
    110:1082, 111:-645, 112:-621, 114:1479, 115:-990, 116:-783, 117:-379,
    118:2240, 119:-762, 120:-518,
}
scale = 100000
limit = 4000000
grid = 10**14
assert coeff[2] == scale and grid % scale**2 == 0

def divisors(q):
    return [d for d in range(1, q + 1) if q % d == 0]

mu = [0, 1]
for q in range(2, max(coeff) + 1):
    mu.append(-sum(mu[d] for d in divisors(q) if d < q))

residue_coeff = {}
lower = upper = 0
for q, a in coeff.items():
    ds = divisors(q)
    assert q == 2 or sum(len(divisors(d)) == 2 for d in ds) >= 2
    assert 2 <= q <= 120
    values = [a * sum(mu[q // d] * (r % d) for d in ds) for r in range(q)]
    lower += min(values)
    upper += max(values)
    for d in ds:
        if d >= 2:
            residue_coeff[d] = residue_coeff.get(d, 0) + a * mu[q // d]

# For r_d(n) = n mod d, its increment is 1 - d * [d divides n].
increments = array('q', [sum(residue_coeff.values())]) * (limit + 1)
for d, a in residue_coeff.items():
    for n in range(d, limit + 1, d):
        increments[n] -= d * a

units = value = 0
for n in range(1, limit + 1):
    value += increments[n]
    denominator = n * (n + 1)
    numerator = value**2 * (grid // scale**2)
    units += (numerator + denominator - 1) // denominator

log_lower = 2 * sum(Fraction(1, (2*j + 1) * 3**(2*j + 1)) for j in range(6))
tail = Fraction(max(-lower, upper)**2, scale**2 * (limit + 1))
bound = Fraction(units, grid) + tail - log_lower**2
assert 0 < bound < Fraction(39, 1000)
print(units, lower, upper, bound)
```

# Signed semiprime blocks and the residual energy

Let \(d=\mathbf 1-P_V\mathbf 1\) in the Pareto Hilbert space, and put \(E=\|d\|^2=\langle d,\mathbf 1\rangle\). Number primes from \(p_0=2\). All statements below concern this actual orthogonal residual. Write \(w_m=1/[m(m+1)]\) for \(m\ge1\), and let \(d_m\) denote its physical coordinates. In these coordinates the inner product is \(\sum_m w_m f_m g_m\). The established Báez-Duarte criterion in the repository gives \(\mathrm{RH}\iff E=0\).

## Two signs and a finite certificate

For \(q_j=p_jp_{j+1}\), let \(R(a)\) be the reciprocal residue pairing, \(s_j=R(q_j)-R(p_j)-R(p_{j+1})\), and \(S_{k,n}=\sum_{j<n}s_{k+j}\). Restoring the two singleton terms gives \(B_{k,n}=\sum_{j<n}R(q_{k+j})\). For every positive block length,

\[
\begin{aligned}
S_{k,n}\ge0 &\ \Longrightarrow\
 E\le \frac{4}{n^2}\sum_{j<n}\frac{2j+1}{p_{k+j}},\\
B_{k,n}\le0 &\ \Longrightarrow\
 E\le \frac{1}{n^2}\sum_{j<n}\frac{2j+1}{q_{k+j}} < \frac{37}{25n^2}.
\end{aligned}
\]

Both statements apply to a single observed sign. The second certificate is uniform in the starting prime. A short hand estimate gives the constant 2, and the exact finite certificate below improves it to 37/25. Its stronger rate belongs to the restored sum, whose individual terms have limit \(+E\). The original terms have limit \(-E\). The sign in the second test is consequently reversed. A finite upper bound on \(E\) restricts every zeta zero \(\rho\) to the right of the critical line by \((2\Re\rho-1)/|\rho|^2\le E\), using the repository's Mellin obstruction.

## The coordinate identity

Put \(A_a(m)=(m\bmod a)/m\) and \(h_a=1-A_a\). Then \(R(a)=\langle d,A_a\rangle\). For \(a,m\ge1\),

\[
 h_a(m)=\frac{a\lfloor m/a\rfloor}{m},\qquad
 \tfrac12\,\mathbf 1_{m\ge a}\le h_a(m)\le\mathbf 1_{m\ge a},
 \qquad \sum_{m\ge a}w_m=\frac1a.
\]

Indeed, if \(m\ge a\), then \(a\lfloor m/a\rfloor\le m<a(\lfloor m/a\rfloor+1)\le2a\lfloor m/a\rfloor\). Divisibility \(a\mid b\) gives \(h_b\le h_a\) because \(m\bmod a=(m\bmod b)\bmod a\). Define \(\Delta(a,b)=R(ab)-R(a)-R(b)\) and \(K_{a,b}=h_a+h_b-h_{ab}\). For arbitrary \(1\le a\le b\),

\[
\Delta(a,b)+E=\langle d,K_{a,b}\rangle,\qquad
h_a\le K_{a,b}\le\mathbf1_{m\ge a}+\mathbf1_{m\ge b}.
\]

The upper envelope squared has Pareto mean \(1/a+3/b\). Define \(\tau(t)^2=\sum_{m\ge t}w_m|d_m|^2\). Cauchy–Schwarz on this support gives
\[
 |\Delta(a,b)+E|\le\tau(a)\sqrt{1/a+3/b}.
\]
Here \(\tau(a)\le\sqrt E\) and \(\tau(a)\to0\). Completing the square in \(-E+\sqrt{E(1/a+3/b)}\) gives \(\Delta(a,b)\le(1/a+3/b)/4\). A nonnegative defect gives \(E\le1/a+3/b\), including equal or composite conductors.

## Ordinary blocks and Fekete’s infimum

For \(t_0\le\cdots\le t_{n-1}\) positive integers, expanding the square of the sum of tail indicators gives
\[
 \left\|\sum_{j<n}\mathbf1_{m\ge t_j}\right\|^2
 =\sum_{i,j<n}\frac1{\max(t_i,t_j)}
 =\sum_{j<n}\frac{2j+1}{t_j}.
\]
The coefficient \(2j+1\) counts ordered index pairs with larger index \(j\), including the diagonal. For \(D_{k,n}=\sum_{j<n}(2j+1)/p_{k+j}\), the carry bounds therefore yield
\[
 \tfrac14 D_{k,n}\le\left\|\sum_{j<n}K_{p_{k+j},p_{k+j+1}}\right\|^2\le4D_{k,n},
 \qquad |S_{k,n}+nE|\le2\tau(p_k)\sqrt{D_{k,n}}.
\]
Completing the square in \(-nE+2\sqrt{ED_{k,n}}\) also gives the unconditional positive-excursion bound \(S_{k,n}\le D_{k,n}/n\) for \(n>0\). If \(S_{k,n}\ge0\), division for \(E>0\) gives the first certificate. It also gives \(E\le4/p_k\), since the odd weights sum to \(n^2\). At fixed \(n\), \(S_{k,n}\to-nE\) as \(k\to\infty\). This yields \(U(n)=\sup_k S_{k,n}\ge-nE\), whether or not a starting position attains the supremum.

The prime number theorem gives \(D_{0,n}\sim2n/\log n\) by summing terms asymptotic to \(2/\log j\). Consequently favorable ordinary blocks imply \(E\le(8+o(1))/(n\log n)\) uniformly in their start. There is also a one-sided remainder for the infimum formula,
\[
 0\le U(n)+nE=o\big(\sqrt{n/\log n}\big).
\]
To see the little-oh, fix \(J\). In any block, the absolute contribution of its centered terms with indices below \(J\) is at most \(\sum_{i<J}|s_i+E|\). The remaining block, of length at most \(n\) and start at least \(J\), contributes at most \(2\tau(p_J)\sqrt{D_{0,n}}\). Divide by \(\sqrt{n/\log n}\), let \(n\to\infty\), and then let \(J\to\infty\). In particular \(\inf_{n\ge1}U(n)/n=-E\). If \(E>0\), the favorable pairs \((k,n)\), \(n\ge1\), form a finite set. Conversely under RH every such block vanishes. Thus an unbounded set of favorable starts alone, even at one fixed positive length, is already equivalent to RH.

## Restoring the singleton terms

For \(M_{k,n}=\sum_{j<n}(2j+1)/q_{k+j}\), move the finite absolute values inside the coordinate sums, then apply Cauchy–Schwarz:
\[
 \sum_{j<n}|E-R(q_{k+j})|
 \le \sum_{m\ge q_k} w_m |d_m|\sum_{j<n}\mathbf1_{m\ge q_{k+j}}
 \le \tau(q_k)\sqrt{M_{k,n}} .
\]
This controls absolute errors individually. Cancellation among neighboring pairs is unnecessary. Write \(C_0^2=\sum_{j\ge0}(2j+1)/q_j\). The first five terms have sum \(1/6+3/15+5/35+7/77+9/143<2/3\). For \(j\ge5\), Rosser's bound \(p_j>(j+1)\log(j+1)\) and monotonicity of the primes give
\[
 \sum_{j\ge5}\frac{2j+1}{q_j}
 \le 2\sum_{m\ge6}\frac1{m\log^2m}
 \le \frac2{6\log^2 6}+\frac2{\log 6}<\frac43.
\]
The integral comparison uses the decreasing positive majorant on \([6,\infty)\). The last inequality follows from \(\log6>7/4\). For example \(\log6=2\sum_{l\ge0}(5/7)^{2l+1}/(2l+1)\), and its first four terms already exceed \(7/4\). Hence \(C_0^2<2\). [Rosser, *The n-th Prime is Greater than n log n*, Proc. London Math. Soc. (1939)](https://doi.org/10.1112/plms/s2-45.1.21).

It follows that
\[
 \sum_{j\ge0}|E-R(p_jp_{j+1})|\le C_0\sqrt E,\qquad
 \sup_{k\ge0}|B_{k,n}/n-E|\le C_0\sqrt E/n \quad(n\ge1).
\]
For any fixed start the unnormalized difference \(B_{k,n}-nE\) itself converges to a finite real number by absolute convergence. When \(B_{k,n}\le0\), \(nE\le C_0\sqrt E\), proving the second certificate. The same finite bound also gives \(E\le1/q_k\) because \(M_{k,n}\le n^2/q_k\). If \(E>0\), **every** corrected block with \(n>C_0/\sqrt E\) is strictly positive. Under RH every corrected block is zero. Thus arbitrarily long nonpositive corrected blocks, allowing the start to vary, are equivalent to RH. The same equivalence holds at any one prescribed start.

## An exact rational bound for the uniform constant

The comparison above works after any prefix. Take \(N=2^{18}\) and round each of the first \(N-1\) summands upwards to a multiple of \(10^{-12}\). Sieve the integers through four million to obtain the required consecutive primes. The sum of the upper numerators is \(1\,318\,276\,203\,507\). Since
\(\log2=2\sum_{\ell\ge0}(1/3)^{2\ell+1}/(2\ell+1)>56/81>69/100\), we have \(L=18(69/100)<\log N\). The remaining indices \(j\ge N-1\) satisfy the same integral comparison with \(m=j+1\ge N\). Consequently

\[
 C_0^2 \le \frac{1\,318\,276\,203\,507}{10^{12}}
          + \frac{2}{NL^2}+\frac{2}{L}<\frac{37}{25}.
\]

The following Python reproduces the integer numerator and checks the final rational comparison. The sieve removes precisely the composite integers because every composite has a prime factor at most its square root.

```python
from fractions import Fraction
from math import isqrt

N, scale, bound = 2**18, 10**12, 4_000_000
sieve = bytearray([1]) * (bound + 1)
sieve[:2] = bytes(2)
for p in range(2, isqrt(bound) + 1):
    if sieve[p]:
        sieve[p*p::p] = bytes((bound - p*p) // p + 1)
primes = [p for p in range(bound + 1) if sieve[p]]
assert len(primes) >= N
upper = 0
for j in range(N - 1):
    q = primes[j] * primes[j + 1]
    upper += ((2*j + 1) * scale + q - 1) // q
assert upper == 1_318_276_203_507
L = 18 * Fraction(69, 100)
assert Fraction(upper, scale) + 2/(N*L**2) + 2/L < Fraction(37, 25)
```

## Powers and an exponentially small tail

For \(a\ge2\) the errors \(h_{a^j}-h_{a^{j+1}}\) are nonnegative coordinatewise. Their sum from \(j=k\) to infinity equals \(h_{a^k}\) pointwise because \(a^j\) eventually exceeds each fixed coordinate. Since \(R(a^{j+1})-R(a^j)=\langle d,h_{a^j}-h_{a^{j+1}}\rangle\), finite telescoping inside the positive majorant and Cauchy–Schwarz give
\[
 \sum_{j\ge k}|R(a^{j+1})-R(a^j)|
 \le \sum_{m\ge a^k}w_m|d_m|h_{a^k}(m)
 \le \tau(a^k)a^{-k/2}=o(a^{-k/2}).
\]
In fact \(|R(t)-E|\le\tau(t)/\sqrt t\) for every positive integer \(t\). For the specific doubling sign,
\[
 2R(a^k)\le R(a^{2k})\quad\Longrightarrow\quad E\le4/a^k.
\]
If \(E>0\), all doubling tests with \(a^k>4/E\) are strictly negative in the convention \(\Delta=R(a^{2k})-2R(a^k)\). Under RH they all vanish. The arguments control size and give consequences of an observed sign. Establishing a favorable sign at unbounded scale for the actual residual remains the RH-equivalent step.

The factor 4 in the power certificate can be sharpened. Put \(t=a^k\). A favorable doubling first gives \(E\le\|2h_t-h_{t^2}\|^2\). Since \(0\le h_{t^2}\le h_t\), one has \(0\le4\|h_t\|^2-\|2h_t-h_{t^2}\|^2\le4/t^2\). For every \(t\ge1\),
\[
 \|h_t\|^2\le\frac{2\zeta(2)-\zeta(3)}{3t}
           +\frac{2\zeta(3)-\zeta(4)}{t^2}.
\]
Indeed, on \(rt\le m<(r+1)t\) the contribution to \(\|h_t\|^2\) is \(t^2r^2\sum_m[m^3(m+1)]^{-1}\). Majorize the summand by \(m^{-4}\). For decreasing \(f(x)=x^{-4}\), its sum over the integers in \([l,u)\) is at most \(\int_l^u f(x)\,dx+f(l)-f(u)\). Sum this bound over \(r\ge1\) and telescope using \(\sum_{r\ge1}r^2(r^{-s}-(r+1)^{-s})=2\zeta(s-1)-\zeta(s)\) for \(s=3,4\). The leading constant in the squared carry norm is exact. Rescale \(m=tx\) on each compact interval, where the Riemann sums for \(t\|h_t\|^2\) converge to the integral of \(\lfloor x\rfloor^2/x^4\). The part with \(m\ge At\) has rescaled mass at most \(1/A\) for integer \(A\). This gives
\[
 \lim_{t\to\infty} t\|2h_t-h_{t^2}\|^2
 =4\int_1^\infty\frac{\lfloor x\rfloor^2}{x^4}\,dx
 =\frac43(2\zeta(2)-\zeta(3)).
\]
The integral is strictly less than 1 because \(\lfloor x\rfloor^2/x^4<x^{-2}\) almost everywhere on \([1,\infty)\). Thus the leading coefficient in this bound for a favorable doubling is strictly smaller than 4. Sharpness here concerns the carry norm. For the actual residual the tail factor \(\tau(t)\) gives a further saving.

## Formalization and sources

The companion [Lean module](RH/SemiprimeBlockRemainders.lean) proves finite norm and sign estimates, absolute summability at the prime products, the corrected-block RH equivalence, the uniform squared envelope
\[
\left(B_{k,n}/n-E\right)^2\le \frac{E C_0^2}{n^2},
\]
and the resulting obstruction: if \(d\ne0\), then all sufficiently long corrected blocks are strictly positive, uniformly in \(k\). It also proves bounded total variation on power towers. The [original Fekete module](RH/SemiprimeFekete.lean) supplies the identification with the density transform of the signed packet and the infimum theorem. The [Mellin obstruction](RH/ResidueDivisorZeroExclusion.lean) supplies the lower bound for each right zero. The explicit Rosser comparison and the tail-localized refinements above are written proofs.

[Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the Riemann hypothesis*](https://arxiv.org/abs/math/0202141) · [Axler, *New estimates for the nth prime number*](https://arxiv.org/abs/1706.03651)

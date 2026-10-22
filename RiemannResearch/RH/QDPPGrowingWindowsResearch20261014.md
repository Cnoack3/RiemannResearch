# Growing Q-divisor DPP windows and Poisson counts

Research continuation, 14 October 2026, based on the previously verified
`QDivisorDPPOverlap`, `QDivisorDPPArithmeticBounds`, and finite determinantal
counting modules. The global overlap identity is reused, not reproved.

## Verification status and scope

The eight source modules below contain 60 public theorem declarations, one
private helper theorem, and eight definitions. All eight saved source modules
compiled successfully in job `job_uzS396cvn-4Ce2Dchm3bbXZf888j2a6u`
(exit code 0, `verified: true`, 31.686 seconds). The six central declarations
audited there use only `propext`, `Classical.choice`, and `Quot.sound`.
These are ordinary foundations; the substantive assumptions of conditional
limits remain visible in their theorem types. Final publication uses the
server checkpoint, including its source audit and required project validation.
The earlier job `job_7-wzeKtEXXWu9KLLvlR8a30UE1t2DXk4` was interrupted when
its worker exited and is not used as verification evidence.

| Module | Public theorems | Mathematical scope |
|---|---:|---|
| `NumberTheory/GcdWindowMoments.lean` | 10 | Exact gcd grouping, consecutive-window moments for every real exponent greater than one, and reindexing |
| `RH/QDivisorDPPOverlapPower.lean` | 6 | Arbitrarily small real-power correction to the existing exact arithmetic overlap |
| `RH/QDivisorDPPGrowingWindows.lean` | 5 | Quantitative Hilbert–Schmidt bound, its limit consumer, and physical-window/matrix identities |
| `Probability/DeterminantalPoissonLimit.lean` | 11 | Exact spectral square identity, signed logarithmic remainder, PGF and vacancy limits, diagonal/off-diagonal decomposition |
| `Probability/ProbabilityGeneratingCoefficients.lean` | 10 | Coefficient convergence from normalized PGFs and the Poisson coefficients |
| `Probability/DeterminantalCountPoissonLimit.lean` | 4 | Actual finite and moving-window DPP count probabilities |
| `RH/QDivisorDPPPoisson.lean` | 4 | Actual Q-divisor-law count/vacancy consumers and explicit growing-window budgets |
| `Analysis/PeriodicWeightedMean.lean` | 10 | Exact Abel identity, weighted remainder, and nonnegative periodic discrepancy |

The arithmetic period-average formula, its specialization to the Q wavelets,
the explicit mean constructions, and the finite Fourier norm estimate in the
research analysis below remain **written proofs**, not Lean-verified providers.
The generic periodic and Abel module does not by itself discharge their
arithmetic hypotheses.

## Unconditional growing-window estimate

Use physical sites \(n=i+1\), and let \(W(x,h)=\{x+1,\ldots,x+h\}\).
The new statement `basisKernel_growing_window_hilbertSchmidt` is

\[
\forall\varepsilon\in(0,3/4),\quad \exists D_\varepsilon>0,\quad
\forall N,x\ge0,\ h\ge1,\qquad
\sum_{\substack{n,m\in W(x,h)\\n\ne m}}K_N(n,m)^2
\le D_\varepsilon\frac{h^{5-4\varepsilon}}{(x+1)^{4-4\varepsilon}}.
\]

The constant depends only on epsilon, uniformly in rank, location, and length.
There is no unproved number-theoretic hypothesis in this theorem's type.
The denominator \(x+1\) also handles \(x=0\) and gives the requested estimate
with denominator \(x\) whenever \(x\ge1\).

The proof preserves the established exact overlap identity

\[
\sum_r|\psi_r(n)\psi_r(m)|
=\frac{g^2}{nm}\prod_{p:\,v_p(n)\ne v_p(m)}2(1-p^{-2}),
\qquad g=\gcd(n,m).
\]

For each positive epsilon choose an integer \(B\) such that
\(p^\varepsilon\ge2\) for every integer \(p\ge B\). Bounding the finite
small-prime contribution gives

\[
|K_N(n,m)|\le C_\varepsilon
\left(\frac{g^2}{nm}\right)^{1-\varepsilon}.
\]

For distinct window points, \(1\le g\le h\). The exact gcd-fiber grouping is

\[
\sum_{n\ne m\in W}g^s
=\sum_{d=1}^h d^s\#\{(n,m)\in W^2:n\ne m,\ \gcd(n,m)=d\}.
\]

The number of window multiples of \(d\le h\) is at most \(2h/d\), so for
every real \(s>1\) the formalized moment bound is

\[
\sum_{n\ne m\in W}\gcd(n,m)^s
\le\left(4+\frac4{s-1}\right)h^{s+1}.
\]

For \(1<s\le2\), the proof uses the integral comparison for
\(\sum_{d=1}^h d^{s-2}\); for \(s\ge2\), a direct power bound suffices.
Substitute \(s=4-4\varepsilon>1\). One admissible constant is
\(D_\varepsilon=(4+4/(3-4\varepsilon))C_\varepsilon^2\).
This checks the full range \(0<\varepsilon<3/4\), rather than silently
assuming an integer exponent in the gcd moment.

## Conditional Poisson counts and vacancy

For finite restrictions of any real Hermitian positive-contraction DPP,
the exact identities used are

\[
\mathbb E[z^{C_N}]=\det(I+(z-1)K_{N,W})
=\prod_j(1+(z-1)\rho_{N,j}),
\]
\[
\sum_j\rho_{N,j}=\operatorname{tr}K_{N,W},\qquad
\sum_j\rho_{N,j}^2
=\sum_{n,m\in W}K_N(n,m)^2.
\]

The newly formalized consumer assumes the trace tends to a finite real
\(\lambda\) and the full square sum tends to zero. Nonnegativity of the
trace implies \(\lambda\ge0\). For \(0\le t\le1/2\), the signed remainder

\[
-2t^2\le\log(1-t)+t\le0
\]

controls the complete logarithmic product. Thus its PGF tends to
\(\exp(\lambda(z-1))\) for \(0\le z\le1\). A separate normalized-PGF
coefficient proof gives, for **every fixed integer** \(k\ge0\),

\[
\mathbb P(C_N=k)\longrightarrow e^{-\lambda}\frac{\lambda^k}{k!},
\qquad
\mathbb P(C_N=0)\longrightarrow e^{-\lambda}.
\]

The statements concern the actual spatial count law, not only an auxiliary
Bernoulli product. The existing determinantal/Bernoulli count identity supplies
that bridge. The coefficient result proves the normalized Poisson mass law;
there is no additional tightness hypothesis hidden in the theorem.

The exact square decomposition is retained:

\[
\sum_{n,m\in W}K_N(n,m)^2
=\sum_{n\in W}K_N(n,n)^2+
\sum_{n\ne m\in W}K_N(n,m)^2.
\]

If the nonnegative diagonals are bounded by \(b_N\to0\), then their square
sum is at most \(b_N\operatorname{tr}K_{N,W}\). This recovers the user's
maximum-occupation plus off-diagonal hypotheses. Alternatively, a vanishing
full square sum already implies vanishing maximum occupation, so a separate
maximum hypothesis is unnecessary in the most general consumer.

For the actual Q-divisor DPP, `basisLaw_growing_window_count_poisson_of_budgets`
retains exactly these domain-specific obligations:

1. The mean occupation converges to \(\lambda\).
2. \(N^3/(x+1)^2\to0\), a sufficient marginal bound from existing arithmetic lemmas.
3. \(h^{5-4\varepsilon}/(x+1)^{4-4\varepsilon}\to0\), for one fixed epsilon in \((0,3/4)\).

The positive-contraction assumptions are supplied by the existing projection
kernel API. They are not additional unproved Q-specific hypotheses. Vacancy
follows either from the general vacancy consumer or from the count theorem
at \(k=0\).

## Comparison of scales

If \(x\to\infty\) and \(h\le x^{4/5-\eta}\), with fixed
\(0<\eta<4/5\), choose

\[
0<\varepsilon<\min\left(\frac34,\frac{5\eta}{4/5+4\eta}\right).
\]

The exponent of \(x\) in the geometric budget is
\(-5\eta+(4/5+4\eta)\varepsilon<0\). Hence the off-diagonal mass vanishes
uniformly in the projection rank. The direct power-scale specialization is
written arithmetic; the Lean limit consumer takes the explicit vanishing
budget as its hypothesis. Positive-mean Poisson counts additionally require
control of the diagonal square sum.

| Regime | Conclusion | Remaining formal obligation |
|---|---|---|
| Fixed offsets at moving locations | Previously verified independent Bernoulli limits and unit-lattice sine obstruction | None newly claimed here |
| Growing \(h\le x^{4/5-\eta}\) | Vanishing off-diagonal mass; Poisson under mean and marginal conditions | Power-scale specialization and arithmetic providers |
| \(N=t^5,\ x=t^8,\ h=\lfloor\lambda Zx^2/S_N\rfloor\asymp t^6\) | Written proof of Poisson(\(\lambda\)) with all hypotheses discharged analytically | Q-wavelet period averages and concrete mean/rounding specialization |
| \(x,h\asymp N^2\) with the explicit choices below | Separate written Fourier proof of Poisson counts and vacancy | Finite Fourier norm estimate and arithmetic mean specialization |
| \(x/N^2\to\infty\), any window length | Written uniform mean bound forces vacancy probability to one | Arithmetic mean/tail provider |
| Other rescalings, unfoldings, or joint point-process limits | Not settled by these statements | Additional estimates and convergence theorems |

At \(h\asymp x\), the generic overlap estimate alone grows like \(x\)
and gives no decay. Its failure is not evidence for GUE: the independent
Fourier estimate below gives Poisson on explicit location-comparable windows.
On scales where a positive-mean Poisson count limit is proved, the count law
differs from a nontrivial sine-kernel DPP, whose count variance is
\(\operatorname{tr}K-\operatorname{tr}K^2<\operatorname{tr}K\).
Claims about kernel limits still require a specified convergence topology;
arbitrary continuum rescalings have not been excluded.

---

# Written arithmetic analysis: explicit windows

Written analytic proof, 14 October 2026. The arithmetic identities, concrete mean estimates, and Fourier bounds in this part have not been formalized in Lean. Their generic Hilbert–Schmidt and Poisson consumers are described separately above.

## 1. Definitions

Write Z = zeta(2), and for positive integers r,n define

\[
A_r(n)=\sum_{d\mid r}\mu(r/d)d^2\mathbf1_{d\mid n},\qquad
J_2(r)=r^2\prod_{p\mid r}(1-p^{-2}),\qquad
b_r(n)=\frac{A_r(n)}{\sqrt{J_2(r)}}.
\]

The counting-coordinate wavelet and finite projection kernel are

\[
\psi_r(n)=\frac{b_r(n)}{\sqrt Z\,n},\qquad
K_N(n,m)=\frac1{Znm}\sum_{r=1}^{N}b_r(n)b_r(m).
\]

Use the consecutive window W(x,h)={x+1,...,x+h}, with integers x>=1 and h>=0. Its expected DPP count is

\[
M_N(x,h)=\operatorname{tr}K_{N,W}
=\frac1Z\sum_{r=1}^{N}\sum_{n=x+1}^{x+h}\frac{b_r(n)^2}{n^2}.
\]

The implementation uses conductor r at basis index r-1, so rank N contains conductors 1 through N.

## 2. Exact period averages

The nonnegative function B_r(n)=b_r(n)^2 has period r. Define

\[
a_r=\frac1r\sum_{n=1}^{r}B_r(n).
\]

CRT factorization and the prime-power formula give the exact identity

\[
\boxed{a_r=r\prod_{p\mid r}\left(1-\frac1{p(p+1)}\right).}
\]

Indeed, for a>=1,

\[
A_{p^a}(n)=p^{2a}\mathbf1_{p^a\mid n}
             -p^{2a-2}\mathbf1_{p^{a-1}\mid n},
\]

and therefore the uniform average over a complete period is

\[
\frac{\mathbb E_{\mathrm{unif}\bmod p^a}A_{p^a}^2}{J_2(p^a)}
=p^a\frac{1-2p^{-2}+p^{-3}}{1-p^{-2}}
=p^a\left(1-\frac1{p(p+1)}\right).
\]

Multiplicativity follows by applying CRT to the distinct prime-power periods. The r=1 formula gives a_1=1.

Set

\[
S_N=\sum_{r=1}^{N}a_r,\qquad D_N=\sum_{r=1}^{N}r a_r.
\]

For a finite set of primes, the elementary product inequality

\[
\prod_p(1-u_p)\ge1-\sum_pu_p,
\quad u_p=\frac1{p(p+1)},
\quad\sum_{p\mid r}u_p\le\sum_{k=2}^{\infty}\frac1{k(k+1)}=\frac12
\]

gives

\[
\frac r2\le a_r\le r,
\quad
\boxed{\frac{N(N+1)}4\le S_N\le\frac{N(N+1)}2\le N^2,}
\quad
\boxed{D_N\le\sum_{r=1}^{N}r^2\le N^3.}
\]

The final inequalities assume N>=1.

For a shorter first formalization, the exact CRT formula can be postponed. The weaker estimates r/2<=a_r<=Zr suffice. The lower bound follows from the single period point n=r, where B_r(r)=J_2(r), together with J_2(r)>=r^2/2. The latter follows by comparing the product over primes dividing r with the telescoping product over all integers 2,...,r:

\[
\prod_{p\mid r}(1-p^{-2})\ge\prod_{k=2}^{r}(1-k^{-2})
=\frac{r+1}{2r}\ge\frac12.
\]

For the upper bound, existing Q-orthonormality gives sum_{n>=1} B_r(n)/n^2=Z. Hence

\[
ra_r=\sum_{n=1}^{r}B_r(n)
\le r^2\sum_{n=1}^{r}\frac{B_r(n)}{n^2}\le Zr^2.
\]

These weaker bounds imply N^2/4<=S_N<=ZN^2 and D_N<=ZN^3. The t-power construction below remains valid, with its explicit mean error replaced by t^(-1)+8lambda^2 Z t^(-2)+t^(-6). Thus one can formalize the nondegenerate windows before formalizing multiplicativity of the period averages.

## 3. Periodic discrepancy and exact weighted mean formula

For k>=0 let

\[
E_r(x,k)=\sum_{j=1}^{k}(B_r(x+j)-a_r).
\]

Write k=qr+s, 0<=s<r. All q complete periods cancel exactly, leaving

\[
E_r(x,k)=\sum_{j=1}^{s}B_r(x+j)-s a_r.
\]

Nonnegativity and the complete-period sum r a_r imply

\[
\boxed{|E_r(x,k)|\le r a_r.}
\]

For w_j=(x+j)^(-2), Abel summation gives the exact identity (for h>=1)

\[
\sum_{j=1}^{h}(B_r(x+j)-a_r)w_j
=E_r(x,h)w_h+
\sum_{j=1}^{h-1}E_r(x,j)(w_j-w_{j+1}).
\]

The weights decrease, so the absolute value is at most

\[
r a_r\left(w_h+\sum_{j=1}^{h-1}(w_j-w_{j+1})\right)
=\frac{r a_r}{(x+1)^2}.
\]

Thus, including h=0 by the empty-sum convention,

\[
\boxed{
M_N(x,h)=\frac{S_N}{Z}\sum_{n=x+1}^{x+h}\frac1{n^2}
                 +R_N(x,h),\qquad
|R_N(x,h)|\le\frac{D_N}{Z(x+1)^2}\le\frac{N^3}{Z(x+1)^2}.
}
\]

This bound is uniform in h and x. It does not require h to be a multiple of any period, and it does not require independence of residues under Q.

## 4. Explicit positive-mean short windows

Fix lambda>0, and for integer t>=1 define

\[
N_t=t^5,\qquad x_t=t^8,\qquad
h_t=\left\lfloor\frac{\lambda Z x_t^2}{S_{N_t}}\right\rfloor.
\]

These are explicit arithmetic sequences: S_N is a finite sum of explicit rational products, and Z is the fixed normalization constant.

The bounds on S_N imply

\[
\lambda Zt^6-1\le h_t\le4\lambda Zt^6,
\qquad h_t\longrightarrow\infty,
\qquad h_t/x_t\longrightarrow0.
\]

The floor error satisfies

\[
0\le\lambda-\frac{h_tS_{N_t}}{Zx_t^2}
<\frac{S_{N_t}}{Zx_t^2}\le\frac1{Zt^6}.
\]

For x>=1,h>=0,

\[
0\le\frac h{x^2}-\sum_{n=x+1}^{x+h}\frac1{n^2}
\le\frac{2h^2}{x^3}.
\]

For example, bound the sum below by h/(x+h)^2 and use
1-(1+y)^(-2)<=2y for y>=0. Hence

\[
0\le\frac{h_tS_{N_t}}{Zx_t^2}
-\frac{S_{N_t}}Z\sum_{n=x_t+1}^{x_t+h_t}\frac1{n^2}
\le2\lambda\frac{h_t}{x_t}
\le\frac{8\lambda^2 Z}{t^2}.
\]

Combining the exact mean identity, Abel discrepancy, floor error and weight variation yields the fully explicit estimate

\[
\boxed{
|M_{N_t}(x_t,h_t)-\lambda|
\le\frac1{Zt}+\frac{8\lambda^2Z}{t^2}+\frac1{Zt^6}.
}
\]

In particular the arithmetic mean really converges to the prescribed positive constant. This is not an unproved mean hypothesis.

The existing pointwise bound |A_r(n)|<=J_2(r)<=r^2 gives

\[
\boxed{
\max_{n\in W(x_t,h_t)}K_{N_t}(n,n)
\le\frac{\sum_{r\le N_t}J_2(r)}{Z(x_t+1)^2}
\le\frac1{Zt}.
}
\]

No new divisor estimate is needed here; the existing `basisKernel_diagonal_le` and `conductor_square_budget_le_cube` are sufficient.

The growing-window theorem formalized and source-verified above implies the form

\[
\sum_{\substack{n,m\in W(x,h)\\n\ne m}}K_N(n,m)^2
\le C_\varepsilon\frac{h^{5-4\varepsilon}}{x^{4-4\varepsilon}}.
\]

Take epsilon=1/8. With H=4 lambda Z, the preceding bound h_t<=Ht^6 gives

\[
\boxed{
\sum_{n\ne m\in W(x_t,h_t)}K_{N_t}(n,m)^2
\le\frac{C_{1/8}H^{9/2}}{t}.
}
\]

The diagonal square sum is at most (max diagonal) times the trace. Therefore

\[
\boxed{
\operatorname{tr}(K_{N_t,W_t}^2)
\le\frac{M_{N_t}(W_t)}{Zt}
     +\frac{C_{1/8}(4\lambda Z)^{9/2}}{t}
\longrightarrow0.
}
\]

The conditional Poisson theorem now applies to this concrete arithmetic sequence. Its assumptions have all been discharged by the written estimates, giving the following analytic conclusion (the concrete arithmetic specialization is not a Lean theorem):

\[
\#(\mathcal X_{N_t}\cap W_t)\Rightarrow\operatorname{Poisson}(\lambda),
\qquad
\mathbb P(\mathcal X_{N_t}\cap W_t=\varnothing)\longrightarrow e^{-\lambda}.
\]

General powers x=N^a with 3/2<a<5/3 work as well, choosing h=floor(lambda Z x^2/S_N), with epsilon positive and small enough that 6a-10+(8-4a)epsilon<0. Integer t-powers avoid all fractional-power rounding issues in a first formalization.

## 5. Exact asymptotic for the period-average mass

Define a multiplicative sequence c_d by

\[
c_d=\begin{cases}
\mu(d)\prod_{p\mid d}\dfrac1{p(p+1)},&d\text{ squarefree},\\
0,&\text{otherwise}.
\end{cases}
\]

Then |c_d|<=d^(-2), and the exact divisor expansion is

\[
a_r=r\sum_{d\mid r}c_d,
\quad
S_N=\sum_{d\le N}c_d d\frac{\lfloor N/d\rfloor(\lfloor N/d\rfloor+1)}2.
\]

Since |floor(y)(floor(y)+1)/2-y^2/2|<=y/2 for y>=0,

\[
S_N=\kappa N^2+O(N),\qquad
\boxed{\kappa=\frac12\sum_{d\ge1}\frac{c_d}{d}
=\frac12\prod_p\left(1-\frac1{p^2(p+1)}\right)>0.}
\]

An explicit remainder is

\[
|S_N-\kappa N^2|\le\frac{ZN}{2}+\frac14.
\]

The first error is bounded by (N/2)sum|c_d|<=ZN/2. The omitted main-term tail is at most (N^2/2)sum_{d>N}d^(-3)<=1/4. In particular 1/4<=kappa<=1/2 follows also from the earlier elementary bounds.

## 6. Location-scale windows: an independent analytic route

This section goes beyond the requested short-window estimate. It is a written analytic argument unless separately formalized.

For fixed c,d>0, take

\[
x_N=\lfloor cN^2\rfloor,\qquad h_N=\lfloor dN^2\rfloor.
\]

Here h_N/x_N tends to d/c>0. The preceding periodic discrepancy is O(1/N), and a decreasing-sum integral comparison gives

\[
\boxed{M_N(x_N,h_N)\longrightarrow
\lambda(c,d)=\frac\kappa Z\frac d{c(c+d)}>0.}
\]

The earlier generic overlap estimate does not prove Poisson on this scale: with h comparable to x, its upper bound grows like x. The following finite Fourier argument does.

### 6.1 Natural-density covariance

Let

\[
B_{r,s}=\operatorname{mean}_{n\bmod\operatorname{lcm}(r,s)}b_r(n)b_s(n).
\]

CRT makes B_{r,s} a product of local factors. At a prime p, with exponents a=v_p(r), b=v_p(s), the local factor is exactly

\[
\begin{cases}
1,&a=b=0,\\
\sqrt{(p-1)/(p+1)},&\min(a,b)=0<\max(a,b),\\
p^a(1-1/[p(p+1)]),&a=b\ge1,\\
\varphi(p^{\min(a,b)}),&a,b\ge1,\ a\ne b.
\end{cases}
\]

Consequently

\[
\boxed{0\le B_{r,s}\le\gcd(r,s).}
\]

For example, if 1<=a<b, expanding the two prime-power formulas gives the unnormalized average

\[
p^{2a+b}(1-p^{-1})(1-p^{-2}),
\]

and division by sqrt(J_2(p^a)J_2(p^b)) gives phi(p^a).

The row sums satisfy

\[
\sum_{s\le N}B_{r,s}
\le\sum_{s\le N}\sum_{q\mid(r,s)}q
=\sum_{q\mid r}q\lfloor N/q\rfloor
\le N\tau(r)\le2N^{3/2}.
\]

Here tau(r)<=2sqrt(r) is the elementary divisor-pairing bound. Since B is real symmetric and nonnegative entrywise,

\[
\boxed{\|B\|_{\mathrm{op}}\le2N^{3/2}.}
\]

### 6.2 Elementary rational-frequency bound

Expand the divisibility indicators by finite Fourier inversion:

\[
b_r(n)=\frac1{\sqrt{J_2(r)}}
\sum_{q\mid r}\mu(r/q)q\sum_{a=0}^{q-1}e^{2\pi i an/q}.
\]

Thus every b_r with r<=N is a linear combination of rational frequencies whose reduced denominators are at most N. Let F_N be the set of these frequencies modulo one. It has at most N^2 elements, and distinct elements have circular separation at least N^(-2).

For z=(z_1,...,z_N), write the exact expansion

\[
\sum_{r\le N}z_rb_r(n)=\sum_{\alpha\in F_N}v_\alpha e^{2\pi i\alpha n}.
\]

Finite Fourier orthogonality over a common complete period gives

\[
\sum_{\alpha\in F_N}|v_\alpha|^2=z^*Bz.
\]

On any consecutive window of length h, the frequency Gram matrix has diagonal h and off-diagonal entries bounded by

\[
\left|\sum_{n=x+1}^{x+h}e^{2\pi i(\alpha-\beta)n}\right|
\le\frac1{2\|\alpha-\beta\|_{\mathbb R/\mathbb Z}}.
\]

Ordering frequencies clockwise and counterclockwise from a fixed alpha, the j-th distance in either half-circle is at least j/N^2. The absolute row sum is therefore at most

\[
L_N(h)=h+N^2H_{|F_N|}\le h+N^2(1+2\log N).
\]

The row-sum bound, followed by the preceding exact Parseval identity, proves

\[
\sum_{n\in W}\left|\sum_{r\le N}z_rb_r(n)\right|^2
\le L_N(h)z^*Bz
\le2N^{3/2}L_N(h)\|z\|_2^2.
\]

This is an elementary finite proof; no external large-sieve result is being assumed.

### 6.3 Restricted-kernel norm and Poisson conclusion

Because n>=x+1 on W,

\[
\sum_{n\in W}\left|\sum_{r\le N}z_r\psi_r(n)\right|^2
\le\frac{2N^{3/2}L_N(h)}{Z(x+1)^2}\|z\|_2^2.
\]

The nonzero spectra of the two finite Gram matrices agree. Hence

\[
\boxed{\|K_{N,W}\|_{\mathrm{op}}
\le\frac{2N^{3/2}[h+N^2(1+2\log N)]}{Z(x+1)^2}.}
\]

For x_N=floor(cN^2), h_N=floor(dN^2), the right-hand side is O_{c,d}(N^(-1/2)log N), and tends to zero. Since K is positive semidefinite,

\[
\operatorname{tr}K_{N,W}^2
\le\|K_{N,W}\|_{\mathrm{op}}\operatorname{tr}K_{N,W}\longrightarrow0.
\]

Therefore these explicit location-scale windows also satisfy

\[
\#(\mathcal X_N\cap W_N)\Rightarrow
\operatorname{Poisson}\left(\frac\kappa Z\frac d{c(c+d)}\right),
\quad
\mathbb P(\mathcal X_N\cap W_N=\varnothing)
\longrightarrow\exp\left(-\frac\kappa Z\frac d{c(c+d)}\right).
\]

The natural prospective continuum intensity under n/N^2 is

\[
\frac\kappa{Zu^2}\,du\quad(u>0).
\]

Counts on each compact interval bounded away from zero have the displayed Poisson limits. A full point-process convergence statement would require writing the joint/Laplace-functional argument; it is not needed for the count and vacancy conclusions here.

### 6.4 Superquadratic locations force empty windows

The exact mean formula gives, uniformly over every finite h,

\[
M_N(x,h)\le\frac{S_N}Z\sum_{n>x}\frac1{n^2}
                  +\frac{D_N}{Z(x+1)^2}
\le\frac{N^2}{Zx}+\frac{N^3}{Z(x+1)^2}.
\]

The same bound holds for the entire infinite tail by monotone convergence. Consequently x_N/N^2->infinity implies M_N(x_N,h_N)->0 for every choice of h_N, even unbounded or infinite lengths. Markov's inequality then gives vacancy probability tending to one. Thus no finite positive limiting mean is possible at superquadratic locations. The quadratic location scale is the terminal scale for nondegenerate tails, and the preceding location-scale construction attains it.

### 6.5 Prescribing the mean without an infinite-product asymptotic

For a prescribed lambda>0 there is a finite-sum alternative to fixed c,d:

\[
x_N=\left\lfloor\frac{S_N}{2Z\lambda}\right\rfloor,
\qquad h_N=x_N.
\]

The elementary bounds on S_N show x_N is bounded above and below by positive lambda-dependent multiples of N^2 for all sufficiently large N. Put T_N=S_N/(2Zlambda), so x_N<=T_N<x_N+1. Integral comparison gives

\[
\left|\sum_{n=x_N+1}^{2x_N}\frac1{n^2}-\frac1{2x_N}\right|
\le\frac1{x_N^2}.
\]

Since S_N/(2Zx_N)=lambda T_N/x_N, the exact mean formula yields

\[
|M_N(x_N,x_N)-\lambda|
\le\frac{D_N}{Z(x_N+1)^2}
   +\frac{S_N}{Zx_N^2}+\frac\lambda{x_N}
=O_\lambda(N^{-1}).
\]

For example, once T_N>=2, one has x_N>=N^2/(16Zlambda), while S_N/(Zx_N)<=4lambda. The finite Fourier norm bound again tends to zero. Thus these explicit windows, with length exactly equal to location, converge to Poisson(lambda) and have vacancy limit exp(-lambda), without using the asymptotic for S_N or the Euler product for kappa.

## 7. Scope and limitations

1. The explicit t-power construction resolves the previously missing nondegenerate-mean example. Its arithmetic mean and diagonal estimates are unconditional; the final convergence uses the separately proved growing-window bound and the conditional DPP counting theorem.
2. The finite Fourier argument supplies an additional written proof for windows comparable to their location. It shows why the failure of the generic overlap bound at that scale is not itself evidence of GUE statistics.
3. We have not proved that every sequence with h/x->0 and bounded mean must be Poisson. The t-power example suffices to answer existence, and the location-scale example treats a different explicit regime.
4. These results concern the complete Q-divisor-wavelet projection DPP. They do not establish a zeta determinant identity, spectral realization of zeta zeros, RH, or a statement about legal residue-span projection DPPs without an additional connection theorem.

## 8. Remaining formalization targets

The source development already includes generic nonnegative-periodic discrepancy and exact finite Abel identities. To obtain a checked concrete arithmetic Poisson example, the remaining steps are:

- The exact prime-power period average for A_(p^a)^2/J_2(p^a), then CRT multiplicativity of a_r.
- A mean wrapper with the explicit assumed finite quantities S,D and the bound |M-(S/Z)sum n^(-2)|<=D/[Z(x+1)^2].
- A t-power specialization: with S between N(N+1)/4 and N^2, N=t^5, x=t^8 and h=floor(lambda Z x^2/S), obtain the three displayed error terms. This algebra can be proved independently of all prime arithmetic.
- Apply the existing verified diagonal-cube bound and the new growing-window statement at epsilon=1/8.

The Fourier location-scale analysis is naturally a subsequent module; do not silently mark it Lean verified just because the generic conditional Poisson consumer has passed verification.

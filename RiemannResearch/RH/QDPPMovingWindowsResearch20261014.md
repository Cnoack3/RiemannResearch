# Q divisor DPP: finite rank, moving windows, and arithmetic obstructions

Research date: 13 October 2026 in America/New_York / 14 October UTC.

## Status and scope

This record separates existing verified providers, new Lean developments, and
written analytic results. The verification ledger records targeted checks; final checkpoint job and
commit identifiers are reported with task completion. A finite-feature DPP is not, by construction alone, GUE,
a sine process, a model of zeta ordinates, or a Hilbert–Pólya realization.

Existing source: `RH/QDivisorDPP.lean`, initially published at
`42803d2da7feb86323bc28116954271f87abd831`. The inspected workspace base is
`fac0365a41f20840ad215f1621a9c182b862372f`. The existing modules
`Probability/DeterminantalMoments.lean`, `DeterminantalEntry.lean`, and
`DeterminantalWindow.lean` provide the generic count, pair, and gap identities.
The new finite-rank argument is user-provided; the arithmetic deductions below
are direct calculations from the existing wavelet definitions and factorization.

Use physical integers n >= 1 in this record. The Lean counting coordinate is
i = n-1. Put Z = zeta(2), q(n) = 1/(Z n^2),

\[
A_r(n)=\sum_{d\mid r}\mu(r/d)d^2\mathbf1_{d\mid n},\qquad
J_2(r)=r^2\prod_{p\mid r}(1-p^{-2}),\qquad
\psi_r(n)=\sqrt{q(n)}\frac{A_r(n)}{\sqrt{J_2(r)}}.
\]

Here r=1,...,N are the first N basis vectors; this is the complete divisor
basis, not the legal residue dictionary of the RH approximation criterion.

## 1. Exact finite-rank occupation obstruction

For distinct sites e(1),...,e(m), let B_{i,r}=psi_r(e(i)). Then

\[
K_{N,W}=BB^{\mathsf T},\qquad
\operatorname{rank}K_{N,W}\le N,\qquad
\mathbb P(W\subset X_N)=\det K_{N,W}.
\]

If m>N, its determinant is zero. Thus every N+1-site window has exactly
zero full-occupation probability at stage N, regardless of its location.
No limiting argument and no arithmetic or RH hypothesis is used.

For completeness, countably many zero-probability N+1-site inclusion events
show |X_N|<=N almost surely. Orthonormality gives the exact trace identity

\[
\sum_{n\ge1}K_N(n,n)
=\sum_{r=1}^N\sum_{n\ge1}|\psi_r(n)|^2=N.
\]

Tonelli therefore gives E|X_N|=N; combined with the almost-sure upper bound,
this proves |X_N|=N almost surely. This last global-cardinality proof is written
here and is not asserted as a new Lean declaration in the present module.

## 2. Exact identities for arbitrary moving windows

Let W_N be any finite set of distinct sites, m_N=|W_N|, and C_N=|X_N intersect
W_N|. No assumption that the window is fixed is needed for these identities:

\[
\begin{aligned}
\mathbb E C_N&=\sum_{n\in W_N}K_N(n,n)=\operatorname{tr}K_{N,W_N},\\
\mathbb E(m_N-C_N)&=\sum_{n\in W_N}(1-K_N(n,n)),\\
\mathbb P(C_N=m_N)&=\det K_{N,W_N},\\
\mathbb P(C_N=0)&=\det(I-K_{N,W_N}),\\
\mathbb P(C_N<m_N)&=1-\det K_{N,W_N},\\
\operatorname{Var} C_N&=\operatorname{tr}K_{N,W_N}
  -\sum_{n,m\in W_N}K_N(n,m)^2.
\end{aligned}
\]

At distinct sites n,m, with I_n their occupation indicators,

\[
\begin{aligned}
\mathbb P(I_n=1)&=K_N(n,n),\\
\mathbb P(I_n=0)&=1-K_N(n,n),\\
\mathbb P(I_n=I_m=1)&=K_N(n,n)K_N(m,m)-K_N(n,m)^2,\\
\operatorname{Cov}(I_n,I_m)&=-K_N(n,m)^2,\\
\mathbb P(I_n=I_m=0)&=(1-K_N(n,n))(1-K_N(m,m))-K_N(n,m)^2.
\end{aligned}
\]

In particular hole indicators have the same off-diagonal covariance as
occupation indicators. For possibly overlapping finite windows U,V,

\[
\operatorname{Cov}(C_U,C_V)
=\sum_{n\in U\cap V}K_N(n,n)-\sum_{n\in U,m\in V}K_N(n,m)^2.
\]

The exact vacancy energy and complementary kernel are

\[
1-K_N(n,n)=\|(I-P_N)e_n\|^2
 =\sum_{r>N}|\psi_r(n)|^2,
\qquad
\delta_{nm}-K_N(n,m)=\sum_{r>N}\psi_r(n)\psi_r(m).
\]

The infinite sums are actual Parseval tails; no signed term is omitted.
The existing window generating theorem also yields
E[z^{C_N}]=det(I+(z-1)K_{N,W_N}). The new Lean consumer assembles count,
vacancy-count, gap, variance, covariance, and finite-rank identities; the other
displayed consequences are written deductions unless separately listed below.

## 3. Exact arithmetic kernel and signatures

The physical kernel is

\[
K_N(n,m)=\frac1{Znm}\sum_{r\le N}\frac{A_r(n)A_r(m)}{J_2(r)}.
\]

For a prime p and a>=1,

\[
A_{p^a}(n)=p^{2a}\mathbf1_{p^a\mid n}
 -p^{2a-2}\mathbf1_{p^{a-1}\mid n},\qquad
A_r(n)=\prod_{p^a\parallel r}A_{p^a}(n).
\]

The existing factorization module verifies this finite product formula.
Define D_N(n)={d:1<=d<=N, d divides n}. If D_N(n)=D_N(m), then A_r(n)=A_r(m)
for every r<=N. Therefore psi_r(n)=(m/n)psi_r(m), and the corresponding
kernel block has rank at most one. For distinct n,m in the same signature class,

\[
\boxed{\mathbb P(n,m\in X_N)=0.}
\]

Each signature class contains at most one occupied site almost surely.
This is a stronger obstruction than the rank-N bound on those selected sites.
Signatures are periodic modulo lcm(1,...,N); equality of signatures does not
require nearby sites or imply stationarity of the kernel.

If n has no prime factor <=N (including n=1), then every common divisor of
n and r<=N is 1, so A_r(n)=mu(r). Write

\[
H_N=\sum_{r\le N}\frac{\mu(r)^2}{J_2(r)}.
\]

For two such sites,

\[
K_N(n,m)=\frac{H_N}{Znm},\qquad
H_N\uparrow\prod_p\left(1+\frac1{p^2-1}\right)=Z.
\]

Thus occupation probabilities are at most 1/n^2. All such sites other than 1
lie above N, giving

\[
\mathbb E|X_N\cap\{n>1:D_N(n)=\{1\}\}|
=\frac{H_N}{Z}\sum_{\substack{n>1\\D_N(n)=\{1\}}}\frac1{n^2}
\le\sum_{n>N}\frac1{n^2}\le\frac1N\quad(N\ge1).
\]

Consequently this entire rough sector is empty with probability tending to one.
Spatial rescaling alone cannot give that restricted process a positive-density
sine limit; conditioning or changing the law would be a different question.

## 4. An exact reverse prime-product occupation law

The nonnegative weights w_n(r)=q(n) A_r(n)^2/J_2(r) sum to 1 by completeness.
They therefore define an auxiliary random positive integer R_n, with

\[
\boxed{K_N(n,n)=\mathbb P(R_n\le N),\quad
1-K_N(n,n)=\mathbb P(R_n>N).}
\]

This is an auxiliary arithmetic law, not a coupling of different DPP stages.
Its prime exponents E_p are independent. For v=v_p(n), their exact laws are

\[
\begin{array}{c|c}
a&\mathbb P(E_p=a)\\\hline
0&(1-p^{-2})p^{-2v}\\
1\le a\le v&(1-p^{-2})p^{-2v}J_2(p^a)\\
v+1&p^{-2}\\
a>v+1&0
\end{array}
\]

To verify normalization, sum J_2(p^a), including J_2(1)=1, from a=0 to v;
the sum is p^{2v}. The first v+1 entries therefore sum to 1-p^{-2}.
For all primes not dividing n, E_p is Bernoulli with success probability p^{-2}.
Since sum_p p^{-2}<infinity, only finitely many such exponents are nonzero
almost surely. Multiplying local probabilities gives exactly w_n(r), including
the factor product_p(1-p^{-2})=1/Z. This proves the claimed law, not only
matching one-prime marginals.

Let S=product of primes for which E_p=v_p(n)+1. These events are independent
with probabilities p^{-2}, independent of the value of n in their marginal
law. Thus

\[
\mathbb P(S=s)=\frac{\mu(s)^2}{ZJ_2(s)},\qquad R_n\mid nS.
\]

The divisibility statement holds prime by prime, including primes not dividing
n. It supplies the following uniform moving-site estimate. First retain the
exact tail identity above; then, for 1<=n<=N,

\[
\begin{aligned}
1-K_N(n,n)&\le\mathbb P(S>N/n)\\
&=\frac1Z\sum_{s>N/n}\frac{\mu(s)^2}{J_2(s)}\\
&\le\sum_{s>N/n}\frac1{s^2}
\le\frac1{\lfloor N/n\rfloor}\le\frac{2n}{N}.
\end{aligned}
\]

Here J_2(s)>=s^2/Z because its finite Euler product is at least the full
product 1/Z; the reciprocal-square tail bound follows by an integral comparison.

For W_N contained in {1,...,N}, the exact expected vacancy count consequently
obeys E(m_N-C_N)<=2 sum_{n in W_N} n/N. Thus

\[
\boxed{\sum_{n\in W_N}n=o(N)\quad\Longrightarrow\quad
\mathbb P(W_N\subset X_N)\longrightarrow1.}
\]

In particular the first M_N sites fill if M_N=o(sqrt(N)). A consecutive window
with starting point x_N and length h_N fills under
h_N(x_N+h_N)=o(N). Fixed-size moving windows centered at x_N=o(N) are included.
This is an unconditional written result. It does not assert an optimal scale,
a converse, or a Lean-verified infinite-product construction in this task.

## 5. Far-tail empty regimes

The local formula gives |A_{p^a}(n)|<=J_2(p^a), hence |A_r(n)|<=J_2(r)<=r^2.
Starting from the exact diagonal sum,

\[
K_N(n,n)\le\frac1{Zn^2}\sum_{r=1}^N r^2
=\frac{N(N+1)(2N+1)}{6Zn^2}.
\]

A window of h_N sites all at least x_N empties in probability if
h_N N^3/x_N^2 tends to zero. This is a sufficient, deliberately coarse regime.

A second prime-product law improves the bound for the entire tail. A column
|psi_r(n)|^2 is a probability distribution in n. For p^a parallel r, its
valuation V_p has the exact law

\[
\mathbb P(V_p=a-1)=p^{-2},\qquad
\mathbb P(V_p=a+b)=(1-p^{-2})^2p^{-2b}\quad(b\ge0).
\]

For p not dividing r it is the ordinary Q-geometric law
P(V_p=b)=(1-p^{-2})p^{-2b}. These coordinates are independent, since Q has
independent prime valuations and the finite wavelet tilt factors prime by prime.
Choose independent geometric B_p with this ordinary law and the independent
drop event at each p dividing r. Then the resulting physical integer Y_r
satisfies Y_r<=rT, where T=product_p p^{B_p} has law Q. It follows, for x>=N>=1,

\[
\begin{aligned}
\mathbb E|X_N\cap(x,\infty)|
&=\sum_{r\le N}\mathbb P(Y_r>x)\\
&\le\sum_{r\le N}\mathbb P(T>x/r)
\le\frac{2}{Zx}\sum_{r\le N}r
=\frac{N(N+1)}{Zx}.
\end{aligned}
\]

Thus the entire tail beyond x_N is empty in probability if x_N/N^2 tends to
infinity. This is a written unconditional bound, not a sharp edge location.

## 6. Prime-cutoff discontinuity

For a prime p with p^2>N, define
H_x^(p)=sum_{r<=x,p not dividing r} mu(r)^2/J_2(r). The exact diagonal is

\[
K_N(p,p)=\frac{H_N^{(p)}+(p^2-1)H_{\lfloor N/p\rfloor}^{(p)}}{Zp^2}.
\]

For p>N this reduces to the rough-sector formula and tends to zero. Along a
sequence of prime sites with p_N/N tending to theta>0 and 1/theta not an
integer, the exact formula instead gives

\[
K_N(p_N,p_N)\longrightarrow
\frac{H_{\lfloor1/\theta\rfloor}}Z,
\quad H_0=0,\ H_1=1,\ H_2=4/3,\ H_3=35/24.
\]

For theta>1 the limit is zero; for 1/2<theta<1 it is 1/Z. The proof uses
H_N^(p)<=Z, fixed cutoff for the second sum, and p_N tending to infinity.
There is no claim here that every theta is supplied with a prime sequence.

Bertrand's postulate already supplies primes p_N in (N,2N), so a uniform
positive unit-lattice occupation density throughout [N,2N] is impossible.
This obstructs that specific proposed local limit, not every averaged,
marked, conditioned, or continuum-unfolded limit.

## 7. Uniform arithmetic overlap: a unit-lattice sine obstruction

Let v_p=v_p(n), w_p=v_p(m), and D={p:v_p!=w_p}. From the exact prime-power
wavelet formula, the local absolute sums are

\[
\sum_{a\ge0}\frac{|A_{p^a}(n)A_{p^a}(m)|}{J_2(p^a)}
=\begin{cases}
p^{2v_p}p^2/(p^2-1),&v_p=w_p,\\
2p^{2\min(v_p,w_p)},&v_p\ne w_p.
\end{cases}
\]

The convention at a=0 is A_1=J_2(1)=1. In the unequal case, the signed
local summands are 1, J_2(p),...,J_2(p^min), and -p^(2 min); this retains
the exact cancellation responsible for the zero full inner product.
Absolute summability follows from the convergent product at primes not
dividing nm and the finitely many exceptional local factors. Multiplying
these local sums and the physical Q square-root factors proves the exact
arithmetic overlap identity

\[
\boxed{\sum_{r\ge1}|\psi_r(n)\psi_r(m)|
=\prod_{p\in D}2(1-p^{-2})p^{-|v_p-w_p|}.}
\]

This is also the Hellinger affinity of the auxiliary laws R_n and R_m from
Section 4. With g=gcd(n,m), A=nm/g^2, the exact right side equals
A^(-1) product_{p|A} 2(1-p^(-2)). Consequently, after the complete equality,

\[
|K_N(n,m)|\le\frac{2^{\omega(A)}}A
\le C_\varepsilon A^{-1+\varepsilon}
=C_\varepsilon\left(\frac{g^2}{nm}\right)^{1-\varepsilon},
\qquad 0<\varepsilon<1.
\]

This holds for every N. For a simple explicit bound, 2^omega(A)<=2 sqrt(A) (separate the primes 2,3
from primes at least 5), so |K_N(n,m)|<=2 gcd(n,m)/sqrt(nm) as well.
The elementary second estimate follows by choosing
P=2^(1/epsilon): for p>=P, 2<=p^epsilon, and the finitely many smaller primes
are absorbed in C_epsilon=2^(number of primes below P). No RH estimate or
Mertens cancellation is used.

The same absolute-overlap bound holds for any finite subset of these
wavelets, or for a wavelet-diagonal contraction with coefficients between
0 and 1. Reordering the divisor basis or tapering its diagonal cutoff therefore
does not repair the unit-lattice obstruction. A different operator family or
a spatial scaling outside the excluded regimes would be needed.

For distinct fixed offsets i,j and x_N tending to infinity, put n=x_N+i,
m=x_N+j. Their gcd is at most |i-j|, so the off-diagonal entries tend to zero
uniformly in the projection rank. Along any subsequence where the finitely
many marginals K_N(x_N+i,x_N+i) tend to rho_i, every finite inclusion
determinant tends to product_i rho_i. Inclusion-exclusion gives convergence
of every finite configuration probability to the corresponding independent
Bernoulli law. Since every finite list of marginals has convergent subsequences,
all such subsequential window limits have independent coordinates.

\[
\boxed{\text{No moving fixed-offset window at infinity has a nontrivial}
\atop\text{unit-lattice sine-kernel limit with density }0<\rho<1.}
\]

Indeed that sine kernel has nearest-neighbor entry sin(pi rho)/pi!=0, whereas
the arithmetic kernel tends to zero there. Its two-point inclusion determinant
therefore differs from the product of its marginals. This is a rigorous written
obstruction, not yet a Lean-verified analytic provider.

For continuum windows n_N(u)=floor(x_N+a_N u), with a_N=o(x_N), distinct fixed
u,v satisfy gcd(n_N(u),n_N(v))<=O(a_N), and n_N(u)n_N(v) is comparable to x_N^2.
Thus the rescaled off-diagonal kernel satisfies

\[
a_N|K_N(n_N(u),n_N(v))|
\le C_{\varepsilon,u,v}\frac{a_N^{3-2\varepsilon}}{x_N^{2-2\varepsilon}}.
\]

If the expression on the right tends to zero for some epsilon in (0,1), a
positive-density continuum sine limit is likewise impossible. In particular
a_N<=x_N^(2/3-eta), eta>0, is excluded by choosing epsilon sufficiently small.
The same off-diagonal obstruction applies to the hole kernel I-K_N. This does
not settle scales comparable to the location, or scales large enough that the
bound does not vanish.

For a consecutive physical window of h sites all at least x, one can also
control the entire off-diagonal Hilbert–Schmidt mass. Take 0<epsilon<3/4 and
s=4-4 epsilon>1. Every off-diagonal gcd is at most h-1. Counting pairs of
multiples of each divisor d<=h gives

\[
\sum_{n\ne m\in W}\gcd(n,m)^s
\le \sum_{d\le h}d^s\,4h^2/d^2
\le C_s h^{s+1}.
\]

The first inequality uses g^s<=sum_{d|g}d^s; a length-h interval has at most
h/d+1<=2h/d multiples of d. Thus, uniformly in N,

\[
\boxed{\sum_{n\ne m\in W}K_N(n,m)^2
\le C_\varepsilon h^{5-4\varepsilon}/x^{4-4\varepsilon}.}
\]

In particular h<=x^(4/5-eta), eta>0, forces this mass to zero, by taking
epsilon sufficiently small. If in addition the mean count tends to lambda
and max_{n in W}K_N(n,n) tends to zero, then tr(K_W^2) tends to zero as well.
For eigenvalues lambda_j of K_W, retain the exact gap identity

\[
\log\det(I-K_W)=-\sum_{k\ge1}\operatorname{tr}(K_W^k)/k
\]

once their maximum is below 1. Since max_j lambda_j<=sqrt(tr(K_W^2)), the
sum of terms k>=2 tends to zero, so the gap tends to exp(-lambda). The same
argument with I+(z-1)K_W for 0<=z<=1 gives the Poisson(lambda) count generating
function. Bounded means give tightness by Markov; the limiting generating
function uniquely identifies each subsequential count law.
This is a conditional Poisson count limit with explicit, stated
marginal conditions, not a construction of those conditions.

A continuum unit-density sine scaling would supply both conditions on
bounded unfolded intervals, but its compressed sine kernel has a strictly
positive squared-kernel integral. Hence h<=x^(4/5-eta) cannot yield such a
sine limit under the usual local trace/gap convergence. This stronger
window-level obstruction complements the pointwise 2/3 threshold. The
proof is written analysis; its divisor estimates and operator limit have
not been formalized in this task.

There is a further hole-specific improvement. The exact complementary Gram
kernel and Cauchy–Schwarz give, at distinct n,m,

\[
|K_N(n,m)|^2=|H_N^{\rm hole}(n,m)|^2
\le (1-K_N(n,n))(1-K_N(m,m)).
\]

Combine this with the vacancy bound from Section 4 and the overlap bound with
epsilon=1/4. For a consecutive window of h sites between x and x+h, suppose
x tends to infinity, h<=C x, h x/N<=B, and h tends to infinity. Then x+h<=N
eventually. Split pairs into gcd<=D and gcd>D. The first contribution is at
most C_1 h^2 D^3/x^3. The number of pairs in the second group is at most
4h^2/D; their squared kernels are at most 4(x+h)^2/N^2. Therefore

\[
\sum_{n\ne m\in W}K_N(n,m)^2
\le C_1 C^2D^3/x + 16(1+C)^2B^2/D.
\]

Choosing D comparable to x^(1/4) proves an O(x^(-1/4)) off-diagonal energy
bound. Also max vacancy is O(1/h), and the mean hole count is bounded. Hence
the entire squared trace of the compressed hole kernel tends to zero. If its
mean tends to lambda, the same exact generating determinant as above gives
Poisson(lambda) hole counts, not sine counts. No mean limit is claimed here.

This also covers the first M_N=O(sqrt(N)) sites, by a truncation argument.
For fixed alpha>0, apply the preceding result to [alpha M_N,M_N]. The expected
holes below alpha M_N are at most (alpha M_N)(alpha M_N+1)/N. Since the full
hole kernel is an orthogonal projection, its exact row identity is

\[
\sum_{m\ge1}|H_N^{\rm hole}(n,m)|^2=H_N^{\rm hole}(n,n).
\]

The omitted rows and cross terms therefore contribute at most twice that
small-head mean. Let N tend to infinity and then alpha tend to zero. This
proves tr((H_{N,[1,M_N]}^{hole})^2)->0; if M_N is bounded the same conclusion
follows directly from the vacancy bound. Thus convergent mean hole counts
on the natural sqrt(N) head scale have Poisson limits. A positive-density
sine-hole limit on that scale is excluded. These are written proofs; the
prime-product estimate, row Parseval argument, and limit consumer remain
to be formalized. Larger or differently normalized hole regimes remain open.

## 8. What a remaining sine-kernel limit would actually require

The infinite-rank sine kernel has strictly positive two-point determinant
1-sinc(pi(u-v))^2 at distinct continuum sites. Finite rank N by itself does
not obstruct it as N tends to infinity. A signature class restricted process,
which has at most one point, cannot have this positive-density limit.

The remaining candidates require a genuinely growing continuum scale that
escapes both pointwise and window-level overlap obstructions, with arithmetic oscillations resolved by a
justified unfolding or averaging, or suitably scaled holes. The transition
region x_N comparable to N at fixed unit-lattice spacing is now ruled out.
The sqrt(N) scale is not proved to be an actual transition threshold.
If its hole means converge, the combined estimate instead gives Poisson
count limits; a sine-hole limit there is excluded.

For a proposed continuum unfolding n_N(u)=floor(x_N+a_N u), a_N tending to
infinity, the counting kernel becomes a_N K_N(n_N(u),n_N(v)) relative to mesh
measure 1/a_N. Unit-density sine convergence requires, after an allowed
row/column gauge if needed,

\[
a_N K_N(n_N(u),n_N(v))\longrightarrow
\frac{\sin\pi(u-v)}{\pi(u-v)},
\]

with diagonal value 1. A discrete sine limit instead uses integer offsets
and a density rho in (0,1), with target kernel sin(pi rho(i-j))/(pi(i-j))
and diagonal rho. Those are different normalizations.

Specific unresolved estimates are:

1. A local density profile and unfolding, with quantitative control of
   arithmetic exceptional sites at the chosen scale.
2. Uniform two-site asymptotics for the signed sum
   sum_{r<=N} A_r(n)A_r(m)/J_2(r), including n!=m. A diagonal or trace estimate
   cannot determine its oscillatory shape.
3. Bounds giving tightness and local operator convergence; trace-norm
   convergence of compressed kernels is one sufficient way to control gap
   determinants as windows grow. Fixed finite determinants alone do not do so.
4. If holes are used, corresponding estimates for the exact complementary
   Parseval tail sum_{r>N} psi_r(n)psi_r(m).

Prime independence supplies the scalar occupation law and a uniform
off-diagonal overlap estimate. The latter rules out nontrivial unit-lattice
sine limits and a range of continuum scales. It supplies neither a remaining
sine asymptotic provider nor translation invariance. Signature exclusion and
prime-cutoff discontinuity give additional obstructions. All continuum
scalings are not yet settled.

## 9. RH and Hilbert–Pólya separation

Full divisor-basis completeness and all results above are unconditional.
The basis includes the constant mode at r=1. Its occupation limit therefore
does not establish approximation of 1 by legal residue atoms. The unweighted full projection has nonzero eigenvalues all equal to 1,
with multiplicity N, so its range-restricted determinant is exactly
(1-z^2)^N. That spectrum itself cannot be the varying zeta ordinates.
Weighted or spatially compressed operators have different spectra and
require a separate arithmetic identification. A zeta-zero
identification, a remaining sine-limit provider, and any zeta determinant/trace identity
remain separate open obligations. Even a sine limit would not, on its own,
identify a self-adjoint operator whose spectral determinant is completed zeta.

## Finite computational checks

Exact rational arithmetic independently matched the reverse prime-product
probability formula with the direct divisor-wavelet diagonal for all 192 pairs
N=1,...,8 and n=1,...,24. Rough-site feature equality was checked for N=1,...,8.
The local absolute-overlap formula was checked exactly for all 180 pairs
of valuations v,w=0,...,5 at p=2,3,5,7,11.
These finite calculations support the written derivation; they are neither
Lean checks nor evidence of a scaling limit.

## Verification ledger

Successful targeted server verification on 14 October 2026:
`job_p4TWFKadHYuhQO_T8qA9lu0lh8EBGj5c` completed with classification
`success`, exit code 0, and `verified: true` (15.687 seconds).
The generic finite-feature module was replayed from its completed build;
`RH/QDivisorDPPWindows.lean` built in 3.3 seconds and
`RH/QDivisorDPPArithmeticWindows.lean` built in 2.7 seconds.

The same job printed axioms for all 21 new theorems: three generic
finite-feature theorems, thirteen Q-DPP finite-rank and moving-window
theorems, and five arithmetic-coordinate and signature theorems.
Every declaration depends only on `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, `admit`, custom `axiom`, or `unsafe` declaration
is used in the new sources.

The central verified application is
`RiemannResearch.RH.QDivisorDPP.basisLaw_occupation_eq_zero_of_dimension_lt`:
more than N distinct sites have exactly zero simultaneous occupation
probability at projection dimension N. The verified exact moving-window
identities and identical-signature exclusion are in
`RH/QDivisorDPPWindows.lean` and `RH/QDivisorDPPArithmeticWindows.lean`.

Earlier attempts and their resolution:

- `job_hWFSY16Jp8mrPoMpekZWy4AlfdP5tyvF` built the generic helper but timed
  out overall at 900 seconds; a second application check also timed out.
- Interactive diagnostics were empty, but did not establish source-build
  completion. A separate earlier axiom request also timed out.
- Automatic approval review initially rejected publication after these
  incomplete checks; that rejection created no checkpoint job or commit.
- After the user authorized the push and the connection recovered,
  checkpoint `job_RMXdawmiVPSBNcMP6DVda9gdRvFDHXYA` returned two concrete
  rewrite errors: DPP set-membership events needed explicit conversion to
  the Boolean occupation events. It failed before publication.
- The two conversions were repaired; the successful targeted build and
  complete 21-theorem axiom audit above verify the corrected sources.

Publication uses the server-gated checkpoint, including the aggregate export
and affected modules. Its final job and commit identifiers are reported with
task completion; targeted source verification alone is not a publication claim.

The infinite prime-product laws, arithmetic overlap estimates, and scaling
arguments in this report remain written proofs, not newly Lean-verified
providers. Broader continuum limits and a zeta-identification bridge remain
unresolved; no RH or Hilbert–Pólya realization is asserted.

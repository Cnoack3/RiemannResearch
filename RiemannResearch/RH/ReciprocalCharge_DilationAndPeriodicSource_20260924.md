# Reciprocal charges: signed dilation correlations and periodic source decay

Prepared 24 September 2026. Mathematical research note. No novelty claim is made.

Formal status: the exact norm limit and the actual integer-dilation correlation
formula are Lean-verified in the companion modules. Prime evaluations are
recorded in the execution report. The general rational-dilation formula,
quotient-spike approximation, joint finite averages, rescaled energy profile,
and periodic source limits below are written mathematics, not Lean-verified.

This note extends the supplied `ReciprocalChargeNormLimit20260924.md` using its
now-formalized norm separation. It also proves the remaining centered-periodic
part of the raw Gram-source limit. The logarithmic Möbius mean used for the
constant part is classical, but its Lean import must still be supplied.

## 1. Definitions and the existing norm argument

Work in the real Pareto Hilbert space

\[
H_P=\left\{f:\mathbb N_{>0}\to\mathbb R:
\sum_{k\ge1}\frac{f(k)^2}{k(k+1)}<\infty\right\}.
\]

Write

\[
m(X)=\sum_{1\le n\le X}\frac{\mu(n)}n,\qquad
a_N(k)=m(\lfloor N/k\rfloor)-m(\lfloor N/(k+1)\rfloor),
\]
\[
b_N(k)=m(\lfloor N/(k+1)\rfloor),\qquad
q_N(k)=\frac{m(\lfloor N/k\rfloor)}k-
\frac{m(\lfloor N/(k+1)\rfloor)}{k+1},
\]
\[
Q_N(k)=k(k+1)q_N(k),\qquad
x_N(k)=\frac{Q_N(k)}{\sqrt{k(k+1)}}.
\]

Thus the passage from (Q_N) to (x_N) is an isometry to ordinary
\(\ell^2(\mathbb N_{>0})\). Both vectors vanish for \(k>N\).

The supplied argument establishes, using PNT and elementary quotient windows,

\[
L_N=\sum_{k(k+1)\le N}a_N(k)^2\longrightarrow0,
\quad R_N=\sum_{k\ge1}\frac{a_N(k)^2}k\longrightarrow0,
\quad B_N=\sum_{k\ge1}\frac{b_N(k)^2}{k(k+1)}\longrightarrow0.
\]

Its complete norm limit is

\[
\|Q_N\|_P^2\longrightarrow
S:=\sum_{n\ge1}\frac{\mu(n)^2}{n^2}=\frac{15}{\pi^2}.
\]

The subsequent limit arguments are mathematical consequences of these results.
The formalized norm and integer-dilation theorems use these actual vectors.
The other arguments retain the separate formal-status boundary stated above.

## 2. A precise quotient-spike approximation

Put

\[
J_N=\{1\le n\le N:N<\lfloor N/n\rfloor(\lfloor N/n\rfloor+1)\}
\]

and define

\[
z_N=\sum_{n\in J_N}\frac{\mu(n)}n e_{\lfloor N/n\rfloor},
\]

where (e_k) is the ordinary orthonormal coordinate vector. Quotient windows in
this region contain at most one integer. Consequently their coordinates are
distinct, and exactly

\[
z_N(k)=\mathbf1_{N<k(k+1)}a_N(k).
\]

The exact coordinate identity is

\[
x_N(k)=\sqrt{1+1/k}\,a_N(k)+\frac{b_N(k)}{\sqrt{k(k+1)}}.
\]

Because \((\sqrt{1+t}-1)^2\le t\) for \(t\ge0\), the triangle inequality gives

\[
\boxed{\|x_N-z_N\|_2\le\sqrt{L_N}+\sqrt{R_N}+\sqrt{B_N}.}
\]

In particular, \(x_N-z_N\to0\) strongly. This estimate preserves the signed
coefficients of every spike; no absolute-value replacement enters the
correlation calculation.

For integers \(D\ge1\) and \(N\ge D^2\), put

\[
z_{N,D}=\sum_{1\le n\le D}\frac{\mu(n)}n e_{\lfloor N/n\rfloor}.
\]

For \(N\ge D^2\), every \(n\le D\) is in \(J_N\). Hence

\[
\|z_N-z_{N,D}\|_2^2
=\sum_{\substack{n\in J_N\\n>D}}\frac{\mu(n)^2}{n^2}
\le\sum_{n>D}\frac1{n^2}\le\frac1D.
\]

Thus (x_N) is approximated, with an error whose limiting upper bound is at
most (D^{-1/2}), by finitely many explicit signed quotient spikes. The
parameter (D) is chosen first and (N) is then taken to infinity.

## 3. Exact signed dilation correlations

**Theorem.** Let \(a,b\ge1\) be integers. Set
\(g=\gcd(a,b)\), \(a'=a/g\), and \(b'=b/g\). Then

\[
\boxed{
\lim_{N\to\infty}\langle Q_{aN},Q_{bN}\rangle_P
=\frac1{a'b'}\sum_{d\ge1}
\frac{\mu(a'd)\mu(b'd)}{d^2}.}
\]

**Proof.** Fix (D). The scalar product of the truncated spikes is

\[
\langle z_{aN,D},z_{bN,D}\rangle
=\sum_{n,m\le D}\frac{\mu(n)\mu(m)}{nm}
\mathbf1_{\lfloor aN/n\rfloor=\lfloor bN/m\rfloor}.
\]

For fixed (n,m), equal rational slopes (a/n=b/m) give identical floors
for every (N). If the slopes differ, their distance multiplied by (N)
eventually exceeds one, so the floors are eventually distinct. Since the sum
is finite, its limit equals the sum over (a/n=b/m). Coprimality of (a',b')
shows that these pairs are exactly

\[
n=a'd,\qquad m=b'd.
\]

Therefore

\[
\lim_N\langle z_{aN,D},z_{bN,D}\rangle
=\frac1{a'b'}
\sum_{d\le D/\max(a',b')}\frac{\mu(a'd)\mu(b'd)}{d^2}.
\]

The difference between the actual and truncated scalar products is bounded by

\[
\|x_{aN}-z_{aN,D}\|_2\|x_{bN}\|_2
+\|z_{aN,D}\|_2\|x_{bN}-z_{bN,D}\|_2.
\]

The actual norms tend to \(\sqrt S\), the truncated norms are eventually
bounded by \(\sqrt S\) for each fixed D, and the limiting truncation errors
are at most (D^{-1/2}).
Letting (D\to\infty) completes the proof, because the displayed scalar
series is absolutely convergent. ∎

Since (a') and (b') are coprime, write (h=a'b'). If (h) is not
squarefree, the limit is zero. If (h) is squarefree, then

\[
\mu(a'd)\mu(b'd)
=\mu(h)\mu(d)^2\mathbf1_{\gcd(d,h)=1}.
\]

Removing the finitely many Euler factors at primes dividing (h) gives

\[
\boxed{
\lim_N\langle Q_{aN},Q_{bN}\rangle_P
=S\,\mu(h)\prod_{p\mid h}\frac{p}{p^2+1},\qquad h=a'b'.}
\]

The expression also gives zero when (h) is not squarefree because
\(\mu(h)=0\). In particular,

\[
\lim_N\langle Q_N,Q_{2N}\rangle_P=-\frac25S=-\frac6{\pi^2},
\quad
\lim_N\langle Q_N,Q_{3N}\rangle_P=-\frac3{10}S=-\frac9{2\pi^2},
\]
\[
\lim_N\langle Q_{2N},Q_{3N}\rangle_P=\frac3{25}S.
\]

These are signed correlations. In particular, the (2N,3N) correlation has
the opposite sign from the correlations of either with (N).

## 4. Exact two- and three-scale energies

For real \(u,v,w\), the preceding theorem gives

\[
\boxed{
\lim_N\|uQ_N+vQ_{2N}+wQ_{3N}\|_P^2
=S\left(u^2+v^2+w^2-\frac45uv-\frac35uw+\frac6{25}vw\right).}
\]

The matrix of the quadratic form divided by (S) is

\[
K=\begin{pmatrix}
1&-2/5&-3/10\\
-2/5&1&3/25\\
-3/10&3/25&1
\end{pmatrix}.
\]

It is positive definite: its leading principal minors are
\(1,21/25,1911/2500\).

For two-scale convex averages,

\[
\lim_N\|\tfrac12(Q_N+Q_{2N})\|_P^2=\frac3{10}S,
\qquad
\lim_N\|\tfrac12(Q_N+Q_{3N})\|_P^2=\frac7{20}S.
\]

For the equal three-scale average,

\[
\lim_N\|\tfrac13(Q_N+Q_{2N}+Q_{3N})\|_P^2
=\frac{46}{225}S=\frac{46}{15\pi^2}.
\]

Subject to (u+v+w=1), the unique minimizer of the limiting quadratic form is

\[
(u,v,w)=\frac1{109}(44,35,30),
\]

and the minimum is

\[
\boxed{\lim_N\|\tfrac{44Q_N+35Q_{2N}+30Q_{3N}}{109}\|_P^2
=\frac{21}{109}S=\frac{315}{109\pi^2}.}
\]

Indeed (K(44,35,30)^\top/109=(21/109)(1,1,1)^\top), so the cross term
vanishes for every perturbation with coefficient sum zero; the remaining
quadratic term is positive. If instead (u=1) is fixed with no sum constraint,
the minimizing pair is \((v,w)=(65,45)/176\), and the minimum is
\((273/352)S\).

## 5. Explicit finite averages using only the seeds 2 and 3

For integers (L,M\ge1), define

\[
\mathcal B_{N,L,M}=\frac1{LM}
\sum_{0\le i<L}\sum_{0\le j<M}Q_{2^i3^jN}.
\]

For a prime (p), let

\[
\kappa_p(r)=
\begin{cases}
1,&r=0,\\
-p/(p^2+1),&|r|=1,\\
0,&|r|\ge2.
\end{cases}
\]

The general correlation formula proves

\[
\lim_N\langle Q_{2^i3^jN},Q_{2^{i'}3^{j'}N}\rangle_P
=S\,\kappa_2(i-i')\kappa_3(j-j').
\]

There are (L) equal-index pairs and (2(L-1)) ordered adjacent-index pairs
for the first seed, and similarly for (M). All other pairs give zero.
Consequently the exact limit is

\[
\boxed{
\lim_N\|\mathcal B_{N,L,M}\|_P^2
=S\frac{L+4}{5L^2}\frac{2M+3}{5M^2}.}
\]

For (L=M=2), this equals \((21/200)S=63/(40\pi^2)\), attained by the
average of (Q_N,Q_{2N},Q_{3N},Q_{6N}).

There exists a strictly increasing sequence of integers (N_T\) such that

\[
\left|\|\mathcal B_{N_T,T,T}\|_P^2
-S\frac{(T+4)(2T+3)}{25T^4}\right|\le\frac1T
\qquad(T\ge1).
\]

Choose each (N_T) after (T), above the preceding (N_{T-1}), using the
fixed-(T) limit. It follows that

\[
\boxed{\mathcal B_{N_T,T,T}\longrightarrow0\quad\text{strongly in }H_P.}
\]

This constructs finite arithmetic dilation averages with vanishing energy.
No effective bound for the diagonal (N_T) is claimed, and no uniform
interchange of the (N,T) limits has been used.

## 6. Rescaled energy profile

The same finite-spike approximation proves, for every continuous
\(\varphi:[0,1]\to\mathbb R\),

\[
\boxed{
\lim_N\sum_{k=1}^N k(k+1)q_N(k)^2\varphi(k/N)
=\sum_{n\ge1}\frac{\mu(n)^2}{n^2}\varphi(1/n).}
\]

To see this, truncate to (n\le D), use
\(\lfloor N/n\rfloor/N\to1/n\), and bound the remaining contribution by
\(\|\varphi\|_\infty\sum_{n>D}n^{-2}\), together with the strongly vanishing
error from Section 2. Thus the limiting measure is the finite atomic measure

\[
\sum_{n\ge1}\frac{\mu(n)^2}{n^2}\delta_{1/n}.
\]

For a nonnegative integer (j), its (j)-th moment is

\[
\sum_{n\ge1}\frac{\mu(n)^2}{n^{j+2}}
=\frac{\zeta(j+2)}{\zeta(2j+4)}.
\]

For (j=0,1,2), these are respectively
\(15/\pi^2\), \(945\zeta(3)/\pi^6\), and \(105/\pi^4\).

## 7. Centered periodic source decay

This part concerns different vectors: the raw Möbius residuals, throughout
with \(N\ge1\),

\[
U_N(k)=1+\sum_{d=2}^N\mu(d)g_d(k),\qquad
g_d(k)=\frac{k\bmod d}{d}.
\]

The supplied repository report provides

\[
U_N(k)=k\,m(N)\quad(1\le k\le N),\qquad
|U_N(k)|\le\min(N,k),\qquad |m(N)|\le1,
\]

and (m(N)\to0). Hence (U_N(k)\to0) for every fixed (k).

Let (h:\mathbb N_{>0}\to\mathbb R) be periodic and have sum zero over
one period. Its partial sums (H(k)=\sum_{j=1}^k h(j)) are bounded. Put

\[
F_N(k)=\frac{U_N(k)}{k(k+1)}.
\]

For (k\ge1), the exact residue jump gives

\[
U_N(k+1)-U_N(k)
=m(N)-\sum_{\substack{d\mid k+1\\d\le N}}\mu(d).
\]

Writing \(\tau(n)\) for the number of positive divisors of (n), it follows
that

\[
|U_N(k+1)-U_N(k)|\le1+\tau(k+1).
\]

The exact identity

\[
F_N(k+1)-F_N(k)
=\frac{U_N(k+1)-U_N(k)}{(k+1)(k+2)}
-\frac{2U_N(k)}{k(k+1)(k+2)}
\]

therefore yields the uniform bound

\[
\boxed{
|F_N(k+1)-F_N(k)|
\le\frac{3+\tau(k+1)}{(k+1)(k+2)}.}
\]

This dominating sequence is summable. For example,

\[
\sum_{n\ge1}\frac{\tau(n)}{n^2}
=\sum_{d,r\ge1}\frac1{d^2r^2}=\zeta(2)^2,
\]

where the rearrangement is justified by nonnegativity. Alternatively,
the elementary bound \(\tau(n)\le2\sqrt n\) reduces this to a convergent

\(3/2\)-power series.

For every finite (K), Abel summation gives exactly

\[
\sum_{k=1}^K h(k)F_N(k)
=H(K)F_N(K)+\sum_{k=1}^{K-1}H(k)(F_N(k)-F_N(k+1)).
\]

Because (H) is bounded and \(|F_N(K)|\le1/(K+1)\), the boundary term
tends to zero as (K\to\infty). Thus

\[
\boxed{
\langle U_N,h\rangle_P
=\sum_{k\ge1}H(k)(F_N(k)-F_N(k+1)).}
\]

Each summand tends to zero as (N\to\infty), and the uniform summable
dominator just proved applies. Dominated convergence proves

\[
\boxed{\langle U_N,h\rangle_P\longrightarrow0
\quad\text{for every mean-zero periodic }h.}
\]

This centered result uses only the ordinary Möbius mean (m(N)\to0), the
raw pointwise bound, the exact residue jump, and elementary summability.

## 8. The constant mode and actual fixed Gram sources

The complete pairing with the target is exactly

\[
\langle U_N,\mathbf1\rangle_P
=1+\sum_{d=1}^N\frac{\mu(d)\log d}{d},
\]

because \(\langle g_d,\mathbf1\rangle_P=(\log d)/d\).
The classical logarithmic Möbius mean says

\[
\sum_{d=1}^N\frac{\mu(d)\log d}{d}\longrightarrow-1.
\]

For a fixed (m\ge2), (g_m) has period mean
\(c_m=(m-1)/(2m)\). The sequence (h_m=g_m-c_m\mathbf1) is mean-zero
periodic, so

\[
\boxed{
\langle U_N,g_m\rangle_P
=c_m\left(1+\sum_{d\le N}\frac{\mu(d)\log d}{d}\right)
+\sum_{k\ge1}H_m(k)(F_N(k)-F_N(k+1))\longrightarrow0.}
\]

In the notation of the agenda, this is the actual fixed-coordinate source
decay

\[
\boxed{(b_N+G_N\mu_N)_m\longrightarrow0
\quad\text{for every fixed }m.}
\]

Only stages (N\ge m) are needed for that coordinate. The same proof applies
to every fixed periodic test sequence, by subtracting its period mean.

**Formal import boundary.** The logarithmic mean is recorded in NIST DLMF
27.11.15; the page identifies it as equivalent to PNT. A citation does not
install a Lean theorem. A complete Lean version of the full source statement
must prove this result from existing PNT infrastructure or retain it as an
explicit premise until that import is completed. In contrast, the centered
periodic result can be formalized independently of the logarithmic mean.

## 9. Why these results do not prove RH

The reciprocal vectors represent ordered reciprocal-charge functionals.
Their dilation averages converging strongly to zero means that those averaged
functionals tend to zero uniformly on the unit ball. These vectors are not
the finite legal approximants of the target, and these identities provide no
map taking the averages to legal approximants with controlled Pareto error.
In particular, they neither show that the projection residual vanishes nor
determine the signed Schur saturation value.

Likewise, fixed Gram-source coordinates tending to zero do not control the
growing inverse Gram matrix. The unresolved implication would require, for
the actual arithmetic sources,

\[
\left[G_N^{-1}(b_N+G_N\mu_N)\right]_m\longrightarrow0
\quad\text{for every fixed }m.
\]

Small source coordinates alone are insufficient: the dimension grows and the
Gram matrices can have small eigenvalues. None of the estimates above bounds
their amplification on the actual source. That remains the RH-strength gap.

## 10. Wolfram corroboration

Wolfram Language evaluated the actual finite sequences using
`MoebiusMu`, prefix sums, and their exact quotient coordinates. The output was:

| (N) | \(\|Q_N\|_P^2\) | \(\langle Q_N,Q_{2N}\rangle_P\) | \(\langle Q_N,Q_{3N}\rangle_P\) |
|---:|---:|---:|---:|
| 100 | 1.4916765001 | -0.6222350868 | -0.4536252142 |
| 1000 | 1.5189735043 | -0.6092003735 | -0.4571032790 |
| 10000 | 1.5210621088 | -0.6083378069 | -0.4562806169 |
| Exact proposed limit | \(15/\pi^2\) | \(-6/\pi^2\) | \(-9/(2\pi^2)\) |

Wolfram also confirmed the rational matrix, its determinant, and the optimal
three-scale coefficients in Section 4. These computations corroborate the
proof; they do not replace it or Lean verification.

## 11. Primary references and Mathlib route for the constant

- Michel Balazard, *An arithmetical function related to Báez-Duarte's
  criterion for the Riemann hypothesis*, especially Propositions 5–7:
  https://arxiv.org/pdf/1812.04309 . This supplies the classical weak reciprocal
  framework. The signed dilation formula in this note is derived directly
  above; no claim that Balazard states it is made.
- NIST DLMF, equation 27.11.15 and its following explanatory paragraph:
  https://dlmf.nist.gov/27.11.E15 .
- Juan Manzur, Waleed Noor, Gustavo Quintero, *A Hardy space approximation
  supporting zero-free half-planes for the ζ-function*:
  https://arxiv.org/abs/2606.16097 . Its abstract states a zero-free consequence
  of approximation and describes numerical analysis; it does not provide
  unconditional approximation down to the critical line.
- Jean-François Burnol, *A note on Nyman's equivalent formulation of the
  Riemann hypothesis*: https://arxiv.org/pdf/math/9910055 . Its continuous
  all-parameter projection product does not by itself identify the integer
  projection norm in the present model.

The following current Mathlib declarations were confirmed in its official
web documentation. They were not checked in the repository's precise pinned
version during this subtask:

1. `EulerProduct.eulerProduct`, in
   `Mathlib.NumberTheory.EulerProduct.Basic`, gives convergence of finite
   Euler products for a norm-summable multiplicative function. Apply it to
   \(f(n)=(\mu(n):\mathbb C)^2/(n:\mathbb C)^2\), with value zero at zero.
   Its local prime factor is exactly \(1+p^{-2}\).
2. `ArithmeticFunction.isMultiplicative_moebius`,
   `ArithmeticFunction.moebius_apply_prime_pow`, and
   `ArithmeticFunction.abs_moebius_le_one`, in
   `Mathlib.NumberTheory.ArithmeticFunction.Moebius`, provide the necessary
   multiplicativity, prime-power simplification, and summability domination.
3. `riemannZeta_eulerProduct`, in
   `Mathlib.NumberTheory.EulerProduct.DirichletLSeries`, gives convergence of
   finite products at (s=2,4). For every finite prime set the exact identity
   is
   \[
   \prod_p(1+p^{-2})
   =\frac{\prod_p(1-p^{-2})^{-1}}{\prod_p(1-p^{-4})^{-1}}.
   \]
   The denominator tends to the nonzero value \(\zeta(4)\), so uniqueness of
   limits yields \(S=\zeta(2)/\zeta(4)\).
4. `riemannZeta_two` and `riemannZeta_four`, in
   `Mathlib.NumberTheory.LSeries.HurwitzZetaValues`, evaluate the quotient as
   (15/\pi^2). A final real-part/cast argument returns to the real sum.

Documentation URLs:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EulerProduct/Basic.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EulerProduct/DirichletLSeries.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Moebius.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/HurwitzZetaValues.html

The finite-product route avoids silently dividing two arbitrary infinite
products. An alternative is the unique square-times-squarefree decomposition
and a nonnegative double-series rearrangement; this may require additional
uniqueness infrastructure in Lean.


## Repository provider located during this continuation

The existing module `RiemannResearch/NumberTheory/SquarefreeEulerSeries.lean`
already proves `RiemannResearch.NumberTheory.squarefree_reciprocal_square_sum`,
evaluating the full real series as `15 / Real.pi ^ 2` without an arithmetic
hypothesis. Thus no new Euler-product import is needed for the norm limit.

A second route to the dilation-correlation theorem avoids the Hilbert-space
spike approximation: at cutoff `hN`, use the charge sequence
`eta_h(n) = mu(n)/n + 1_{h divides n} mu(n/h)/(n/h)`. Its partial sum is exactly
`m(M)+m(floor(M/h))`. After dividing by `h+1`, the general quotient-kernel
energy theorem applies. Polarization recovers the signed correlation series.
This route is suitable for Lean because it reuses the exact finite window theorem.

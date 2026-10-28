# Horizontal moments and the third prime-phase coefficient

Date: 2026-10-28. These are deductions from the existing project bounds and
classical analytic inputs, not a claim of literature novelty.

## Conventions and the exact identity

Every sum below runs over the actual nontrivial zeros
\(\rho=\beta+i\gamma\), \(0<\gamma\le T\), with analytic multiplicity. Set
\(\ell=\log T\), \(b_\rho=\beta-\tfrac12\), and
\[
Z_T(u)=\sum_\rho e^{iu\gamma},\qquad
L_T(u)=\sum_\rho e^{u(\rho-1/2)},\qquad
M_{2j}(T,u)=\sum_\rho b_\rho^{2j}e^{iu\gamma}.
\]
Reflection preserves the ordinate and multiplicity, and gives
\(L_T(u)=\sum_\rho e^{iu\gamma}\cosh(ub_\rho)\).
For every integer \(J\ge0\), define
\[
r_J(x)=\cosh x-\sum_{j=0}^J\frac{x^{2j}}{(2j)!}.
\]
The complete signed identity is
\[
E_J(T,u):=Z_T(u)-L_T(u)
 +\sum_{j=1}^J\frac{u^{2j}}{(2j)!}M_{2j}(T,u)
 =-\sum_\rho e^{iu\gamma}r_J(ub_\rho).
\tag{1}
\]
No RH or density hypothesis is needed for (1).

## A uniform remainder at every order

Write the classical Selberg input, after reflection, as
\[
D_T(t):=\#\{\rho:|b_\rho|>t\}
 \le 2CT\ell e^{-a\ell t},\qquad 0\le t\le\tfrac12.
\tag{2}
\]
The classical zeta theorem permits \(a=1/4\), with absolute \(C\) and a
height threshold. The Lean project keeps its proof as an open provider
obligation; it does not replace it by RH.

The nonnegative cosh series gives, for \(0<v\) and \(|u|\le v\),
\[
r_J(ut)\le (|u|/v)^{2J+2}(\cosh(vt)-1)\qquad(t\ge0).
\]
The existing exact finite layer-cake formula bounds the final cosh sum by
\(2CT\ell\,v^2/((a\ell)^2-v^2)\). Taking \(v=a\ell/2\) proves
\[
\boxed{\quad
\frac{|E_J(T,u)|}{T}
 \le \frac{2^{2J+3}C}{3a^{2J+2}}
       \frac{|u|^{2J+2}}{\ell^{2J+1}},
\qquad |u|\le a\ell/2 .
\quad}
\tag{3}
\]
The Lean theorem retains the equivalent factored expression, which is also
valid at \(u=0\). In particular, for \(a=1/4\),
\[
\frac{|Z_T(u)-L_T(u)+(u^2/2)M_2(T,u)|}{T}
 \le \frac{8192C}{3}\frac{u^4}{\ell^3},
\qquad |u|\le\ell/8.
\tag{4}
\]
The constants and threshold do not depend on the frequency in this band.

There is a sharper ordinary analytic bound, not needed for the Lean
comparison-frequency proof:
\[
\frac{|E_J(T,u)|}{T}
 \le 2C\ell\,
 \frac{(|u|/(a\ell))^{2J+2}}{1-(u/(a\ell))^2},
 \qquad |u|<a\ell.
\tag{5}
\]
Indeed, finite layer cake gives \(\int_0^{1/2}D_T(t)
\,\frac{d}{dt}r_J(|u|t)\,dt\). The integrand is nonnegative. Extend the upper
endpoint to infinity, expand the nonnegative derivative series, and use
\(\int_0^\infty e^{-\lambda t}t^{k-1}dt=(k-1)!/\lambda^k\).
The resulting geometric series is exactly (5).
For \(J=1,a=1/4,|u|\le\ell/8\), this improves \(8192C/3\) to \(2048C/3\).
Wolfram independently evaluated the corresponding scalar integral as
\(u^4/(\lambda^4-\lambda^2u^2)\); the proof above is the justification.

## The exact missing limit for a third term

For a fixed rational \(q=n/m>1\), put \(u=\log q\) and
\[
A(q)=-\frac{\Lambda(q)}{2\pi\sqrt q},
\]
where \(\Lambda(q)=0\) unless \(q\) is an integral prime power.
The project's uniform rational Landau bound gives, without a density
hypothesis,
\[
L_T(u)/T=A(q)+o(1/\ell).
\]
The strengthened bound checked in this development is
\(O(\ell^{-3})\), uniformly for \(1\le m<n\) and
\(\log n\le\ell/8\). Thus (4) implies
\[
\ell\bigl(Z_T(u)/T-A(q)\bigr)
 =-\frac{u^2}{2}\,\frac{\ell}{T}M_2(T,u)+o(1).
\tag{6}
\]
For every \(m_2\in\mathbb C\), (6) yields the equivalence
\[
\boxed{
\frac{\ell}{T}M_2(T,u)\longrightarrow m_2
\quad\Longleftrightarrow\quad
\ell\bigl(Z_T(u)/T-A(q)\bigr)
 \longrightarrow-\frac{u^2}{2}m_2 .
}
\tag{7}
\]
The forward direction, converse, and exact normalization have Lean proofs.
The coefficient \(m_2\) is not asserted to exist along all heights.

This is the next analytic target in a necessary-and-sufficient form:
prove convergence of the oscillatory horizontal energy. Bounds on its
absolute value alone do not establish convergence.

## Fourier synthesis and uniformity

This section gives the ordinary analytic extension of the checked
single-mode and finite-band theorems. It is not a claim that the full
countable synthesis below was newly formalized in this checkpoint.

For a finite set of primes \(P\), define
\[
\Theta_P(\gamma)=\left(\frac{\gamma\log p}{2\pi}\bmod1\right)_{p\in P},
\quad
u_h=\sum_{p\in P}h_p\log p,\quad H(h)=\sum_{p\in P}|h_p|\log p.
\]
For \(f=\sum_h c_h e^{2\pi i h\cdot\theta}\), put
\[
\|f\|_{\mathcal A_s}=\sum_h|c_h|(1+H(h))^s,\qquad
D_P=\sum_{p\in P}\frac{\log p}{2\pi}\partial_{\theta_p}.
\]
Define the arithmetic functional \(C_P\) by
\[
C_P(f)=\sum_h c_h A_h,\quad
A_0=0,\quad
A_{k e_p}=-\frac{\log p}{2\pi p^{|k|/2}}\ (k\ne0),\quad
A_h=0\text{ for mixed modes}.
\]
This equals \(\int fG_P\,d\theta\) for the usual finite-prime FMZ density.

The all-frequency quartic estimate follows by a height split.
In the band \(\log\max(n,m)\le\ell/8\), use (4) and the proved
uniform inverse-cubic-log Landau bound. Outside it, set
\(w=1+\log n+\log m\), so \(\ell<8w\), and use
\[
|Z_T(u)|/T\le C_N\ell,\quad |A(q)|\le w,\quad
|M_2(T,u)|/T\le\frac{4C}{a^2\ell}.
\]
At \(a=1/4\), these three contributions cost respectively at most
\(4096C_N\), \(512\), and \(2048C\), times \(w^4/\ell^3\).
For negative \(u\) take conjugates. At \(u=0\) subtract \(N(T)\)
exactly and the quadratic correction vanishes. Hence one constant \(K\)
works for all rational modes. For reduced prime coordinates,
\(w=1+H(h)\).

Absolute Fourier summation therefore proves
\[
\boxed{
\sum_\rho f(\Theta_P(\gamma))
 =N(T)\int f+TC_P(f)
 +\frac12\sum_\rho b_\rho^2D_P^2f(\Theta_P(\gamma))
 +O\!\left(\frac{T}{\ell^3}\|f\|_{\mathcal A_4}\right).
}
\tag{8}
\]
The sign is positive because \(D_P^2 e^{2\pi i h\cdot\theta}
=-u_h^2e^{2\pi i h\cdot\theta}\).
Constants are independent of \(P\) when the arithmetic weighted norm
displayed here is used. This does not assert an unrestricted bound for
indicator boxes or arbitrary moving tests.

The same split works at every fixed order \(J\): layer cake bounds
\[
\sum_\rho |b_\rho|^{2j}
 \le \frac{2C(2j)!}{a^{2j}}\frac{T}{\ell^{2j-1}},\qquad j\ge1,
\]
and the normalized uniform Landau envelope
\(T^{-1/2}\operatorname{poly}(\ell)\) is smaller than every fixed
inverse power of \(\ell\). Consequently the general ordinary analytic
hierarchy is
\[
\sum_\rho f(\Theta_P(\gamma))
 =N(T)\int f+TC_P(f)
 +\sum_{j=1}^J\frac{(-1)^{j+1}}{(2j)!}
     \sum_\rho b_\rho^{2j}D_P^{2j}f(\Theta_P(\gamma))
 +O_J\!\left(\frac{T}{\ell^{2J+1}}\|f\|_{\mathcal A_{2J+2}}\right).
\tag{9}
\]
The moments in (9) still depend on \(T\). This is a hierarchy with
controlled remainders, not a Poincare expansion with fixed coefficients.
Even leading limits for all the rescaled moments would not alone supply
every subsequent coefficient; lower moments may need their own
higher-order expansions.

## A subsequential third coefficient

This is an ordinary analytic consequence, with its proof recorded here.
The measure-level compactness and synthesis are not kernel-checked below.

Define the positive horizontal-energy measures
\[
\nu_{P,T}=\frac{\ell}{T}\sum_\rho b_\rho^2
                  \delta_{\Theta_P(\gamma)}.
\]
Layer cake and (2) give
\(\nu_{P,T}(\mathbb T^P)\le4C/a^2\).
Compactness of the torus implies that every sequence \(T_n\to\infty\)
has a subsequence along which \(\nu_{P,T_n}\) converges weakly to a finite
positive measure \(\nu_P\). Equation (8) gives, on that subsequence,
\[
\boxed{
\frac{\ell_n}{T_n}
 \left[\sum_{\rho:\gamma\le T_n}f(\Theta_P(\gamma))
       -N(T_n)\int f-T_nC_P(f)\right]
 \longrightarrow \frac12\int D_P^2 f\,d\nu_P .
}
\tag{10}
\]
Convergence is uniform on \(\|f\|_{\mathcal A_4}\le1\). To verify this,
split at height \(R\). There are finitely many modes of height at most
\(R\), and their measure Fourier coefficients converge. If all masses
are at most \(M\), the remaining pairing is bounded by
\(2M(1+R)^{-2}\|f\|_{\mathcal A_4}\), using \(|u_h|\le H(h)\).
The error from (8), after scaling, is \(O(\ell_n^{-2})\).

There is a single subsequence valid for all prime sets: use the compact
metrizable product \(K=\prod_p\mathbb T\), with the same energy measures.
Characters are indexed by finitely supported integer prime vectors.
A height ball is finite because
\(\prod_p p^{|h_p|}\le e^R\). The same argument gives uniformity on the
global arithmetic \(\mathcal A_4\) unit ball. The arithmetic functional
is defined by the compatible coefficients \(A_h\), which are bounded.
No convergence of an ordinary density series \(\sum_p G_{\{p\}}\)
is asserted.

There is also a useful description of the limiting energy. Consider the
probability measures
\[
\eta_T=\frac1{N(T)}\sum_\rho
       \delta_{(\Theta(\gamma),\,y=\ell b_\rho)}.
\]
By (2) and \(N(T)/(T\ell)\to1/(2\pi)\), their marks have uniformly
exponential tails. They are tight on \(K\times\mathbb R\), and all fixed
mark moments are uniformly integrable. A subsequential limit \(\eta\)
has Haar phase marginal, by prime-phase equidistribution, and is
symmetric in \(y\), by exact reflection. If
\(v(\theta)=\mathbb E_\eta[y^2\mid\theta]\), then
\[
d\nu(\theta)=\frac{v(\theta)}{2\pi}\,d\theta,\qquad
\frac12\int D^2f\,d\nu=\frac1{4\pi}\int D^2f\,v\,d\theta.
\]
Conditional Jensen and the exponential moment bounds imply
\(v\ge0\) and \(v\in L^q\) for every finite \(q\ge1\).
The missing full-height theorem would determine convergence of these
conditional horizontal variances modulo constants.

## What a vanishing third correction does and does not say

A Haar component of \(\nu\) is invisible because \(\int D^2f\,d\theta=0\).
If all third phase corrections vanish, uniqueness of Fourier transforms
and \(u_h\ne0\) for every nonzero prime vector show only
\(\nu=c\,d\theta\). They do not force \(c=0\).
RH gives \(b_\rho=0\), hence \(\nu=0\), but vanishing of the third
phase correction does not conversely prove RH. In particular, a
constant positive conditional horizontal variance is invisible here.

The task concerns the Fourier expansion of phase test functions and
zero-sampling functionals. It neither proves that zeta ordinates are a
Fourier basis nor supplies a CRT on the zero ordinates.

## Formalization ledger and sources

Checked declarations in this development include:

- CoshTaylorRemainder: exact positive Taylor tail, all-order frequency
  scaling, and the explicit quadratic head.
- ActualZeroHorizontalRemainder: actual multiplicity-weighted moments,
  exact signed finite-head identity, all-order density transfer,
  explicit quartic bound, and finite Fourier synthesis in the growing band.
- LogarithmicRemainder: inverse-cubic-log control implies a negligible
  error on the third-coefficient scale.
- ActualRationalThirdCoefficient: uniform rational Landau
  inverse-cubic-log rate, normalized second-moment bound, and the
  necessary-and-sufficient third-coefficient reduction, and existence of
  a third-coefficient subsequence for each fixed rational mode.

**Open:** a checked provider of UniformSelbergDensity (1/4).
**Open:** full-height convergence of rescaled oscillatory horizontal
moments, or equivalently the corresponding third phase coefficient.
The sharp integral bound (5), global synthesis (8)--(9), and
measure-level compactness/refinement (10) are ordinary proofs in this note,
not claims of complete Lean verification.

Primary analytic sources:

1. K. Ford and A. Zaharescu, *On the distribution of imaginary parts of
   zeros of the Riemann zeta function*, Lemma 1 (uniform Landau formula),
   Lemma 2 (Selberg density), and (3.8) (comparison strategy):
   https://ford126.web.illinois.edu/wwwpapers/fz.pdf
2. K. Ford, X. Meng, and A. Zaharescu, *Simultaneous distribution of the
   fractional parts of Riemann zeta zeros*, Theorem 1, Corollary 1.1,
   and Lemma 2:
   https://www.ford126.web.illinois.edu/wwwpapers/FMZ.pdf

The existing project provides the uniform rational Landau estimate,
exact reflection, finite layer cake, and horizontal second-moment bound.

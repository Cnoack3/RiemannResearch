# Gaussian signed matrices and the single-zero detector

29 October 2026. Continuation of `LandauSingleZeroDetection20261028.md`.

**Analytic proof completed on paper (29 October 2026).** See
[GaussianActualZetaExplicitFormula20261029.md](GaussianActualZetaExplicitFormula20261029.md)
for the full contour proof, Gaussian Fourier normalization, absolute convergence,
actual multiplicity-weighted zero identity, and summability needed by localization.
This discharges the ordinary analytic identification, not its Lean formalization.
The all-height subexponential negative-part estimate remains open.

**Conclusion.** The complete prime–archimedean matrix has an unconditional signed exponential rate strictly below 1/4 at each fixed height. This is proved on paper by localization of the complete zero sum. An explicit published zero-free region makes the improvement quantitative. The rate remains at least the squared displacement of every hypothetical zero it permits, so it supplies no new zero exclusion. The stronger all-height subexponential negative-part estimate remains RH-equivalent.

The work supplies exact matrix entries, pole removal, constrained Schur formulas, 15 numerical cases including every prime power through 20,000,000 with an analytic omitted-tail envelope, and Lean-checked finite algebra and conditional infinite-series localization. The Gaussian Fourier integral, complete zeta explicit-formula instance, zero-count summability and published zero-location theorems are paper-level inputs, not newly Lean-certified providers.

The original detector requires vanishing at all other nearby zeros and additional boundary interpolation. The low-degree numerical constraints below impose only pole removal and P(i/4)=i. They explore the signed form and must not be called complete single-zero detectors.

## 1. Exact moments, including every prime power

Let R>0, tau real, w=t-tau, and

\[
F_R(u)=\frac{e^{-u^2/(4R)}}{\sqrt{4\pi R}},\qquad
G_k(R,u)=i^k\partial_u^kF_R(u).
\]

For the Fourier convention g(u)=(2pi)^(-1) integral h(t)e^(-itu)dt,

\[
\frac1{2\pi}\int_{\mathbb R}(t-\tau)^k
 e^{-R(t-\tau)^2}e^{-itu}\,dt=e^{-i\tau u}G_k(R,u).
\]

Using physicists' Hermite polynomials H_k,

\[
G_k(R,u)=\frac{(-i)^k}{(2\sqrt R)^k}
 H_k\!\left(\frac{u}{2\sqrt R}\right)F_R(u).
\]

An alternative finite formula, convenient for exact rational coefficients, is

\[
G_k(R,u)=F_R(u)k!\sum_{j=0}^{\lfloor k/2\rfloor}
 \frac{1}{j!(k-2j)!}\left(\frac1{4R}\right)^j
 \left(\frac{-iu}{2R}\right)^{k-2j}.
\]

Thus

\[
G_0=F_R,\quad G_1=-\frac{iu}{2R}F_R,\quad
G_2=\left(\frac1{2R}-\frac{u^2}{4R^2}\right)F_R,
\]
\[
G_3=i\left(\frac{u^3}{8R^3}-\frac{3u}{4R^2}\right)F_R,\qquad
G_4=\left(\frac{u^4}{16R^4}-\frac{3u^2}{4R^3}
 +\frac3{4R^2}\right)F_R.
\]

Put K(t)=Re psi(1/4+it/2)-log pi. Define the complete arithmetic moments

\[
A_k=\frac1{2\pi}\int_{\mathbb R}w^ke^{-Rw^2}K(t)\,dt,
\]
\[
\Pi_k=2\sum_{p\ {
m prime}}\sum_{\ell\ge1}
 \frac{\log p}{p^{\ell/2}}
 \Re\left[e^{-i\tau\ell\log p}G_k(R,\ell\log p)\right],
\qquad \mu_k=A_k-\Pi_k.
\]

No prime power is discarded. Absolute convergence holds for each fixed R,
because exp(-(log n)^2/(4R)) dominates every fixed power of log n and every
fixed power of n. The archimedean integral is absolutely convergent as well.

For P(w)=sum_(j=0)^d c_j w^j, the arithmetic Hankel matrix is

\[
M_d(R,\tau)_{jk}=\mu_{j+k},\qquad
c^\mathsf T M_dc=\mathcal A_R(P)-\mathcal P_R(P).
\]

Before imposing pole removal, the zero-side matrix is M_d+E_d, where

\[
(E_d)_{jk}=2\Re\left[(-\tau+i/2)^{j+k}
 e^{-R(-\tau+i/2)^2}\right].
\]

In particular M_d itself need not be positive even under RH when the pole
conditions have not been imposed. Testing its unrestricted eigenvalues as an
RH criterion would be an error.

## 2. Pole removal by a stable polynomial basis

For real P the pole constraints are exactly

\[
P(-\tau+i/2)=0
\iff P(w)=D_\tau(w)S(w),\qquad
D_\tau(w)=(w+\tau)^2+\tfrac14.
\]

For d>=2 use q_j(w)=D_tau(w)w^j, j=0,...,d-2. Let r=d-2 and k=r+1=d-1.
The coefficient map T has columns with three consecutive nonzero entries
(tau^2+1/4,2tau,1). Then the exact constrained matrix is

\[
\mathcal K_d=T^\mathsf T M_dT,
\]

with explicit entries

\[
(\mathcal K_d)_{ij}=\mu_{i+j+4}+4\tau\mu_{i+j+3}
 +(6\tau^2+\tfrac12)\mu_{i+j+2}
 +(4\tau^3+\tau)\mu_{i+j+1}
 +(\tau^2+\tfrac14)^2\mu_{i+j}.
\]

This basis enforces pole removal algebraically; numerical cancellation of two
large pole terms is unnecessary. Its Euclidean coefficient norm is the norm
used in all bounds below. Spectra change under a nonorthogonal basis change,
although inertia and positivity do not. Generalized eigenvalues against a
specified positive Gram matrix are preferable for comparisons across bases.

Writing z_rho=(rho-1/2)/i and w_rho=z_rho-tau, the exact zero-side identity is

\[
(\mathcal K_d)_{ij}=\sum_\rho q_i(w_\rho)q_j(w_\rho)e^{-Rw_\rho^2}.
\tag{1}
\]

Zeros and multiplicities are all retained. Complex conjugate spectral points
make (1) real symmetric. It is a symmetric bilinear square, not an absolute
square off the real spectral axis.

## 3. Pair contributions and constrained Schur complements

For a conjugate pair w=eta+i delta and conjugate w, put

\[
v_j=q_j(w)e^{-Rw^2/2}=u_j+i v'_j.
\]

If the multiplicity is m at each point, its matrix contribution is exactly

\[
2m\Re(vv^\mathsf T)=2m(uu^\mathsf T-v'v'^\mathsf T).
\]

Let alpha=||u||^2, beta=||v'||^2, and gamma=u dot v'. The two possibly nonzero
eigenvalues are

\[
m\left[\alpha-\beta\pm\sqrt{(\alpha+\beta)^2-4\gamma^2}\right].
\]

The remaining eigenvalues vanish. If k>=2 and delta!=0, the q_0,q_1 ratio is
w, which is nonreal; thus u and v' are linearly independent, and exactly one
of these eigenvalues is negative and one positive. D_tau(w) is nonzero at a
nontrivial zeta zero. Other zero contributions can mask that negative direction;
the interpolation detector is what removes them locally.

For additional real affine interpolation constraints Bx=b, choose one solution
x0 and a matrix Z spanning ker B. Write H=Z^T K Z and g=Z^T K x0. Then

\[
(x_0+Zy)^\mathsf T K(x_0+Zy)
=x_0^\mathsf T Kx_0+2g^\mathsf Ty+y^\mathsf THy.
\]

If H is positive definite, the exact constrained minimum is

\[
x_0^\mathsf T Kx_0-g^\mathsf TH^{-1}g.
\]

If H is positive semidefinite singular, replace the inverse by its pseudoinverse
only when g lies in its range; otherwise the infimum is negative infinity. If
H has a negative eigenvalue, the infimum is also negative infinity. These checks
must precede interpretation of any Schur complement.

## 4. A genuine unconditional signed improvement below exponent 1/4

Write w_rho=eta_rho+i delta_rho, where eta=gamma-tau and
delta=1/2-beta. Define

\[
\theta_\rho=\delta_\rho^2-\eta_\rho^2,\qquad
W_{d,\tau}(w)=|D_\tau(w)|^2\sum_{j=0}^{d-2}|w|^{2j},
\]
\[
C_{d,\tau}=\sum_\rho W_{d,\tau}(w_\rho)e^{\theta_\rho}<\infty.
\]

Finiteness follows from the strict critical strip and the ordinary zero-count
bound N(U)=O(U log(U+2)); W has fixed polynomial growth while e^theta has
Gaussian decay in gamma. For real x, Cauchy--Schwarz gives

\[
|\sum_jx_jq_j(w)|^2\le\|x\|_2^2 W_{d,\tau}(w).
\]

Consequently, if theta_rho<=eta for every zero, then for R>=1,

\[
|x^\mathsf T\mathcal K_d(R,\tau)x|
\le C_{d,\tau}e^{\eta(R-1)}\|x\|_2^2,
\qquad
\|\mathcal K_d(R,\tau)\|_{\rm op}
\le C_{d,\tau}e^{\eta(R-1)}.
\tag{2}
\]

For each fixed tau one can unconditionally take

\[
\eta_\tau=\max(0,\sup_\rho\theta_\rho)<\tfrac14.
\]

Indeed outside |gamma-tau|<=1, theta<-3/4; inside that window there are only
finitely many distinct zeros, each with delta^2<1/4. The maximum of their
theta-values is strictly below 1/4. The empty-window case is immediate.

Thus the complete signed arithmetic matrix does have strictly smaller
exponential rate than the exp(R/4) absolute prime envelope at every fixed
tau. This result is a consequence of the complete explicit formula and strict
critical strip, not an independent arithmetic positivity theorem. A hypothetical
target at gamma=tau and displacement a forces eta_tau>=a^2, so (2) cannot
contradict the target signal.

### Explicit rate from an established zero-free region

For tau>=3, Mossinghoff--Trudgian--Yang's published zero-free region implies

\[
|\beta-\tfrac12|<b_\tau:=\tfrac12-
 \frac{1}{5.558691\log(\tau+1)}
\]

for every zero with |gamma-tau|<=1. Here gamma>=2 and gamma<=tau+1, so their
|gamma|>=2 hypothesis is met; functional-equation symmetry supplies the lower
boundary for beta. Since b_tau>0 and outside the local window theta<=-3/4,
one may take eta=b_tau^2 in (2). This is explicit and strictly less than 1/4.
For tau<=-3 use symmetry and |tau| in place of tau. Small |tau| can use the
abstract compact-window argument or a certified local zero list.

Primary source: M. J. Mossinghoff, T. S. Trudgian, A. Yang,
*Explicit zero-free regions for the Riemann zeta-function*, Theorem 1.3,
https://arxiv.org/abs/2212.06867 and DOI 10.1007/s40993-023-00498-y.
This is a safe established input, not a claim to use the latest available
constant. The new inequality here is a direct consequence for the Gaussian
matrix. It does not improve the zero-free region itself.

## 5. Local criticality yields a much stronger lower spectral bound

Suppose every zero with |gamma-tau|<=L is critical, where L>1/2. Its matrix
contribution is positive semidefinite. For every remaining zero,

\[
\theta_\rho\le\tfrac14-L^2=-\kappa,\qquad\kappa=L^2-\tfrac14>0.
\]

Let C_tail be the same convergent sum defining C_(d,tau), restricted to
|gamma-tau|>L. Keeping the local matrix positive and bounding only the tail gives

\[
\boxed{\mathcal K_d(R,\tau)\succeq
 -C_{\rm tail}e^{-\kappa(R-1)}I\quad(R\ge1).}
\tag{3}
\]

If all zeros with |gamma|<=T are critical and |tau|<T-1/2, take
L=T-|tau|. This makes (3) an unconditional estimate at heights covered by a
rigorous finite verification. Platt--Trudgian proved criticality of every zero
with 0<gamma<=3*10^12 using interval arithmetic; conjugation covers negative
heights. This theorem is external paper input and is not automatically a
Lean theorem in this project.

Primary source: D. Platt, T. Trudgian, *The Riemann hypothesis is true up to
3*10^12*, https://arxiv.org/abs/2004.09765, DOI 10.1112/blms.12460.

For low-height experiments, near-positivity with an extremely small permitted
negative tail is therefore expected unconditionally. It does not test unknown
high-height criticality. At a hypothetical off-line target, the premise of (3)
would fail for every local window containing that target.

### Eventual strict positivity at a fixed degree

The same argument can certify strict positivity when the verified local window
contains k=d-1 distinct critical ordinates gamma_1,...,gamma_k satisfying

\[
s:=\max_j|\gamma_j-\tau|^2<\kappa.
\]

Let v_j=(q_i(gamma_j-tau))_(i=0)^(k-1), and let
lambda0=lambda_min(sum_j v_j v_j^T)>0. Positivity follows because D_tau at real
arguments is positive and the evaluation matrix is Vandermonde at k distinct
points. With multiplicities at least one, their positive contribution is at
least lambda0 exp(-Rs) I. Therefore

\[
\lambda_{\min}(\mathcal K_d)
\ge\lambda_0e^{-Rs}-C_{\rm tail}e^{-\kappa(R-1)}>0
\]

for all sufficiently large R, since kappa>s. This is a finite-degree, locally
certified result. Taking degree to infinity is not justified: the number of
available certified nodes is finite and lambda0 can become extremely small.

## 6. What remains RH-equivalent

For all d>=2, all tau>0 and all R>=1, exact nonnegativity of these pole-restricted matrices
is equivalent to RH by the memorandum's interpolation construction. The weaker
assertion that for every d,tau,epsilon>0 their negative eigenvalue parts are
O_(d,tau,epsilon)(exp(epsilon R)) is also RH-equivalent. Under RH every summand
in (1) is positive semidefinite. Conversely, the fixed-degree detector P for
any hypothetical pair yields -2m exp(a^2 R)+O(exp(-3R/4)); choosing epsilon<a^2
contradicts that lower bound.

The unconditional statements (2) and (3) are genuine improvements on the
absolute arithmetic exponent, but they encode already known spectral location
information. They supply no rate below a^2 for a hypothetical allowed target.
The missing new input is an arithmetic signed estimate whose rate excludes
previously allowed zero locations, uniformly over the required detector family.

## 7. Archimedean asymptotics and what the prime sum must cancel

The archimedean kernel K(t) is smooth on the real axis. If
P(w)=p_ell w^ell+O(w^(ell+1)) with p_ell!=0, Gaussian scaling and Taylor
expansion give

\[
\mathcal A_R(P)=\frac{K(\tau)p_\ell^2}{2\pi}
 \Gamma(\ell+\tfrac12)R^{-\ell-1/2}
 +O_{P,\tau}(R^{-\ell-3/2}).
\]

Odd terms integrate to zero. If K(tau)=0, the displayed leading coefficient
vanishes and later Taylor terms determine the first nonzero term.

At a certified isolated critical ordinate tau=gamma_0 of multiplicity m, with
a sufficiently wide locally critical window, the complete zero sum satisfies
Q_R(P)=mP(0)^2+O(exp(-cR)) for some c>0. Therefore the complete prime sum is
Pi_R=A_R-mP(0)^2+O(exp(-cR)). At an ordinate tau separated from all local
critical zeros and with such a window, Q_R(P)=O(exp(-cR)), so Pi_R agrees with
A_R to every algebraic order in 1/R. These are actual signed cancellations,
but their proof uses already known local criticality and the complete formula.
At a hypothetical interpolated off-line target, Pi_R instead contains the
positive term 2m exp(a^2 R) dictated by the negative zero contribution.

## 7. Archimedean asymptotics and what actually cancels

For a fixed polynomial P with first nonzero term p_l w^l and fixed tau, Gaussian scaling gives

\[
\mathcal A_R(P)=\frac{K(\tau)}{2\pi}p_l^2\Gamma(l+1/2)R^{-l-1/2}+O_{P,\tau}(R^{-l-3/2}).
\]

The displayed leading coefficient may vanish if K(tau)=0. This follows by Taylor expansion of the smooth real archimedean kernel and parity of Gaussian moments; Gaussian tails control the remainder.

If a critical local window of radius greater than 1/2 contains no zero at tau, the complete zero side decays exponentially at a rate determined by the nearest local zero and the remote-tail gap. Thus the complete signed prime sum matches the archimedean expansion to every algebraic order. If tau is a certified critical ordinate of multiplicity m, then Q_R tends to m P(0)^2 and the complete prime sum tends to -m P(0)^2. For the hypothetical interpolated off-line pair, it instead carries the growing term +2m exp(a^2 R). The complete explicit formula accommodates all these behaviors; no contradiction follows from cancellation alone.

The theoretical operator bounds above use the fixed monomial pole basis. The numerical generalized eigenvalues below use the Gaussian L2 Gram norm, which depends on R. At fixed degree this change can introduce polynomial factors in R and conditioning losses; the exponential-rate comparison is unaffected, but numerical eigenvalues and the fixed-coordinate bound must not be equated without the Gram conversion.

## 8. Numerical calculations and truncation control

All calculations use the prime–archimedean explicit-formula side. Every prime power up to N=20,000,000 is included (1,271,339 prime powers; 1,270,607 distinct primes). No zero sum replaces the prime sum. The full infinite sum is represented by this truncation and an analytic entrywise tail envelope. All reported numbers, quadrature estimates and eigensystems use ordinary floating point, not validated interval arithmetic.

The pole-free basis is p_j(x)=q_tau(x) H_j(sqrt(R)x)/sqrt(2^j j!), q_tau(x)=((x+tau)^2+1/4)/(tau^2+1/4), j=0,1,2. Thus polynomial degrees 2,3,4 correspond to leading principal blocks of the reported 3 by 3 matrix. Generalized eigenvalues use the exact Gaussian L2 Gram matrix G; they describe W M W with W=G^(-1/2), avoiding arbitrary monomial scaling.

### Degree 4 at the midpoint tau=17.578382390253125

| R | Generalized eigenvalues | Prime-tail operator envelope | abs-prime envelope |
|---:|---|---:|---:|
| 0.25 | 2.031637e-05, 0.1426875, 0.3888318 | 1.69e-113 | 1.8917 |
| 0.5 | 2.555352e-11, 0.0191481, 0.1422196 | 4.18e-53 | 3.104 |
| 1 | 3.079972e-16, 0.0001377904, 0.002427715 | 3.55e-23 | 5.9856 |
| 2 | -1.961291e-13, 2.693482e-09, 1.036094e-07 | 2.22e-08 | 14.947 |
| 4 | -0.0006191682, 1.205783e-07, 9.779447e-05 | 0.463 | 57.544 |

The positive eigenvalues visible for R=.25 and .5 are numerical observations. Eigenvalues around 1e-16 are unresolved roundoff. At R=2 the prime-tail envelope already dominates the smallest eigenvalues. At R=4 the apparent negative eigenvalue is smaller than the tail envelope by hundreds of times and gives no evidence of a negative complete form. The archimedean quadrature error estimates in these cases are around 1e-12 in whitened norm, but are heuristic estimates, not rigorous error certificates.

### Low degrees and affine interpolation

The affine constraints are only pole removal and P(i a)=i with a=1/4. They do not include the memorandum’s annihilation of all competing nearby zeros or its extra boundary conditions. Degree 2 is infeasible for these constraints; degree 3 is typically a unique vector; degree 4 has one free direction. The JSON records q0, b, H in q(y)=q0+2by+Hy² and q0-b²/H. A stationary Schur value is called a minimum only conditionally on H>0. Prime-tail-only Schur intervals are included where the lower bound on H is positive; they do not include quadrature or rounding error.

| R | degree 2 eigenvalue | degree 3 eigenvalues | degree 4 stationary Schur value |
|---:|---:|---|---:|
| 0.25 | 0.0344922 | 0.02142841, 0.1903729 | 13.58049 |
| 0.5 | 0.002563861 | 0.001519498, 0.0293079 | 0.7003973 |
| 1 | 9.737997e-06 | 5.632168e-06, 0.0002267139 | 0.001863134 |
| 2 | 9.788946e-11 | 5.596409e-11, 4.603964e-09 | 1.317499e-08 |
| 4 | -9.801522e-07 | -3.029501e-06, 3.602488e-05 | 0.0002131239 |

At tau=14.134725141734695 the largest generalized eigenvalue grows approximately as sqrt(R), and the other two collapse to numerical zero: this is consistent with Gaussian concentration on the first tabulated on-line zero. It is not a completeness assertion about the zeros. At tau=0 and R<=1, the tiny residual entries are limited by quadrature and rounding; at R=2 and R=4, prime truncation dominates (largest residual entries approximately 2.0e-6 and 1.57). The first ten tabulated on-line zeros are used only as a diagnostic: their matrix agrees to approximately 1e-15 for R<=1 at the positive-height centers, and within 1.3e-12 across all tested centers including tau=0. At R>=2, the independently bounded prime truncation error becomes visible.

### Analytic prime-tail envelope

For a product polynomial b(x)=sum_k b_k x^k, set D_0(u)=1, D_(k+1)=D_k'(u)-u D_k(u)/(2R), and C_b(u)=sum_k b_k i^k D_k(u)=sum_j a_j u^j. Its Fourier transform is sqrt(pi/R) exp(-i tau u-u²/(4R)) C_b(u). The tail after N has absolute value at most

    sqrt(pi/R)/pi * sum_j |a_j| I_(j+1)(R,log N),

where I_p(R,L)=integral_L^infinity y^p exp(y/2-y²/(4R))dy. The bound uses Lambda(n)<=log n and the integral test, valid when L>(-R+sqrt(R²+8R(j+1)))/2 for each coefficient. For L>=R, let z=(L-R)/(2sqrt(R)); then

    I_p=e^(R/4) 2sqrt(R) sum_(l=0)^p binom(p,l) R^(p-l) (2sqrt(R))^l * Gamma((l+1)/2,z²)/2.

The code verifies the monotonicity threshold. Thus increasing R without increasing N does not produce trustworthy smaller signed eigenvalues. The exp(R/4) factor belongs to the absolute tail envelope, while the signed computed matrices show substantial cancellation in the resolvable regime.

### Interpretation

These computations demonstrate numerical cancellation and identify conditioning/truncation barriers. They supply no unconditional asymptotic lower bound for the complete signed form. In particular they neither prove nonnegativity for all admissible tests nor improve the exp(R/4) exponent uniformly. The apparent R=4 negative eigenvalues are fully compatible with the explicit truncation error bounds.

Run: python3 numerics/gaussian_signed_matrices.py --N 20000000 --out numerics/results.json; then python3 numerics/summarize_results.py. Dependencies: NumPy, SciPy, Matplotlib.

### One explicit reduced matrix

For R=1/4 and tau=17.578382390253125, in the normalized pole/Hermite basis specified above, the following are the directly computed archimedean, truncated prime, and signed matrices (not interval certificates):

A:

```text
[0.615857814592, 0.239455264238, 0.0505155695355]
[0.239455264238, 0.68729761814, 0.349171211617]
[0.0505155695355, 0.349171211617, 0.75961771991]
```

P_truncated:

```text
[0.488828782544, 0.0352236276296, -0.392320387108]
[0.0352236276296, -0.0659960297003, -0.363031054801]
[-0.392320387108, -0.363031054801, -0.785121124031]
```

M_truncated:

```text
[0.127029032048, 0.204231636608, 0.442835956644]
[0.204231636608, 0.75329364784, 0.712202266418]
[0.442835956644, 0.712202266418, 1.54473884394]
```

gaussian_gram:

```text
[3.68283360953, 1.1619707176, 0.195685736289]
[1.1619707176, 3.95957503175, 1.67455044423]
[0.195685736289, 1.67455044423, 4.23809566754]
```

## 9. Lean verification boundary and reusable declarations

Two new modules accompany this memorandum:

- `Analysis/GaussianSignedMatrixAlgebra.lean`: `polynomialFunctional_square` identifies an arbitrary real linear functional of a polynomial square with its Hankel quadratic form. `poleReduced_quadratic` proves the complete five-term pole-factor reduction. `quadratic_signed`, `affine_completion`, `affine_lower_bound`, `quadratic_entrywise_lower` and `nonnegative_plus_entrywise_lower` retain the signed terms, Schur remainder and error budget. Positive semidefiniteness is an explicit hypothesis where needed.
- `Analysis/GaussianLocalization.lean`: `weighted_exp_factor_bound`, `norm_tsum_le_exp_rate`, `nonnegative_head_add_tsum_lower`, `gaussian_gap_exponent` and `exponent_below_quarter` prove the summable Gaussian localization and signed lower bound from stated hypotheses. The actual-zero summability, strip/zero-free bounds, and positive local core are not silently discharged.

The combined source passed an isolated server check with exit code 0 (job `job_cmnG3atZWwF6tnhZVVUqZQkc7F0d9NgZ`, reported verification time 5.483 seconds). The final repository publication is separately gated by a server checkpoint. An isolated check does not certify the entire repository or the paper-level analytic adapters.

Existing relevant work was inspected rather than reproved: `HankelMomentPositivity.lean` for finite Hankel positivity, `GaussianHankelInterpolation.lean` for conjugation-respecting interpolation and negative witnesses, `GaussianHankelTailBridge.lean` for conditional growing-degree tails, and `FiniteConstrainedMatrixReparametrization.lean` for the exact congruence identity under coefficient changes. In particular, that last module's `reparam_quadratic` already supplies the general T-transpose M T equality.

Wolfram symbolically confirmed the Gaussian Fourier polynomials through degree 6 and the pole-factor square. Independent numerical integration checked 27 monomial Fourier transforms (degrees 0 through 8 at three frequencies), with maximum absolute discrepancy 1.70e-13. These checks validate implementation conventions, not infinite-dimensional positivity.

### Open obligations

1. Formalize the Gaussian explicit-formula functional on real polynomials and connect its analytic Fourier/prime/archimedean definitions to the checked matrix algebra.
2. Supply the actual full-zero summability and localization hypotheses to the checked infinite-series theorem, including multiplicities.
3. Use directed-rounding quadrature, prime summation and interval eigensystem bounds if certified numerical matrix positivity is wanted. Current tail formulas are analytic bounds evaluated in ordinary floating point.
4. Obtain an independent signed arithmetic lower estimate that excludes a previously allowed zero location. Reusing a zero-free region in the zero-side bound cannot improve that same region.
5. A proof of the all-height, all-degree subexponential negative-part estimate would prove RH; it remains Open.

No Riemann Hypothesis proof or new zero-free region is claimed.

## Sources

- Repository memorandum: https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/LandauSingleZeroDetection20261028.md (detector and open arithmetic target).
- A. Bondarenko, D. Radchenko, K. Seip, *Fourier interpolation with zeros of zeta and L-functions*, equation (1.1): https://arxiv.org/abs/2005.02996 ; https://doi.org/10.1007/s00365-022-09599-w (complete explicit formula and admissible test class).
- M. J. Mossinghoff, T. S. Trudgian, A. Yang, *Explicit zero-free regions for the Riemann zeta-function*: https://arxiv.org/abs/2212.06867 (published classical zero-free constant used here).
- D. Platt, T. Trudgian, *The Riemann hypothesis is true up to 3·10^12*: https://arxiv.org/abs/2004.09765 (rigorous finite-height verification, used as external paper input).
- J.-F. Burnol, *The Explicit Formula in simple terms*: https://arxiv.org/abs/math/9810169 (classical positivity/interpolation context).

# Infinite arithmetic DPPs and the sine-kernel limit

## Status

This continuation separates the integer-site process, an auxiliary process made
from nonzero residue classes, the legal Ramanujan Mellin sampling process, and
the deterministic zeta-zero sequence.

New Lean modules:
- `RH/IntegerDPPLawLimit.lean`: convergence of finite inclusion probabilities,
  finite-hole probabilities, and multivariate finite-window generating functions.
- `RH/ParetoResidueSineLimit.lean`: exact phase cancellation in every finite
  determinant; a moving-frequency determinant limit with explicit error
  hypotheses; an unconditional fixed-center microscopic determinant limit.
- `RH/ParetoResidueFrequencyKernel.lean`: the exact feature-sum kernel and
  normalization connecting the nonzero residue partition to the grouped Gram.

The auxiliary process construction and weak convergence described below are
mathematical deductions using Mellin--Plancherel and the published DPP convergence
theorem. They are not claimed as a completed Lean formalization of a continuous
infinite point process. The finite-k Gram limit and the displayed algebraic
kernel identities are the Lean results.

## 1. The infinite integer law

Let V_n be the legal conductor-prefix spaces in the counting realization of
the complete Pareto Hilbert space, and V their closed union. The existing
definitions give
```
integerKernel n i j = <P_{V_n} e_i, P_{V_n} e_j>
limitingKernel i j = <P_V e_i, P_V e_j>.
```
The existing `integerKernel_tendsto` and `limitingLaw_isDPP` prove entrywise
kernel convergence and the existence of the limiting countable DPP without RH.

The new results take the actual finite laws to the actual limiting law for all
finite inclusion events, all finite-hole events, and all multivariate window
generating functions. Finite-dimensional convergence follows by finite
inclusion-exclusion. On the compact product {0,1}^N this determines the usual
weak limit. The latter packaging is a mathematical consequence, not an
additional Lean declaration in this change.

For a finite window A, the limiting hole probability is det(I-K_A). The
complement process has kernel I-P_V. Negative association and monotone
couplings for nested projection spaces are available from Lyons [1]; the
repository's construction of a full spatial coupling still retains its
finite-transport obligation. The new law-limit statements do not need it.

## 2. A genuine auxiliary sine-process limit

Put L=N+1>1 and ell=log L. For 1<=r<L set
```
w_L(r) = sum_{n>=1, n mod L=r} 1/[n(n+1)],
b_{L,r}(n) = 1_{n mod L=r}/sqrt(w_L(r)), n>=1.
```
Set the anchor value to zero. These are bounded orthonormal vectors of the
complete Pareto Hilbert space. The multiples class is excluded; this matches
the existing `classCrossSum` exactly.

Write s_t=1/2+it. Their Mellin transforms are
```
Phi_{L,r}(t)
 = [sum_{k>=0} ((r+kL)^(-s_t)-(r+kL+1)^(-s_t))]
   / [s_t sqrt(w_L(r))].
```
Mellin--Plancherel makes these an orthonormal family for dt/(2 pi).
Consequently the rank-(L-1) kernel
```
Q_L(t,u) = sum_{r=1}^{L-1} Phi_{L,r}(t) conjugate(Phi_{L,r}(u))
```
defines a finite projection DPP by the standard orthonormal-feature
construction [2]. The existing grouped numerator is therefore
```
classCrossSum(t,u,N) = s_t conjugate(s_u) Q_L(t,u),
phaseStrippedCross(t,u,N) = Q_L(t,u)/ell.
```
The new frequency-kernel module formalizes these algebraic equalities.

Fix any real t0 and rescale sampled frequencies by
```
x = ell (t-t0)/(2 pi).
```
Since dt/(2 pi)=dx/ell, the kernel relative to dx becomes
```
Qtilde_L(x,y)
 = Q_L(t0+2 pi x/ell, t0+2 pi y/ell)/ell
 -> exp(-i pi(x-y)) sin(pi(x-y))/(pi(x-y)).
```
The existing quantitative Gram bound is uniform for x,y in each fixed compact
set: its error budget is continuous and bounded there, and is divided by ell.
Thus the convergence is locally uniform, including the diagonal.

The phase is a unitary gauge. Every fixed-k determinant has the exact limit
```
det[S(x_i-x_j)]_{i,j=1}^k,
S(h)=sin(pi h)/(pi h), S(0)=1.
```
The new `phaseStrippedCross_det_fixedCenter_tendsto` proves this for any fixed
finite index type and every cofinal period sequence, with no RH or zero premise.

Here S(x-y) is the Fourier projection kernel for the band [-1/2,1/2].
The local trace convergence follows from the diagonal convergence. Together
with bounded projection operators and convergence on compactly supported
test functions, this gives the weak-operator and local-trace hypotheses of
Soshnikov [3, Theorem 5]. Hence the rescaled auxiliary residue-partition DPP
converges to the stationary sine process: the GUE/CUE bulk limit.

Without rescaling, its intensity is ell/(2 pi)+O_I(1) on each fixed bounded
frequency window I. Its mean count on I grows like |I| ell/(2 pi), and the
DPP count variance is at most its mean. Thus counts on positive-length bounded
intervals tend to infinity in probability. There is no locally finite
unscaled limit for this auxiliary family.

## 3. What structure this supplies

For the limiting auxiliary process:
- Unit density and a band-limited Fourier projection (free-fermion structure).
- Pair intensity 1-S(h)^2 = pi^2 h^2/3 + O(h^4): quadratic repulsion.
- Number variance on an interval of length R grows as (1/pi^2) log R.
  See [3, Section 3, equation (3.15)].
- Interval gaps are Fredholm determinants det(I-S_I); see [4].
- Counts in bounded regions are sums of independent Bernoulli variables with
  the compressed-kernel eigenvalues; diverging variance yields Gaussian
  count fluctuations [2, Theorems 7 and 24].

Wolfram independently checked the phase identity, a symbolic 3x3 determinant
cancellation, the Fourier-band integral, and the expansion
1-S(h)^2 = pi^2 h^2/3 - 2 pi^4 h^4/45 + pi^6 h^6/315 + O(h^8).
These checks are not the proof of the infinite-process assertion.

## 4. A reduced-Palm comparison at an actual critical zero

The following is a mathematical deduction from the finite projection geometry;
its full specialization to the legal frequency kernel is not formalized in
these new modules.

Let A_L be the Mellin projection kernel of the full-divisor legal space and
let gamma be a fixed actual critical-line zero. Every legal Mellin feature
vanishes at gamma. Since the legal space is contained in the nonzero
residue-partition space, the evaluation vector at gamma is orthogonal to it.
Whenever Q_L(gamma,gamma)>0, orthogonal projection order gives the exact
positive-semidefinite kernel comparison
```
A_L <= Q_L^gamma,
Q_L^gamma(t,u)
 = Q_L(t,u) - Q_L(t,gamma) Q_L(gamma,u)/Q_L(gamma,gamma).
```
This is the familiar reduced-Palm projection kernel [6]. The positivity of
its denominator holds for all sufficiently large L by the proved diagonal
Gram limit.

At the microscopic scale centered at gamma, the upper comparison kernel,
after removing the phase, converges to
```
S^0(x,y) = S(x-y) - S(x) S(y).
```
Consequently the normalized legal diagonal satisfies
```
limsup_{L->infty} A_L(gamma+2 pi x/log L,
                    gamma+2 pi x/log L) / log L <= 1-S(x)^2.
```
This is an upper comparison, not an equality or a proof that the legal process
converges to the reduced-Palm sine process. It explains why a window pinned at
a known zero has a natural density depression rather than stationary unit
sine intensity. A sufficient transfer condition would be vanishing local trace
of Q_L^gamma-A_L after the same rescaling. That quantitative condition is OPEN.

## 5. Why this does not settle the legal Mellin DPP or RH

The auxiliary space contains all nonzero residue-class indicators, of
dimension L-1. The full-divisor legal space has dimension tau(L)-1 and lies
inside that space. The indicators are generally not legal conductor
combinations. Replacing the legal space by the larger partition space changes
the problem: the latter already approximates the constant by deleting only
the multiples class, whose complete Pareto mass tends to zero.

The legal Mellin sampling kernel is the packet inverse-Gram kernel with the
zeta envelope. No theorem above identifies it with Q_L or proves that its
rescaled kernel has the same limit. A vanishing local trace difference could transfer the auxiliary sine limit
at centers away from prescribed zeros; establishing such an estimate is OPEN.
At a window pinned to an actual zero, that unconditioned transfer is impossible:
the Palm comparison leaves a limiting local trace deficit at least the integral
of S(x)^2 on the window. The appropriate comparison there is Q_L^gamma,
whose additional difference from the legal projection still requires a bound.

For actual zeta zeros near a height T, the customary unfolding uses
log T/(2 pi), not an arbitrary conductor-period logarithm [5].
Our present microscopic error budget contains positive multiples of
sqrt(9/4+t^2) and sqrt(9/4+u^2). At heights comparable to T it grows on the
order of T. Its vanishing-after-division-by-ell hypothesis therefore needs
T=o(ell). Matching the usual zero scale would require ell comparable to log T,
which is outside the scope of this bound. A sharper high-height estimate is
OPEN; this is a limitation of the current estimate, not a disproof of GUE.

The constant-target vacancy remains
```
E_M = ||1-P_{V_M}1||_P^2 -> ||1-P_V 1||_P^2.
```
For the full legal conductor program, proving that this limit is zero is still
the RH task. The auxiliary sine law alone supplies no bound forcing it to zero.

## References

[1] R. Lyons, Determinantal probability measures, Publ. Math. IHES 98 (2003),
167-212. https://arxiv.org/abs/math/0204325

[2] J. B. Hough, M. Krishnapur, Y. Peres, B. Virag, Determinantal Processes and
Independence, Probability Surveys 3 (2006), 206-229.
https://arxiv.org/abs/math/0503110

[3] A. Soshnikov, Determinantal random point fields, Russian Math. Surveys 55
(2000), 923-975. https://arxiv.org/abs/math/0002099

[4] H. Widom, Asymptotics for the Fredholm determinant of the sine kernel on a
union of intervals, Commun. Math. Phys. 171 (1995), 159-180.
https://arxiv.org/abs/hep-th/9405010

[5] J. Arias de Reyna and B. Rodgers, On convergence of points to limiting
processes, with an application to zeta zeros (2024 version), Section 5.1 and
Theorem 2. https://arxiv.org/abs/2311.13441

[6] J. Moller and E. O'Reilly, Couplings for determinantal point processes and
their reduced Palm distributions with a view to quantifying repulsiveness,
Section 2.1.3. https://arxiv.org/abs/1806.07347

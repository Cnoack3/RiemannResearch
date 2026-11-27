# Ingham's density bound for the actual zeta zeros

## Selberg slope two and the moving endpoint of the 61.7% paper

Let \(L=\log T\) and \(\sigma_0=1/2+1/(2L)\). In the arXiv version of Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh, Theorem 3 assumes a uniform little-\(o\) bound for the inclusive, multiplicity-weighted count starting at \(\sigma_0\). For scaled displacement \(d\), the exact comparison power is \(T^{2(1-(1/2+d/L))}=T e^{-2d}\). At \(d=1/2\) the power is \(T/e\).

- **Conditional research reduction.** Under the strip hypothesis with any fixed upper cutoff \(b>1/2\), the endpoint count is \(o(T/e)\), \(o(N(T)/L)\), and \(o(N(T)/e)\). The unconditional Riemann–von Mangoldt lower bound gives the changes of normalization. A signed pair remainder of size \(o(TL)\), as in the paper's (6.3) for Lemma 7, likewise has size \(o(N(T)/e)\). The latter declaration takes the pair-remainder estimate as its premise. [Endpoint identities and normalizations](Analysis/ActualBGSTBDensity.lean) · [Theorem 3 and Lemma 7](https://arxiv.org/abs/2306.04799)
- **Conditional research reduction.** With a fixed overlap \(b>25/32\), the short-strip hypothesis and the three named far-strip inputs imply uniform \(o(T^{2(1-\sigma)})\) through \(\sigma=1\). The total count on \([1/2,\sigma_0]\) then gives \(\mathrm{UniformSelbergDensity}(2)\) on the entire closed half strip, with one logarithm. **Open** as Lean providers are the moving-strip hypothesis, `TaoBourgainFarDensityHypothesis`, `HuxleyDensityHypothesis`, and `BellottiKorobovVinogradovCount`. [Far-strip proof](Analysis/ActualSelbergSlopeTwo.lean)
- **Conditional research reduction.** The thin box in Theorem 2 at all sufficiently large heights gives the full moving-strip estimate and slope two by itself. For \(\sigma_0\le\sigma\le3/4\) all contributing zeros have height at most \(T^{3/8}\). For \(\sigma\ge3/4\), testing the box at each zero's own height leaves a fixed finite head whose largest real part is strictly below one. **Open** is the thin-box hypothesis for actual zeros. [Thin-box proof](Analysis/ActualBGSTBThinBox.lean)

## Curved Ingham slopes and the one-logarithm Selberg transition

Write \(L=\log T\), \(\ell=\log L\), \(d=\sigma-1/2\), and \(r(d)=4d/(3-2d)\). Counts include each analytic zero occurrence with real part at least \(\sigma\). The actual density input is \(\ll T^{1-r(d)}L^{3-r(d)}\).

- `ingham_low_price`, `ingham_middle_price`, and `ingham_high_price` give the least intercept \(b\) for \(a d\le r(d)+b\) throughout \(0\le d\le1/2\). It is zero for \(a\le4/3\), \(3a/2+2-2\sqrt{3a}\) for \(4/3\le a\le3\), and \(a/2-1\) for \(a\ge3\). `exists_ingham_priced_density` retains the complete factor \(\exp((L+\ell)(b-ad))\).
- `eventually_ingham_substrip_one_log` gives \(N(1/2+d,T)\ll T^{1-ad}L\) on \(d_0\le d\le1/2\) for every fixed \(0<d_0\le1/2\) and \(a<4/(3-2d_0)\).
- `tendsto_tilted_moment_loglog_window` gives \(T^{-1}\sum_{\rho} |\beta-1/2|^{p+1}\exp(v_T|\beta-1/2|)\to0\) if \(p\ge7\), \(0\le c<(4/3)\sqrt{p-6}\), and eventually \(0\le v_T\le(4/3)L+c\sqrt{L\ell}\).
- `ingham_one_log_iff_transition_displacement` gives the exact comparison of the Ingham majorant with \(T^{1-ad}L\) at \(T>e,\ a>0\). The comparison holds precisely when \(2aLd^2+((4-3a)L+8\ell)d-6\ell\ge0\). `exists_actual_selberg_above_transition` transfers this to actual counts with an absolute constant. For any fixed \(M\), `uniformSelbergDensity_iff_exact_transition` reduces the global slope to the band \(M/L<d<d_T(a)\), where \(d_T(a)\) is the positive root.
- At the fixed abscissa \(\sigma=5/6\), `one_log_five_sixths_of_far_density` gives every \(a<21/10\) from the repository's `TaoBourgainFarDensityHypothesis`. The published table gives \(q=3/10\) there. **Open in Lean** is a provider for the fixed-abscissa literature estimate. [Zero-density exponent table](https://teorth.github.io/expdb/blueprint/zero-density-chapter.html)

- **Conditional research reduction.** `dyadic_one_log_curved_density` gives \(N(\sigma,T)\ll_\eta T^{\max(\eta,3(1-\sigma)/(2-\sigma))}L\) for every fixed \(\eta>0\). `dyadic_one_log_moving_selberg` yields the full-strip one-log slope \(4/3+c/\sqrt L\) with prefactor \(\exp(9c^2/32)\). `dyadic_one_log_priced_density` retains the exact height price and one logarithm wherever the resulting height exponent is at least a fixed positive number. `dyadic_one_log_tilted_moment_loglog` gives the same growing critical tilt for \(p\ge3\) and \(c<(4/3)\sqrt{p-2}\). **Open in Lean** is a provider for `DyadicInghamOneLog`. The dyadic case of rStation Paper 184, Theorem 1, supplies the written input. The detector and zero-free-cap formalizations keep their analytic hypotheses explicit. In the detector's Hölder step the exponents are 4 for the mollified zeta factor and 2 for the finite inverse on an actual dyadic height interval. To reach slope 3/2 by this same step, one sufficient replacement is a uniform sixth moment for the mollified factor. Another is a uniform moment of order 12/5 for the finite inverse together with the existing fourth moment. Either replacement must hold with the detector's coefficient-gap construction.

[Ingham slopes and moments](Analysis/ActualInghamSlopeFrontier.lean) · [Actual Selberg transition](Analysis/ActualSelbergCurvedFrontier.lean) · [Chourasiya and Simonič, Theorem 1](https://arxiv.org/abs/2507.15184) · [Dyadic fourth-moment input](https://rstation.ai/problems/riemann_hypothesis/papers/184/v1)

The declaration `RiemannResearch.Analysis.ActualZeroOrdinate.inghamDensityBound`
in [ActualInghamDensityBound.lean](Analysis/ActualInghamDensityBound.lean) proves
the uniform, inclusive, multiplicity-weighted statement
`ActualZeroOrdinate.InghamDensityBound`. Write
\[
  q(\sigma)=\frac{3(1-\sigma)}{2-\sigma}.
\]
The stronger declaration `exists_ingham_density_log_profile` supplies a single
constant and threshold, uniform for every real height above the threshold and
every \(1/2\le\sigma\le1\), such that
\[
  N(\sigma,T)\le C(T/\log T)^{q(\sigma)}(\log T)^5
  = C T^{q(\sigma)}(\log T)^{5-q(\sigma)} .
\]
The count includes every copy of a nontrivial zero with
\(0<\Im\rho\le T\) and \(\Re\rho\ge\sigma\). The theorem uses the actual
zeta function and its finite Möbius mollifier. All moment and zero-count
inputs in the proof have unconditional Lean declarations.

The declaration `exists_ingham_density_all_heights` absorbs the finite
initial range and combines the result with the total count. For every real
height \(T\ge2\) and every \(1/2\le\sigma\le1\), one positive constant gives
\[
  N(\sigma,T)\le C\min\{T\log T,\;T^{q(\sigma)}(\log T)^{5-q(\sigma)}\}.
\]
At \(\sigma=3/4\), the density term is \(T^{3/5}(\log T)^{22/5}\).

## Proof

Let \(F_X(s)=\zeta(s)\sum_{n\le X}\mu(n)n^{-s}-1\), \(X=\lceil T\rceil\),
\(d=1/\log X\), \(Y=T/\log T\), and
\(L=3\log Y/[2(2-\sigma)]\). At a zeta zero, \(F_X(\rho)=-1\).
The exact normalized, positively oriented rectangle integral of
\[
  F_X(s)\frac{\exp(L(s-1/2)+(s-\rho)^2)}{s-\rho}
\]
is \(-\exp(L(\rho-1/2))\). The vertical sides lie at \(1/2\) and \(1+d\);
the horizontal sides lie at heights 1 and \(2T\). The source identity
`cauchyDetector_rectangle` retains all four signed integrals.

1. The actual left endpoint is
   \(\int_0^{2T}|F_X(1/2+it)|^{4/3}\,dt\ll T(\log T)^2\).
   It follows from the zeta fourth moment and the mollifier second moment.
   The moving right endpoint in
   [ActualInghamRightMoment.lean](Analysis/ActualInghamRightMoment.lean)
   gives \(\int_1^{2T}|F_X(1+d+it)|^2\,dt\ll(\log T)^3\).
2. If \(r\ge d>0\), \(U\ge0\), and \(1\le p\le2\), splitting at
   \(U=d/r\) gives \(U/r\le U^p/d+d/r^2\).
   On a vertical edge the complement is bounded by the Poisson kernel
   \(d/(d^2+(t-\Im\rho)^2)\). Its interval integral is exactly an arctangent
   difference and is at most \(\pi\). Thus either endpoint moment costs
   just \(1/d\). The Gaussian factor supplies the common integrable weight
   \(1/(1+(t-\Im\rho)^2)\).
3. For \(1+4\log T<\Im\rho\le T\), Gaussian decay bounds each horizontal
   edge after normalization by \(1/8\). The low ordinates contribute
   \(O((\log T)^2)\) via the actual total zero count. If
   \(\sigma-1/2<d\), total counting alone suffices.
4. The local multiplicity bound makes the sum of the common weights over
   the zero copies at most \(C\log(T+3)\). The precise tilt identities are
   \[
     Ye^{(4/3)L(1/2-\sigma)}=Y^{q(\sigma)},\qquad
     e^{2L(1-\sigma)}=Y^{q(\sigma)}.
   \]
   The additional right-line shift costs a bounded factor since \(Ld\le2\).
   Including the moment, inverse separation, and local count, the left side
   contributes \(O(Te^{(4/3)L(1/2-\sigma)}(\log T)^4)\)
   and the right side contributes \(O(e^{2L(1-\sigma)}(\log T)^5)\).
   Both have the claimed order.

## Related estimates

The sharper Gabriel–Littlewood profile has logarithmic exponent at most
three. At distance $b=(3/2)\log\log T/\log T$, the exponential factor
absorbs the surplus two powers over the total-count scale. The squared
excess $(|\beta-1/2|-b)_+^2$ then sums to $O(T/\log T)$. Keeping the
actual Riemann–von Mangoldt leading count in the complementary bound
gives the unconditional estimate
\[
  \limsup_{T\to\infty}\frac{E(T)}{T(\log\log T)^2/\log T}
  \le \frac{9}{8\pi}.
\]
See `eventually_horizontalEnergy_ratio_le_ingham` in
[ActualZeroInghamHorizontalEnergy.lean](Analysis/ActualZeroInghamHorizontalEnergy.lean).

For the count-normalized moments, put \(X_\rho=\Re\rho-\tfrac12\),
\(M_k(T)=N(T)^{-1}\sum_{0<\Im\rho\le T}|X_\rho|^k\), and
\(s_T=\log\log T/\log T\). Counting the central strip only on its off-line
copies gives, for each fixed positive integer \(k\),
\[
   \limsup_{T\to\infty} M_k(T)/s_T^k \le (3/2)^k/3,
   \qquad M_k(T)\longrightarrow 0.
\]
In particular \(M_2=E(T)/N(T)\). The squared, cubed and fourth powers of
the per-copy energy \(X_\rho^2\) have respective means \(M_4,M_6,M_8\).
Reflection makes every signed odd moment vanish at finite height, even
with an arbitrary real ordinate weight. At order two, Riemann–von Mangoldt
converts the improved coefficient \(3/4\) into \(3/(8\pi)\) in the
preceding height normalization. The proof uses the checked Ingham envelope
and the checked two-thirds critical-line theorem. It retains the finite
Mellin tail identity and bounds the positive excess using Euler's gamma
integral. [Displacement moments](Analysis/ActualZeroDisplacementMoments.lean)

The joint empirical law of the ordinate modulo \(2\pi\) and \(X_\rho\)
converges to angular Haar measure pushed forward under \(t\mapsto(t,0)\).
The horizontal marginal converges weakly to \(\delta_0\).
The infinite prime-torus word-character law and each fixed Hilbert-orbit
pushforward now use this unconditional second-moment input. Their
former full-strip Selberg hypothesis has been discharged.
[Infinite prime torus](Analysis/ActualInfinitePrimeTorus.lean) · [Joint law and Lipschitz coupling](Analysis/ActualZeroAngleDisplacementLaw.lean)

For the zero-label DPP, give each selected label with inclusion probability
\(\pi_i\) the signed weight \(X_i|X_i|^p/\sqrt{\pi_i}\), and call its sum
\(H_p\). Reflection centres every ordinate fibre. For each dictionary and
cutoff, \(\mathbb E[H_p H_r]/N(T)=M_{p+r+2}(T)\). The weighted identity
allows moving bounded ordinate tests and gives both Fourier quadratures at
a difference frequency. [DPP moments](Analysis/ZeroDPPHorizontalVariance.lean)

**Conditional research reduction.** The classical single-logarithm
Selberg estimate gives \(M_k(T)\ll_k(\log T)^{-k}\).
The finite bound in Lean is
\(M_k(T)(a\log T)^k\le 2C\,T\log T\,k!/N(T)\).
The positive-exponent full-strip provider for the actual zeros remains
open in Lean. [Ford–Zaharescu, Lemma 2](https://arxiv.org/abs/math/0405459)

The away-line Selberg transfer in
[ActualSelbergIngham.lean](Analysis/ActualSelbergIngham.lean) now has its
Ingham hypothesis supplied. The unconditional corollary
`exists_selberg_far_windows_on_fixed_strip` gives a single logarithm for
all \(\sigma\ge1/2+\eta\) in the half strip and every fixed slope
\(a<4/(3-2\eta)\), with \(0<\eta\le1/2\). The separate near-line Conrey–Baluyot dyadic
mollified moment for lengths cofinal below \(T^{4/7}\) stays open in Z03.
The dyadic and Gaussian cofinal theorems in
[ActualConreyBaluyotDensity.lean](Analysis/ActualConreyBaluyotDensity.lean)
now take only their respective near-line moment input.
The preceding proof records the original three-logarithm endpoint. The following refinements use the sharp right-line moment.

[Chourasiya and Simonič](https://arxiv.org/abs/2507.15184) state the
classical Ingham bound and prove an explicit estimate with log exponent
\((7-5\sigma)/(2-\sigma)\). This source supports the analytic context and
the moment orders. The Lean proof above counts via individual Cauchy
rectangles and uses its own constants.

## Sharp right edge and Gabriel interpolation

Write \(F_X(s)=\zeta(s)M_X(s)-1\), where \(M_X(s)=\sum_{n\le X}\mu(n)n^{-s}\).
For each fixed \(\delta>0\), all integers \(X\ge2\), all real \(H\le T\), and
\(\beta=1+\delta/\log X\), the actual right-line error satisfies
\[
   \int_H^T |F_X(\beta+it)|^2\,dt
   \le C_\delta\bigl((T-H)/X+\log X\bigr).
\]
The cutoff and both interval endpoints are uniform. The complementary-divisor
estimate bounds the diagonal by an absolute constant divided by \(X\).
[Sharp interval estimate](Analysis/ActualInghamSharpLength.lean)
· [Complementary-divisor argument](Analysis/ActualInghamComplementaryDiagonal.lean)
· [One-log Gaussian endpoint with its full \(\Gamma(3/2)\) term](Analysis/ActualInghamSharpEndpoint.lean)

On \(\Re s>1\) the error is the tail with the actual truncated Möbius divisor
coefficients \(a_X(n)=\sum_{d\mid n,\ d\le X}\mu(d)\).
For \(\tau>1\), its exact squared coefficient sum is
\[
   \sum_{n>X} a_X(n)^2 n^{-\tau}
   =\zeta(\tau) S_X(\tau)-1,\qquad
   S_X(\tau)=\sum_{d,e\le X}\mu(d)\mu(e)[d,e]^{-\tau}.
\]
The signed off-diagonal mean-square error is bounded on both sides by 52
times the weighted coefficient sum. The totient expansion and uniform
coprime Möbius estimate give \(S_X(1)\le K\) with absolute \(K\).
The prime-by-prime comparison gives
\(S_X(1+b/\log X)\le e^{4b} S_X(1)\) for \(b\ge0\). These inputs all have
Lean proofs. [Coefficient identity](Analysis/ActualInghamMobiusCoefficients.lean)
· [Signed mean square](Analysis/ActualInghamSharpRightMoment.lean)
· [Totient expansion](Analysis/MobiusLCMTotientExpansion.lean)
· [Moving-line comparison](Analysis/ActualMobiusLCMTransport.lean)

The theorem `actual_gabriel_moving_window` proves the analytic mixed-norm
inequality for the pole-removed, Gaussian-damped actual error on the strip
from \(1/2\) to \(\beta\). The observation exponent is \(p=4/(3-\theta)\) at
\(\sigma=(1-\theta)/2+\theta\beta\), \(0\le\theta\le1\). It retains the
factor \(e^{b(\sigma^2-T^2)}(1-1/H)\), positive for \(H>1\). The theorem
`exists_actual_gabriel_sharp_window` supplies the two-log critical-line
and one-log right-line Gaussian budgets together, for \(2\le X\le T\) and
\(1\le H\le T\). Its constants are uniform in the window and interpolation
position. [Full strip theorem](Analysis/ActualInghamGabrielMovingWindow.lean)
· [Both endpoint estimates](Analysis/ActualInghamGabrielSharp.lean)

If \(2\le X\le T\le DX\) and \(2\le H\le T\), set
\(\theta=(\sigma-1/2)/(\beta-1/2)\) and
\(q_\theta=3(1-\theta)/(3-\theta)\). For every \(1/2\le\sigma\le1\),
the undamped actual moment then satisfies
\[
 \int_H^T |F_X(\sigma+it)|^{4/(3-\theta)}\,dt
 \le C_{\delta,D}\,T^{q_\theta}(\log T)^{1+q_\theta}.
\]
[Comparable-cutoff Gabriel moment](Analysis/ActualInghamGabrielComparable.lean)

## Inclusive zero counting

The actual Gabriel–Littlewood argument gives, uniformly for all \(T\ge2\)
and \(1/2\le\sigma\le1\),
\[
  N(\sigma,T)\le C\min\{T\log T,\;T^{q(\sigma)}(\log T)^{2+q(\sigma)}\}.
\]
The count includes analytic multiplicities at both inclusive upper thresholds.
Here \(2+q(\sigma)=(7-5\sigma)/(2-\sigma)\), the logarithmic exponent
in Chourasiya and Simonič's Theorem 1. The Lean theorem supplies one
existential constant. At \(\sigma=3/4\) the second term is
\(T^{3/5}(\log T)^{13/5}\).

Littlewood's lemma is applied to \(1-F_X^2\) on a single outward-shifted,
zero-free rectangle, with fixed lower height. A Jensen argument bounds
the signed top-minus-bottom horizontal argument integral by
\(O(1+\log(T+2)+\log(X+1))\). The left edge uses the undamped Gabriel
moment. Choosing \(X=\lfloor T\rfloor\) gives a uniform cost for moving
the counting line by at most \(2/\log T\).
[All-height counting theorem](Analysis/ActualInghamLittlewoodDensity.lean)
· [Horizontal argument](Analysis/ActualInghamHorizontalBoundary.lean)
· [Outward rectangle and moment count](Analysis/ActualInghamLittlewoodAssembly.lean)
· [Focused Bazel check](https://app.buildbuddy.io/invocation/035fedd8-2df2-4930-af8a-ec8c8bc885dc)

For every \(T\ge2\) and \(1/2\le\sigma\le1\), the sharp right edge in the
two-edge argument gives a single absolute constant for
\[
   N(\sigma,T)\le C\min\{T\log T,\;T^{q(\sigma)}(\log T)^{3+q(\sigma)}\}.
\]
At \(\sigma=3/4\) the second term is \(T^{3/5}(\log T)^{18/5}\).
[Sharp Cauchy counting theorem](Analysis/ActualInghamSharpDensity.lean)
· [Focused Bazel check](https://app.buildbuddy.io/invocation/10258554-1b74-4bdb-8389-d5213db28ded)

## The independent Selberg estimate

For \(0\le a<4/3\), any fixed \(A\), and \(u=(\sigma-1/2)\log T\), the
uniform one-log Selberg estimate is equivalent to its restriction to
\[
  A<u<\frac{2\log\log T}{4/3-a}.
\]
The dyadic and all-height statements are both available with uniform
constants. [Transition window](Analysis/ActualSelbergTransitionWindow.lean)

[ActualZeroLogExcessIntegral.lean](Analysis/ActualZeroLogExcessIntegral.lean)
gives the exact identity
\[
  W_{H,T}(\alpha)=\int_{\alpha}^{1} N_{H,T}(\sigma)\,d\sigma
\]
for \(\alpha\le1\). Both sides count the actual zeros with analytic
multiplicity on \(H<\Im\rho\le T\). The threshold is inclusive.

[ActualSelbergNearExcessCriterion.lean](Analysis/ActualSelbergNearExcessCriterion.lean)
proves `uniformSelbergDensity_iff_truncated_near_excess` for \(0<a\le4/3\).
This is the fixed-strip Z1 condition from the Ingham / Z03 checkpoint
with the Ingham argument supplied by `inghamDensityBound`. The converse
integrates the Selberg profile and retains the upper-endpoint subtraction
before bounding it by zero.

The sharper moving-window theorem
`uniformSelbergDensity_iff_dyadic_transition_logExcess` works for
\(0<a<4/3\) and any fixed \(A\ge0\). At the Z03 exponent \(a=1/4\),
`uniformSelbergDensity_quarter_iff_dyadic_transition_logExcess` gives the
equivalent provider
\[
  W_{T/2,T}(\alpha)\le D T e^{-u/4},
  \qquad A<u<\frac{24}{13}\log\log T,\qquad
  u=(\alpha-\tfrac12)\log T.
\]
Here \(D\ge0\) and the height threshold are uniform, with
\(\alpha\in[1/2,1]\). Recovering the count uses the existing shift
\(1/(a\log T)\), with the lower count cutoff raised to \(A+1/a\).
Baluyot's Theorem 1.2.1 gives the corresponding arithmetic estimate on paper,
since its exponent in these coordinates is twice the mollifier-length
parameter. An unconditional Lean proof of this arithmetic input remains open.

At the arithmetic level the actual Gaussian moment is the signed residue
sum plus the signed vertical integral minus the pole correction, including
both rays. The normalized pole correction is \(O_A(T^{-A})\) for every
fixed \(A\ge0\), uniformly over the padded Gaussian centers. For the full
\(0<a<8/7\) range, the remaining sufficient input is
`UniformGaussianMellinPartsBound` for an admissible \(a\le2\theta<8/7\):
uniformly in the height, center and near-line strip, the real part of
the combined arithmetic terms must be \(\le1+C y^{1-2\sigma}\), with
\(y=T^\theta\). The growing-modulus averaged Kloosterman estimate in
Baluyot's Chapter 3 is an external analytic input. The Lean reduction
retains the cancellation between the two arithmetic contributions.
[Pole estimate](Analysis/ConreyBaluyotGaussianPoleReduction.lean)
· [Exact signed splitting and conditional density theorem](Analysis/ConreyBaluyotRayMellinSeparation.lean)
· [Baluyot, Chapter 3, Lemma 3.1.6 and equation (3.4.61)](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320)

## Additive moving-line error in the strip

For fixed \(\delta>0\), write \(F_X(s)=\zeta(s)\sum_{n\le X}\mu(n)n^{-s}-1\)
and \(\beta=1+\delta/\log X\). The translated second-moment theorem
`exists_actual_moving_right_error_moment_add_log` bounds the integral over
\([H,T]\) by \(C_\delta((T-H)/X+\log X)\).
Averaging the affine majorant at \(U=Ta\sqrt v\) against \(e^{-v}dv\)
gives the right Gaussian endpoint
\[
 C_\delta\bigl(\log X+\Gamma(3/2)Ta/X\bigr).
\]
The declaration `exists_actual_gabriel_right_endpoint_add_log` proves this
bound and integrability on the complete positive ray.
The declaration `exists_actual_gabriel_sharp_window_add_log` transfers it
to every \(0\le\theta\le1\), \(p=4/(3-\theta)\), and damping \(b>0\)
with right scale \(a=1/(T\sqrt{2b})\). In particular the length term
in the right boundary budget is free of a multiplicative \(\log X\).
[Strip and endpoint proofs](Analysis/ActualInghamGabrielSharp.lean)

For a literature proof with explicit dependence on \(\delta\), put
\(c_X(n)=\sum_{d\mid n,\ d\le X}\mu(d)\). De la Bretèche, Dress and
Tenenbaum prove \(\sum_{n\le y}c_X(n)^2\ll y\), uniformly in \(X,y\).
Partial summation on \(n>X\) at \(s=2\beta\) and \(s=2\beta-1\), followed
by the Montgomery–Vaughan mean-value theorem, bounds the interval moment by
\[
 \ll e^{-2\delta}\bigl((T-H)/X+1+(\log X)/(2\delta)\bigr)
\]
with an absolute implied constant, also for real cutoffs \(X\ge2\).
This dependence on \(\delta\) is a paper refinement.
[Divisor-sum estimate, (1.5)](https://tenenb.perso.math.cnrs.fr/PPP/Sxz.pdf)
· [Dirichlet mean-value estimate, Lemma 10](https://arxiv.org/html/2507.15184v2)

## Verification

The focused Bazel check of the downstream Conrey–Baluyot module passed with the
all-heights estimate and the strengthened cofinal theorems in its imports.
The source includes guarded axiom checks for the classical proposition and both
logarithmic refinements. Each lists propext, Classical.choice, and Quot.sound.
[Focused BuildBuddy record](https://app.buildbuddy.io/invocation/d0388711-1695-4867-b75d-4aeba2bd7db3).

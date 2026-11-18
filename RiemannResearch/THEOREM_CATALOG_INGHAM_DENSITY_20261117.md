# Ingham's density bound for the actual zeta zeros

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

## Verification

The focused Bazel check of the downstream Conrey–Baluyot module passed with the
all-heights estimate and the strengthened cofinal theorems in its imports.
The source includes guarded axiom checks for the classical proposition and both
logarithmic refinements. Each lists propext, Classical.choice, and Quot.sound.
[Focused BuildBuddy record](https://app.buildbuddy.io/invocation/d0388711-1695-4867-b75d-4aeba2bd7db3).

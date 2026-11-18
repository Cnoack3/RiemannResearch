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
The proof above uses the three-logarithm right endpoint. The sharper
one-logarithm endpoint and the sharper published logarithmic profile remain
separate formalization targets.

[Chourasiya and Simonič](https://arxiv.org/abs/2507.15184) state the
classical Ingham bound and prove an explicit estimate with log exponent
\((7-5\sigma)/(2-\sigma)\). This source supports the analytic context and
the moment orders. The Lean proof above counts via individual Cauchy
rectangles and uses its own constants.

## Verification

The focused Bazel check of the downstream Conrey–Baluyot module passed with the
all-heights estimate and the strengthened cofinal theorems in its imports.
The source includes guarded axiom checks for the classical proposition and both
logarithmic refinements. Each lists propext, Classical.choice, and Quot.sound.
[Focused BuildBuddy record](https://app.buildbuddy.io/invocation/d0388711-1695-4867-b75d-4aeba2bd7db3).

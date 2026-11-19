# Rational disk centers and the horizontal RH threshold

Let \(\xi\) be the entire Riemann xi function, \(Z\) its nontrivial zero set, and \(B=\sup_{\rho\in Z}\Re\rho\). For each \(q\in\mathbb Q\) define \(s_q=1+iq\) and the Taylor coefficients
\[
a_n(q)=\frac1{n!}\left(\frac{\xi'}{\xi}\right)^{(n)}(s_q).
\]
The exact relation between derivative growth and the horizontal boundary is
\[
\sup_{q\in\mathbb Q}\limsup_{n\to\infty}|a_n(q)|^{1/n}
=\frac1{1-B},
\]
with the right side interpreted as infinity at \(B=1\). In particular, RH holds exactly when the left side is at most 2. With coefficients divided by the additional factor \(2^n\), the threshold is 1.

## Proof

The logarithmic derivative is holomorphic near each \(s_q\) and meromorphic on the plane. At every zero of multiplicity \(m\) it has a genuine simple pole with residue \(m\). The Taylor radius at \(s_q\) is therefore exactly \(d_q=\inf_{\rho\in Z}|s_q-\rho|\). The lower inequality follows by holomorphy inside the open disk. If the series had larger radius, uniqueness of analytic continuation would extend the logarithmic derivative through a nearest pole. A nearest zero exists because zeros are discrete and the set of zeros in any compact disk is finite. Cauchy–Hadamard now gives the pointwise root growth \(1/d_q\).

For every zero \(\rho=\beta+i\gamma\), one has \(|1+iq-\rho|\ge1-\beta\), and a sequence of rational ordinates tending to \(\gamma\) attains that infimum. Taking infima in both variables yields \(\inf_q d_q=1-B\). The functional equation reflects the nontrivial zero set across \(\Re s=1/2\), so \(B\le1/2\) is equivalent to RH. The geometric step, the exact radius-one-half disk criterion, and the starting radius from the continuum-contact source are the local Lean declarations. The Cauchy–Hadamard identification for this concrete logarithmic derivative is a paper deduction. [Rational disk theorems](RationalZeroFreeDisks.lean) · [Entire xi and its logarithmic derivative](WeilExplicitFormula/XiPrime/Seam.lean) · [Xi-zero characterization](WeilExplicitFormula/XiPrime/ExplicitFormula/ZeroFree.lean)

## Relation to a published pair criterion

Ford and Zaharescu prove that a sequence of normalized derivatives of smoothed **unnormalized differences** of positive Dirichlet-zero ordinates converges pointwise on \((1/2,\infty)\) exactly under RH for zeta. Theorem 4 fixes a primitive character modulo \(q>1\), a compactly supported smooth nonnegative density of integral one and a reference shift \(b>1/2\). For each derivative order \(k\), the height limit is taken before removing the smoothing. Their proof in §6 identifies the limiting normalized derivative differences and, if RH fails, constructs a subsequence growing exponentially. Consequently a subexponential-in-\(k\) bound at every fixed test location suffices for that published criterion as well. The rational-disk proof above uses complex derivatives of the completed logarithmic derivative and has its own countable testing set. [Ford and Zaharescu, Compositio Mathematica 151 (2015), Theorem 4 and §6](https://www.ford126.web.illinois.edu/wwwpapers/linear.pdf)

The externally verified continuum-contact boundary gives radius at least \(1-B_*\) at each rational ordinate, hence a normalized derivative growth ceiling \(1/[2(1-B_*)]\). The remaining task is to lower that ceiling to 1 at each rational ordinate. Positive density estimates average over zeros. A single zero inside a disk already reduces its radius.

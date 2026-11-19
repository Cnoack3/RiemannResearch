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

For every zero \(\rho=\beta+i\gamma\), one has \(|1+iq-\rho|\ge1-\beta\), and a sequence of rational ordinates tending to \(\gamma\) attains that infimum. Taking infima in both variables yields \(\inf_q d_q=1-B\). The functional equation reflects the nontrivial zero set across \(\Re s=1/2\), so \(B\le1/2\) is equivalent to RH. The repository proves the geometric disk condition, diskwise analyticity, and the exact Cauchy–Hadamard criterion for the actual scalar coefficients. The formal statement uses the equivalent reciprocal of the infimum of the horizontal distances, with values in the extended nonnegative reals. [Rational disk theorems](RationalZeroFreeDisks.lean) · [Taylor disks](XiTaylorDiskRadius.lean) · [Scalar coefficient criterion](XiTaylorCoefficientRadius.lean)

For the converse from the canonical coefficient radius, write $g(z)$ for the centered power-series sum inside its convergence disk. It agrees with $\xi'/\xi$ near the center. The analytic identity $g\xi=\xi'$ then holds throughout the disk by connectedness. The zeros of $\xi$ are isolated, so this gives equality of $g$ and $\xi'/\xi$ on a punctured neighborhood of every interior point. A zero of $\xi$ would give meromorphic order $-1$ to its logarithmic derivative, whereas $g$ has nonnegative order. In the forward direction, Cauchy's integral formula gives convergent expansions on all strictly interior disks. Uniqueness of scalar Taylor series identifies their coefficients with $a_n(q)$ and yields the radius bound up to the limiting radius. The inverse radius equals the root limsup by Cauchy–Hadamard. [Analytic disk identity and the pole obstruction](XiTaylorCoefficientRadius.lean) · [Kernel formulation of Cauchy–Hadamard](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Analytic/RadiusLiminf.html)

## Relation to a published pair criterion

Ford and Zaharescu prove that a sequence of normalized derivatives of smoothed **unnormalized differences** of positive Dirichlet-zero ordinates converges pointwise on \((1/2,\infty)\) exactly under RH for zeta. Theorem 4 fixes a primitive character modulo \(q>1\), a compactly supported smooth nonnegative density of integral one and a reference shift \(b>1/2\). For each derivative order \(k\), the height limit is taken before removing the smoothing. Their proof in §6 identifies the limiting normalized derivative differences and, if RH fails, constructs a subsequence growing exponentially. Consequently a subexponential-in-\(k\) bound at every fixed test location suffices for that published criterion as well. The rational-disk proof above uses complex derivatives of the completed logarithmic derivative and has its own countable testing set. [Ford and Zaharescu, Compositio Mathematica 151 (2015), Theorem 4 and §6](https://www.ford126.web.illinois.edu/wwwpapers/linear.pdf)

The externally verified continuum-contact boundary gives radius at least \(1-B_*\) at each rational ordinate, hence a normalized derivative growth ceiling \(1/[2(1-B_*)]\). The remaining task is to lower that ceiling to 1 at each rational ordinate. Positive density estimates average over zeros. A single zero inside a disk already reduces its radius.

The exact pointwise radius is stated as the infimum of the extended distances to all nontrivial zeros. The supremum over rational centers equals the inverse of the horizontal distance to the right boundary. The zero count is eventually positive, and reflection places at least one zero on or to the right of the critical line. Thus the actual root-growth supremum is at least 2. RH is equivalent to equality, and the continuum-contact nonvanishing input gives the current upper endpoint $1/(1-B_*)=7.8955174245431589\ldots$. [Scalar coefficients and exact extrema](XiTaylorCoefficientRadius.lean) · [Continuum contact](../Analysis/ActualQuasiRiemannSupport.lean)

## Signed moments of the prime-counting error

There is a prime-side version of the same exact growth statistic. Let $\psi(x)=\sum_{m\le x}\Lambda(m)$, $E(u)=e^{-u}\psi(e^u)-1$, and
$$
 I_n(q)=\frac1{n!}\int_0^\infty u^n E(u)e^{-iqu}\,du
 \qquad(q\in\mathbb Q).
$$
Each integral converges absolutely. For example, Fiori–Kadiri–Swidinsky's published estimate gives $|E(u)|<9.22106\,u^{3/2}\exp(-0.8476836\sqrt u)$ for $u>\log 2$. Near $u=0$ the integrand is bounded for each fixed $n$. The sharp target is
$$
 \sup_{q\in\mathbb Q}\limsup_{n\to\infty}|I_n(q)|^{1/n}
 =\frac1{\inf_\rho(1-\Re\rho)} .
$$
In particular, RH is equivalent to the statement that, for every rational $q$ and every $\varepsilon>0$, there is a finite $C_{q,\varepsilon}$ with $|I_n(q)|\le C_{q,\varepsilon}(2+\varepsilon)^n$ for all $n$. The original sign of the prime error and the complex phase are retained inside the integral. The reduction to these integrals is a paper deduction from the kernel-checked coefficient criterion. [Fiori–Kadiri–Swidinsky, *Sharper bounds for the Chebyshev function*](https://www.sciencedirect.com/science/article/abs/pii/S0022247X23004298) · [Accessible theorem statement](https://arxiv.org/abs/2204.02588)

To verify the transfer, fill the removable singularity at $s=1$ in $A(s)=\zeta'(s)/\zeta(s)+(s-1)^{-1}$. The Laurent expansion of zeta with residue one supplies this cancellation. Taking the logarithmic derivative of the completed xi product and using the digamma recurrence gives
$$
 \frac{\xi'}\xi(s)-A(s)
 =\frac12\left\{\frac{\Gamma'}{\Gamma}(1+s/2)-\log\pi\right\}.
$$
Its only poles are at $-2,-4,\ldots$. The Taylor coefficients of this difference at $c=1+iq$ have root growth at most $1/\sqrt{9+q^2}\le1/3$. Each nontrivial zero is still a simple pole of $A$ with residue its positive multiplicity. [DLMF, completed xi product](https://dlmf.nist.gov/25.4.E4) · [DLMF, digamma recurrence](https://dlmf.nist.gov/5.5.E2) · [DLMF, gamma and digamma poles](https://dlmf.nist.gov/5.2)

For $\Re s>1$, Abel summation of the absolutely convergent von Mangoldt series gives the repository's Chebyshev-error Mellin expression
$$
 J(s)=\int_0^\infty [\psi(e^u)-e^u]e^{-su}\,du
   = -\frac{\zeta'(s)}{s\zeta(s)}-\frac1{s-1}
   =-\frac{A(s)+1}{s}.
$$
This expression is regular at $s=1$ after filling the removable value. Multiplication by $-1/s$ preserves every nontrivial pole, because every nontrivial zero differs from zero. The possible new pole at $s=0$ has distance $\sqrt{1+q^2}\ge1$ from the test center. The poles at negative even integers have distance at least three. Thus the supremum of the root growth for any of these additional poles is at most one. The actual nontrivial zero poles give global growth at least two. Consequently $J$, $A$, and $\xi'/\xi$ all give exactly the same supremum over rational $q$, even when individual Taylor radii differ. [Repository Mellin identity](ChebyshevMellin.lean) · [Actual zeta pole orders](ChebyshevMellinRH.lean) · [Euler product](https://dlmf.nist.gov/25.2.iv)

For each fixed $n$, differentiate the integral for $\Re s>1$ and let $s=\sigma+iq$ with $\sigma\downarrow1$. The bound on $|E|$ above dominates $u^n |E(u)|e^{-(\sigma-1)u}$ by an integrable function independent of $\sigma$. Dominated convergence and the holomorphy of $J$ at $c$ give $J^{(n)}(c)/n!=(-1)^n I_n(q)$. Cauchy–Hadamard now gives the stated equality with this order of limits. At $q=n=0$, the Laurent expansion yields the normalization check $I_0(0)=J(1)=-1-\gamma_{\rm E}$, where $\gamma_{\rm E}$ is Euler’s constant.

# The Selberg density endpoint in the repository's normalization

Write $L=\log T$, $X=L(\sigma-1/2)$ and let $N(\sigma,T)$ count each nontrivial zero with $0<\gamma\le T$ and $\beta\ge\sigma$ with its analytic multiplicity. The uniform one-logarithm estimate at slope $a$ asks for

\[
N(\sigma,T) \le C_a T L e^{-aX}
\quad (T\ge T_a,\quad 1/2\le\sigma\le1).
\]

Baluyot proves this for **each fixed $0<a<8/7$**. The source uses mollifier length $T^\theta$, exponent $1+\theta(1-2\sigma)$, and a strict right cutoff. Its slope is $a=2\theta$; the repository converts the strict count to the inclusive count, including equality at $1/2$. Each fixed slope has its own constant and threshold. [Baluyot, Theorem 1.2.1 and §3.6](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320) · [Tao, Trudgian and Yang, zero-density chapter](https://teorth.github.io/expdb/blueprint/zero-density-chapter.html)

The November 19 source audit also records a newer dyadic fourth-moment claim implying a single logarithm at $a=4/3$. Lean proves that implication with the dyadic estimate explicit. The interpolation below uses only the classical subcritical range and the native Ingham bound. [Source audit and checked implications](SelbergDensitySourceAudit20261119.md)

## A uniform estimate at the limiting slope

The repository's Gabriel–Littlewood bound gives $N(\sigma,T)\ll T^q L^{2+q}$, with $q=3(1-\sigma)/(2-\sigma)$. Since $q\le1-(4/3)(\sigma-1/2)$, it follows that

\[
N(\sigma,T) \ll T L^3 e^{-(4/3)X}.
\]

Geometric interpolation with a fixed subcritical Selberg slope gives

\[
N(\sigma,T)\ll_\varepsilon T L^{1+\varepsilon} e^{-(8/7)X}
\qquad(\varepsilon>0).
\]

More generally, for $8/7<b<4/3$, a log power $1+e$ works whenever $e>(21/2)(b-8/7)$. These constants are independent of $T,\sigma$. At $4/3$ the preceding unconditional three-logarithm estimate applies. The straight-line comparison here concerns what follows from these two envelopes. [Lean derivation](../Analysis/ActualSelbergDensityInterpolation.lean) · [Chourasiya and Simonič](https://arxiv.org/abs/2507.15184)

At the exact tilt $8/7$, the exponential moment of $L|\beta-1/2|$ is $O_\varepsilon(L^\varepsilon)$ for every $\varepsilon>0$. Indeed the interpolation permits a slope strictly *above* $8/7$ at any positive prescribed loss. The gap between the two fixed slopes makes integration of the tilted tail finite, uniformly in the height. The constant in this moment can depend on the loss. [Critical exponential moment](../Analysis/ActualSelbergCriticalExponentialMoment.lean)

## The remaining window for a single logarithm

The clean $a=8/7$ estimate holds unconditionally wherever $X\ge(21/2)\log L$. Indeed $L^2\exp[-(4/3-8/7)X]\le1$ precisely in this range. Consequently the global clean endpoint is **equivalent** to proving it for $0\le X\le(21/2)\log L$ with one absolute constant. The shifted Conrey input controls every fixed interval and even a single unspecified diverging window \(W(T)\to\infty\) with a height-uniform constant, by the formal theorem `microscopic_endpoint_on_growing_window`. The comparison \(W(T)\ge(21/2)\log L\) that would cover the remaining window is open. [Lean window equivalence](../Analysis/ActualSelbergDensityInterpolation.lean) · [Fixed-scale stop-loss estimates](OptimizedHorizontalMoments20261119.md)

A sufficient moving-slope version uses $a_T=8/7-g(T)$, a common bound $C$, and $0\le g(T)$ with $g(T)\log L\le M$ eventually. In the remaining window,

\[
e^{-a_T X}=e^{g(T)X}e^{-(8/7)X}\le e^{21M/2}e^{-(8/7)X}.
\]

This identifies an analytic target with the needed order of uniformity. In Baluyot's (3.6.2), the two error terms contain $T^{-1/2+7\delta/2+\varepsilon}y^{7/8}$ and $T^{-1+7\delta/2+\varepsilon}y^{7/4}$. His choices in (3.6.3)–(3.6.7) use a **fixed** margin $4/7-\theta$ before $T\to\infty$. To see what a quantitative refinement would give, set $y=T^{4/7}\exp[-B L/\log L]$ and replace the smoothing exponent $\delta$ by $D/\log L$. If the remaining losses in both error terms admit a uniform bound $\exp(K L/\log L)$, with the constants of the diagonal and desmoothing estimates uniform for these choices, any $B>(8/7)(K+7D/2)$ makes both errors exponentially small in $L/\log L$. Meanwhile $y^{1-2\sigma}\le e^{21B}e^{-(8/7)X}$ throughout the remaining window. The printed fixed-$\varepsilon$ estimate does not furnish those uniform constants. This quantitative mollifier estimate is an **open** provider. [Baluyot, §3.6, equations (3.6.2)–(3.6.12)](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320)

## A sharp obstruction for the two available envelopes

For \(t\ge1\), put probability \(m=\exp(t-8t^2/7)\) at the mark \(X=t^2\), and the remaining probability at zero. Choose \(L=\exp(2t^2/21+t/2)\). For every fixed \(a<8/7\), completing the square gives \(m\le e^{1/[4(8/7-a)]}e^{-at^2}\). Also \(m=L^2 e^{-(4/3)t^2}\) exactly. These inequalities control the full positive tail of the two-atom model because the tail is constant up to its positive atom and vanishes beyond it.

For a proposed slope \(b\) and surplus log exponent \(e\), the ratio at the atom is exactly
\[
  m e^{bt^2}/L^e=\exp\big((b-8/7-2e/21)t^2+(1-e/2)t\big).
\]
It diverges whenever \(e\le(21/2)(b-8/7)\) and \(e<2\). This proves that the clean \(8/7\) endpoint, and even equality in the interpolation exponent for \(8/7<b<4/3\), cannot follow from these two numerical envelopes alone. At \(b=4/3,e=2\) the ratio is one. The model is a probability law used to delimit a method for bounding actual zeros. [Exact profile and divergence](../Analysis/SelbergDensityProfileSharpness.lean)

This obstruction persists even if the normalized exceptional contribution to *every* strictly subcritical exponential moment tends to zero: for \(a<8/7\), it equals \(\exp[t-(8/7-a)t^2]\to0\). In particular all fixed positive polynomial mark moments of the model tend to zero. Uniform control along a genuinely growing scale is what the clean density endpoint requires.

The exceptional mark respects the physical strip width for large heights. For \(t\ge42\), \(L=e^{2t^2/21}e^{t/2}\ge t^3/21\ge2t^2\), so \(X/L\le1/2\). Splitting its mass equally at horizontal displacements \(\pm X/L\) also enforces reflection symmetry.

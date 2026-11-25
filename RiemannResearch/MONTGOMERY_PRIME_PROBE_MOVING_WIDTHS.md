# Prime-probe energy beyond logarithmic widths

The reference commit is [87d798f4](https://github.com/Cnoack3/RiemannResearch/commit/87d798f4718f8a8897a8a02da82551465ad3343d). Write $L=\log T$, $P_T=\texttt{primeFourierProbe}\ T$, $c=\texttt{primeContinuumProbe}$, and $G_{\sin}=\texttt{sineGapMass}$. The arithmetic question is whether

$$
H_T(q)=\int_0^q |P_T(u)|^2\,du-(q-G_{\sin}(q))
$$

tends to zero for an eventually nonnegative moving width. In this normalization $q-G_{\sin}(q)=\int_0^q|c(u)|^2du$, with limiting value $1/2$ as $q\to\infty$.

## Centering and the three-halves estimate

Let $S(x)=\sum_{n\le x}\Lambda(n)/n$ and $e(y)=e^{-y}\psi(e^y)-1$. Partial summation with the inclusive upper endpoint, followed by a change of variables, gives for every $y\ge0$
$$
S(e^y)-y=1+e(y)+\int_0^y e(t)\,dt.
$$
The repository's unconditional classical quantitative PNT implies $|e(y)|\ll e^{-a\sqrt y}(1+y)^{-2}$ after decreasing the positive exponent and enlarging the constant. Define
$$
C=1+\int_0^\infty e(t)\,dt,\qquad r(y)=S(e^y)-y-C.
$$
Then $r(y)=e(y)-\int_y^\infty e(t)\,dt$ and $|r(y)|\ll e^{-a\sqrt y}/(1+y)$. In particular the constant is uniquely determined, $r(0)=-C$, and $r\in L^1\cap L^2(0,\infty)$.

Put $z=2\pi i u$. The exact shifted Abel identity is
$$
P_T(u)-c(u)=\frac{C+e^z r(L)}{L}
       -\frac zL\int_0^1 r(Lv)e^{zv}\,dv.
$$
The identity $z\int_0^1 e^{zv}\,dv=e^z-1$, including at $z=0$, accounts for the constant. The physical-space integral after centering is exactly
$$
\int_0^1\left(D_T(v)-\frac CL\right)^2dv
=\frac1{L^3}\int_0^L r(y)^2dy,
\qquad D_T(v)=\texttt{primeLogCDF}(T,v)-v .
$$
Writing $M_2=\int_0^\infty r^2$, $B=\log 4+4+2|C|$, the bound uniform in $T>1,q\ge0$ is
$$
I_T(q):=\int_0^q|P_T-c|^2\le
2B^2\frac q{L^2}+8\pi^2M_2\frac{q^2}{L^3}.
$$
The first term also covers the upper endpoint $r(L)$. Cauchy–Schwarz and the continuum energy bound give $|H_T|\le 2\sqrt{I_T}+I_T$. Thus $q=o(L^{3/2})$ suffices, including every $q=c_0 L$ with fixed $c_0\ge0$. There is no zero-distribution hypothesis in the arithmetic estimate.

## Actual-zero implications

Write $A_T(q)=\texttt{sampledArgumentIncrement}\ T\ q$. For each fixed positive rational $q$, the repository characterizes ordinary positive-gap PCC by $A_T(q)+\texttt{primeProbeEnergy}\ T\ q\to0$ at every such width. When a chosen moving width has $H_T(q(T))\to0$, replacing the prime energy by $q(T)-G_{\sin}(q(T))$ changes the signed trace by a term tending to zero. At a diverging width with finite limiting defect $\delta$, the uncorrected trace tends to zero exactly when $A_T(q(T))\to-1/2-\delta$. The arithmetic estimate supplies the centering. A bound on the signed increments still requires information about actual zero ordinates.

There is a complementary one-sided formulation. Write $G_T(q)=\texttt{positiveGapMass}\ T\ q$. Suppose that for every fixed rational shell $0\le a<b$ and every $\varepsilon>0$, eventually $G_T(b)-G_T(a)\le G_{\sin}(b)-G_{\sin}(a)+\varepsilon$. Then PCC is equivalent to the following cofinal lower test. For every $\varepsilon>0$ and integer $m\ge0$, there is an integer $n>m$ such that eventually
$$
 A_T(n)+\texttt{primeProbeEnergy}\ T\ n\ge-\varepsilon .
$$
The integer is chosen before the limit in $T$. This follows from the fixed-width signed discrepancy identity and the repository's cofinal affine lower criterion. A lower test at a single drifting width has a different quantifier. A measure can remove a fixed amount of mass from a bounded shell of positive model mass and place it at the drifting endpoint, leaving a fixed deficit on the original shell while preserving the model cumulative value at the moving endpoint.

The stronger repository predicate `FullOrdinateIntervalUpper` adds $\mathbf1_{a=0}(\mathrm{actualCollision}(T)/(T\log T/(2\pi))-1)$ to the left side of the shell test. It implies normalized collision convergence to one, ordinary positive-gap PCC, and the fixed-rational signed trace. The repository proves the converse from PCC under `ShortWindowSecondMomentUpper`. The prime error estimates supply neither the full interval predicate nor this second-moment assumption.

[Signed arithmetic trace](https://github.com/Cnoack3/RiemannResearch/blob/87d798f4718f8a8897a8a02da82551465ad3343d/RiemannResearch/Analysis/MontgomeryPrimeProbeEnergy.lean) · [Ordinate intervals](https://github.com/Cnoack3/RiemannResearch/blob/87d798f4718f8a8897a8a02da82551465ad3343d/RiemannResearch/Analysis/MontgomeryOrdinateIntervalUpper.lean) · [Classical quantitative PNT](https://github.com/Cnoack3/RiemannResearch/blob/87d798f4718f8a8897a8a02da82551465ad3343d/RiemannResearch/NumberTheory/PrimeNumberTheorem/Quantitative/ClassicalStrongPNT.lean)

## Sharp range and the quadratic transition

The quadratic threshold and its limiting coefficient are proved on paper below. Lean verifies the summable Mertens envelope, a squared-increment estimate on each block, a Fourier translation estimate, and the first-atom lower bound. A Lean proof of the full quadratic profile still requires the uniform tail estimate (1), the diagonal limit, and the bound on the signed mixed term. [Mertens envelope](Analysis/MontgomeryCenteredMertens.lean) · [Block increments](Analysis/MontgomeryPrimeProbeBlockIncrement.lean) · [Fourier translation](Analysis/MontgomeryPrimeProbeTranslation.lean) · [First atom](Analysis/MontgomeryPrimeProbeAtomTest.lean)

Define the signed measure on log coordinates by
$$
\nu_L=\sum_{2\le n\le e^L}a_n\delta_{\log n}-\mathbf1_{(0,L]}dy,\qquad
a_n=\Lambda(n)/n,\qquad F_L(\xi)=\int e^{2\pi i \xi y}\,d\nu_L(y).
$$
With $A=q/L$, one has $P_T(u)-c(u)=F_L(u/L)/L$ and $I_T(q)=L^{-1}\int_0^A |F_L(\xi)|^2d\xi$. The stretched-exponential estimate above gives a summable sequence of suprema of $|r|$ on intervals $[j,j+2]$.

### Local mass and Fourier means

For an integer $M$ and real $L$ with $0\le M\le L$, truncate the same signed measure to
$(M,L]$ and call the result $\nu_{M,L}$. Its Fourier transform is $F_{M,L}$.
For $0<h\le1$ let $b(x)=\nu_{M,L}((x,x+h])$. Clipping both
endpoints to $[M,L]$ gives
$b(x)=r(\operatorname{clip}(x+h))-r(\operatorname{clip}(x))$.
For $x\in[j,j+1]$ where $b(x)\ne0$ the two clipped endpoints
belong to $[\max(0,j),j+2]$. Put
$e_j=\sup_{[\max(0,j),j+2]}|r|$ for $j\ge-1$.
Then $|b(x)|\le 2e_j$. Uniformly in $M,L,j$,
$$
 \int_j^{j+1}|b(x)|\,dx\le h|\nu_{M,L}|([j,j+2])\ll h.
$$
Tonelli gives the first inequality. For the second, the mass of the positive
arithmetic measure in a closed length-two interval is bounded by its mass
in a slightly larger half-open interval, which is $O(1)$ by the Mertens
discrepancy bound. It follows that
$$
 \|b\|_2^2\ll h\sum_{j\ge M-1}e_j.
$$
Apart from an endpoint convention on a Lebesgue-null set,
$b=\nu_{M,L}*\mathbf1_{[-h,0]}$. Its transform has modulus
$h|\operatorname{sinc}(\pi h\xi)||F_{M,L}(\xi)|$.
For $A\ge1$, choose $h=(2A)^{-1}$.
On $0\le\xi\le A$ the sinc factor is at least $2/\pi$.
Plancherel yields
$$
 \frac1A\int_0^A|F_{M,L}(\xi)|^2\,d\xi\ll\sum_{j\ge M-1}e_j .
 \tag{1}
$$
For $M=0$, $F_{0,L}=F_L$. When $0<A\le1$, the centered Abel formula gives
$|F_L(\xi)|\le |C|+\|r\|_\infty+2\pi\|r\|_1$ on $[0,A]$.
Thus for all $T>1, q\ge0$,
$$
 E_d(T,q):=\int_0^q|P_T-c|^2\,du \ll \frac{q}{L^2}.
 \tag{2}
$$

### Diagonal coefficient

The exact double-sinc expansion has a contribution of $qL^{-2}\sum_{n\le T}a_n^2$ on its diagonal. Its off-diagonal summands can have either sign. The uniform tail estimate above permits truncating the measure before averaging. [Exact double-sinc expansion](https://github.com/Cnoack3/RiemannResearch/blob/87d798f4718f8a8897a8a02da82551465ad3343d/RiemannResearch/Analysis/MontgomeryPrimeProbeSincExpansion.lean)

For fixed integer $M\ge0$, the positive-frequency Cesàro mean
$A^{-1}\int_0^A|F_M|^2$ converges to
$D_M=\sum_{n\le e^M}a_n^2$. The pure finite atomic part follows by
integrating each exponential from a pair of distinct logarithms and dividing
by $A$. The transform of the fixed interval has finite total square
integral $M$, so its contribution and mixed term vanish by Cauchy–Schwarz.
The coefficients are summable in square because
$0\le a_n\le(\log n)/n$ for $n\ge2$.
The reverse triangle inequality in the norm
$\|f\|_A^2=A^{-1}\int_0^A|f|^2$, followed by the uniform tail estimate (1), gives
$$
 \big|\|F_L\|_A-\|F_M\|_A\big|
 \ll\left(\sum_{j\ge M-1}e_j\right)^{1/2},\qquad L\ge M,\quad A\ge1.
$$
First take $A,L\to\infty$ and then $M\to\infty$. Thus
$\|F_L\|_A^2\to D$ jointly, where
$$
 D=\sum_{n\ge2}\frac{\Lambda(n)^2}{n^2}
  =\sum_p\frac{(\log p)^2}{p^2-1}>0 .
$$
It follows that $E_d(T,q)\sim Dq/L^2$ whenever $q/L\to\infty$.

### Uniform control of the signed mixed term

Let $A=q/L$ and $\operatorname{Si}(t)=\int_0^t (\sin s)/s\,ds$.
The finite Fourier representation and Fubini give
$$
 2\Re\int_0^q \overline{c(u)}\,(P_T(u)-c(u))\,du
 =\frac1L\int_{[0,L]}g_{A,L}(y)\,d\nu_L(y),
 \quad
 g_{A,L}(y)=\frac{\operatorname{Si}(2\pi Ay)+
     \operatorname{Si}(2\pi A(L-y))}{\pi}.
$$
Indeed, integrating cosine in $u$, then $v\in[0,1]$, yields the displayed
kernel with a removable value at the origin. The sine integral is bounded on the whole real line. On $[1,X]$ this follows by integrating $\sin(t)/t$ by parts once and bounding $\int_1^Xdt/t^2$. For $L\ge2$, the two boundary strips of width one
have uniformly bounded total variation of $\nu_L$. On $[1,L-1]$,
$$
 |g'_{A,L}(y)|\le \frac{1}{\pi y}+\frac{1}{\pi(L-y)}\le 2/\pi.
$$
Here $d\nu_L=dr$. Stieltjes integration by parts bounds the interior
contribution by two bounded endpoint terms and $2\|r\|_1/\pi$.
Choose a disjoint half-open partition of the strips. Any shared atom
can also be absorbed in either boundary estimate. Consequently the mixed
term is $O(1/L)$, uniformly in $q$.

Writing $E_T(q)=\int_0^q |P_T(u)|^2du$ and $E_0(q)=q-G_{\rm sin}(q)$,
the resulting signed profile is
$$
 |E_T(q)-E_0(q)|\ll L^{-1}+q L^{-2},\qquad
 E_T(q)-E_0(q)\sim D q L^{-2}\quad(q/L\to\infty).
$$
Therefore $q=o(L^2)$ is necessary and sufficient for
$E_T(q)-E_0(q)\to0$ for eventually nonnegative widths. For necessity,
any subsequence on which $q/L^2\ge\epsilon>0$ also satisfies $q/L\to\infty$.
At $q/L^2\to\alpha>0$ the excess tends to $\alpha D$.

# The second-order transition for the raw Montgomery form factor

Put \(L=\log T\), \(u=(\log L+c)/2\), \(\alpha=u/L\), and \(x=e^u=e^{c/2}\sqrt L\). Fix \(A\ge0\) and take \(|c|\le A\). Let \(F_{\rm raw}\) be the positive-height raw-ordinate form factor with normalization \(TL/(2\pi)\) and \(w(y)=4/(4+y^2)\). Let \(F_\sharp\) denote the corresponding complex-zero statistic. In both sums each analytic zero occurrence with \(0<\gamma\le T\) is counted, including coincident ordinates.

The calculation below gives, uniformly in bounded \(c\),
\[
 F_{\rm raw}(T,\alpha)=e^{-c}+\frac{\log L+c}{2L}
       +O_A(L^{-1}).
\]
In particular \(2L(F_{\rm raw}-e^{-c})/\log L\to1\) uniformly on those intervals. The final section refines the remainder by recovering the signed archimedean constant. This is an analytic derivation. The status of individual Lean components is recorded separately in the theorem catalog. No novelty comparison establishes priority for this asymptotic.

## Positive-height complex estimate at the transition

Use the positive-height version of Baluyot, Goldston, Suriajaya and Turnage-Butterbaugh, equation (3.4) and its proof. With the paper's **unnormalized** sum \(\mathcal F_{(0,T]}(x)\),
\[
  2\pi\mathcal F_{(0,T]}(x)=R(x,T)+O(\sqrt T+x),\qquad
  R=\int_0^T |A_1+A_2+A_3|^2\,dt.
\]
The absolute constant \(2\pi\) is absorbed into the cutoff error. Equation (3.5) in that paper supplies a uniform error \(O(T\sqrt L)\) on \(1\le x\le T\). The sharper transition error below follows by returning to (3.4) and the displayed component estimates in its proof. For sufficiently large \(T\) depending on \(A\), the entire interval \(e^{-A/2}\sqrt L\le x\le e^{A/2}\sqrt L\) lies in \([2,T]\). [BGSTB, corrected text, §3](https://arxiv.org/html/2501.14545v3#S3.E4)

Writing \(M_j=\int_0^T|A_j|^2dt\), the paper gives
\[
 M_1=\frac{T}{x^2}(L^2+O(L)),\qquad
 M_3\ll T/x^2+x,\qquad
 \left|\int_0^T A_1\overline{A_2}\,dt\right|
 \ll \frac{\log T}{\sqrt x\log(2x)}.
\]
The first expression uses \(A_1=\log(t+2)/x\), so its unexpanded lower-order contribution is \(O_A(T)\) here. Retaining \(T/x^2+x\) gives \(M_3\ll_A T/L\). Both endpoint terms in (3.4) are \(O_A(T)\).

For \(r_n(x)=\min(n/x,x/n)\), the second part is the absolutely convergent Dirichlet series \(-\sum_n \Lambda(n) r_n(x)n^{-1/2-it}\). The Montgomery–Vaughan mean-value theorem with the integer frequency spacing gives
\[
 M_2= T D(x)+O\!\left(\sum_n\Lambda(n)^2r_n(x)^2\right),\quad
 D(x)=\sum_n\frac{\Lambda(n)^2}{n}r_n(x)^2 .
\]
The finite-polynomial inequality passes to the limit since the weighted coefficient square sum is finite and the series converges uniformly in \(t\) for fixed \(x\). [Montgomery–Vaughan, *Hilbert's inequality*, 1974](https://doi.org/10.1112/jlms/s2-8.1.73)

For completeness, the classical prime number theorem with an error \(O(y/\log^2 y)\) in \(\vartheta(y)\) gives \(S(y)=\sum_{n\le y}\Lambda(n)^2=y\log y+O(y)\). Indeed summation by parts applies to \(\sum_{p\le y}(\log p)^2\), and the prime powers of order at least two contribute \(O(\sqrt y\log^3(2y))\). Stieltjes integration with the head closed at real \(x\) and tail open at \(x\) gives the exact cancellation
\[
 \begin{aligned}
 D(x)&=x^{-2}\int_{1^-}^x t\,dS(t)+x^2\int_{(x,\infty)}t^{-3}\,dS(t)\\
     &=-x^{-2}\int_1^x S(t)\,dt+3x^2\int_x^\infty S(t)t^{-4}\,dt .
 \end{aligned}
\]
The two boundary terms \(S(x)/x\) and \(-S(x)/x\) cancel even for a prime power \(x\). The \(t\log t\) terms have total \(\log x+O(1)\) and the integrated \(O(t)\) remainders are bounded uniformly. The analogous head/tail partial summation, or dyadic decomposition with \(S(y)\ll y\log(2y)\), gives \(\sum_n\Lambda(n)^2r_n(x)^2\ll x\log(2x)\). Thus \(M_2=T\log x+O_A(T)\), and \(M_2\ll_A T(1+\log L)\).

Garunkštis and Paliulionytė, §2, before equation (2.28), give the sharper spacing-weighted remainder \(O(x\log\log(4x))\). Their displayed spacing estimate concerns the positive von Mangoldt weights themselves. Their main pair theorem concerns primitive Dirichlet characters of conductor greater than one. Here the preceding direct argument for ζ is sufficient at the transition. [Glasnik Matematički 60 (2025), 207–227](https://web.math.pmf.unizg.hr/glasnik/vol_60/no2_03.html)

The signed expansion of \(R\) contains \(M_1+M_2+M_3\) and \(2\operatorname{Re}\int A_i\overline{A_j}\) for all three \(i<j\). The \(1,2\) term has the oscillatory bound above. Cauchy–Schwarz gives \(O_A(T)\) for \(1,3\) and \(O_A(T\sqrt{(1+\log L)/L})\) for \(2,3\). Consequently
\[
 R=TL^2/x^2+T\log x+O_A(T),\qquad
 F_\sharp(T,\alpha)=e^{-c}+\alpha+O_A(L^{-1}).
\]
The main term \(e^{-c}\) uses \(L/x^2=e^{-c}\). The displayed asymptotic is derived in the narrower range and cannot be substituted for (3.5) over the full support interval.

## The reflected difference before squaring

For each zero occurrence set \(d_i=\beta_i-1/2\), \(t_i=\gamma_i\), and \(b_i=e^{iut_i}\). Reflection across the critical line preserves the positive-height range and analytic multiplicities. The exact difference of the weighted spectral signals at shift \(s\) is
\[
 e^{-|s|}\sum_i b_i e^{ist_i}[\cosh(d_i(u+s))-1].
\]
The repository's integral representation and reverse triangle inequality bound the difference of the square roots of the two normalized form factors by the square root of the normalized squared norm of this signal. Keeping both reflected shifts in each summand gives an additional cancellation.

Define \(H_d f(y)=(f(y+d)+f(y-d))/2-f(y)\) and
\[
 G_{u,v}(y)= e^{uy}\frac{4}{4-(y+iv)^2}.
\]
The \(i,j\) Gram entry before multiplication by \(b_i\overline{b_j}\) is **exactly**
\(H_{d_i}H_{d_j}G_{u,t_i-t_j}(0)\). Expand both hyperbolic cosines and apply \(\int_{\mathbb R}e^{-2|s|}e^{(y+iv)s}\,ds=4/(4-(y+iv)^2)\) for \(|y|<2\). The pair features are integrable because all shifts satisfy \(|d_i|+|d_j|\le1\).

Taylor's theorem with integral remainder gives, also for negative shifts,
\[
 H_d f(y)=\frac{d^2}{2}\int_{-1}^1 (1-|r|) f''(y+rd)\,dr .
\]
Both applications retain their boundary terms through the central differences. The arguments of \(G^{(4)}\) belong to the interval \(|y|\le |d_i|+|d_j|\). Write the rational factor as \(4/[(2-y-iv)(2+y+iv)]\). Every denominator has magnitude at least \(\sqrt{1+v^2}\) there. Differentiation and the product rule show for \(0\le k\le4\) that the rational factor's \(k\)-th derivative has magnitude at most \(4k!(k+1)/(1+v^2)\). Each term in the derivative of the two reciprocals retains one factor of each denominator. Leibniz then yields
\[
 |H_a H_b G_{u,v}(0)|\ll
 \frac{a^2 b^2 (1+|u|)^4 e^{|u|(|a|+|b|)}}{1+v^2}.
\]
The exponential is uniform at the pair level and does not use a maximum displacement over all zeros.

The actual ordinate row estimate is \(\sup_i\sum_j(1+|t_i-t_j|^2)^{-1}\ll\log(T+3)\). It follows from local zero counts with multiplicities, independently of PCC. Apply the symmetric Schur bound with nonnegative weights \(v_i=d_i^2e^{|u||d_i|}\). Dividing the integral by the form-factor normalization gives
\[
  {\rm horizontalDefect}(T,\alpha)
  \ll \frac{(1+|u|)^4}{T}\sum_i |d_i|^4 e^{2|u||d_i|}.
\]
All off-diagonal and repeated-ordinate pairs are incorporated in this estimate. No division by an ordinate gap occurs.

Suppose a fixed positive Selberg exponent \(a\) gives
\(\#\{i:|d_i|>s\}\le C T L e^{-aLs}\), \(0\le s\le1/2\).
For \(q=aL\), \(v=2|u|\le \theta q\), \(0\le\theta<1\), layer cake with \(f(s)=s^4e^{vs}\) gives
\[
 \sum_i f(|d_i|)\le CTL
 \int_0^\infty(4s^3+vs^4)e^{-(q-v)s}ds
 =24CTL\,\frac{q}{(q-v)^5}.
\]
Thus the defect is \(O_{a,\theta}((1+|u|)^4/L^3)\). It tends to zero for \(|u|=o(L^{3/4})\), exactly the same upper frequency scale as the current reflected quartic estimate. At the **transition**, however, it gives
\[
 |\sqrt{F_{\rm raw}}-\sqrt{F_\sharp}|
   \ll_A (1+\log L)^2/L^{3/2}=o_A(1/L).
\]
Here \(F_\sharp=O_A(1)\), whence the two nonnegative square roots are bounded and the same little-oh bound applies to the form factors themselves. This proves the stated raw expansion. Under RH the horizontal difference vanishes identically, so the calculation gives no positive horizontal lower bound. The nonzero second-order coefficient comes from \(T\log x\) on the prime side.

The repository also has an independent route at the transition. Its checked Ingham moment estimates give enough higher absolute moments to absorb an exponential tilt of size \(2u=O_A(\log L)\). Split at displacement \(1/\log L\). The tilt on the near side is uniformly bounded, and on the far side the extra high moment absorbs its power of \(L\). The resulting fourth-moment estimate is \(O_A((\log L)^4/L^3)\) after division by \(T\). Combined with the quartic Gram bound it yields a defect of \(O_A((\log L)^8/L^3)\) and a raw-to-complex form-factor gap \(O_A((\log L)^4/L^{3/2})\). This supplies the signed second and third terms without a temporary Selberg-density assumption. The Selberg route improves the logarithmic prefactor in the horizontal comparison.

For the individual reflected pair the exact optimal prefactor multiplying \(a^2b^2(1+|u|)^4e^{|u|(|a|+|b|)}w(v)\) is \(8/15\). All five derivatives of \(4/(4-(y+iv)^2)\) on \(|y|\le1\) are dominated by \(w(v)\) times the fourth derivative of the real comparison kernel \(Q_0(y)=4/(4-y^2)\). Averaging the fourth derivative against the two triangular Taylor weights reduces the extremum to \(u=v=0,\ a=b=1/2\), where the mixed central difference is \(1/30\). The accompanying sharp-constant note gives the full argument and an algebraic certificate for the comparison model. This replaces the contour estimate \(1536e\) by a factor \(2880e\) in the individual-pair inequality.

The pairwise Cauchy-weight constant in this argument can be made optimal. The estimate keeps \((1+|u|)^4e^{|u|(|a|+|b|)}a^2b^2 w(d)\) and has best uniform coefficient \(8/15\) on \(|a|,|b|\le1/2\). Equal displacements \(a=b=1/2\) with \(u=d=0\) give a kernel value \(1/30\). On each smaller symmetric band \(|a|,|b|\le r\) the optimal coefficient is \(3/[2(4-r^2)(1-r^2)]\). The accompanying reflected-kernel note gives the comparison, sharpness proof and the scope of this pairwise extremizer.

## What this reaches in the pair-correlation program

These are shrinking normalized frequencies. The second-order formula fixes the leading error at the boundary between the spike and the small-frequency form factor. Pair-correlation asymptotics for fixed normalized support or above support one require estimates on different frequencies. In the displayed quartic majorant, \(u=\alpha L\) with fixed \(\alpha\ne0\) yields a term of order \(\alpha^4 L\).

Ford and Zaharescu's unconditional Theorem 1 on unnormalized differences has a test function whose support stays away from zero, with an error constant depending on that function. Its prime density contains the same Dirichlet series \(\sum\Lambda(n)^2n^{-s}\). Rodgers's small-error macroscopic theorem for smooth tests assumes RH. Those results give related prime-diagonal structure under distinct test-function or zero-location hypotheses. [Ford–Zaharescu, Compositio Mathematica 151 (2015), Theorem 1](https://arxiv.org/abs/1305.2520) and [Rodgers, QJM 64 (2013), 1197–1219](https://doi.org/10.1093/qmath/has024)

Ford and Zaharescu's Theorem 4 does supply a separate pair-statistical criterion equivalent to RH. Fix a primitive Dirichlet character of modulus \(q>1\), a nonnegative smooth compactly supported bump of integral one, and an ordinate \(\beta>1/2\). Take the authors' successive height and bump-width limits of the \(k\)-th derivative test against that character's positive-height zero pairs. Pointwise convergence in \(k\) for every \(\alpha>1/2\) is equivalent to RH for ζ. Their normalization contains \(2^{k+1}(k+1)!\), and the order of the three limits is part of the theorem. The Cauchy-weight transition considered here estimates a different fixed-order kernel. [Ford–Zaharescu, Theorem 4](https://www.ford126.web.illinois.edu/wwwpapers/linear.pdf)

BGSTB §3 warn about a lower-order error at \(x=c\log T\) in the former relative-error formulation and announce a Montgomery–Vaughan refinement on RH. The authors have posted the subsequent Volume III draft. Its Theorem 30.1, equation (30.8), applies on RH throughout \(1\le x\le T\) and uses the denominator \(T\log(T/(2\pi))/(2\pi)\). With \(k=\log(2\pi)\), converting its two main terms to this repository's normalization gives
\[
 \frac{(L-k)(L-k-2)}{Lx^2}+\frac{\log x}{L}.
\]
The draft remainder in the repository's normalization is \(O((\log(2x))^3/(\sqrt{x}L)+x\log\log(4x)/(TL))\). This confirms the signed transition correction on RH, the two fixed-interior polynomial exponents, and the \(O(\log\log T/L)\) endpoint independently of the present calculation. The draft's (30.10) retains both \(D(x)\) and \(S_3/x^2\) in an intermediate step. Its (30.12) retains the first two centered logarithmic terms. Replacing \(D(x)\) by \(\log x\) discards information relevant to the fourth displayed order at the transition. The unconditional complex-to-raw arguments in this note use the BGSTB positive-height contour identity. [BGSTB corrected §3, discussion preceding (3.3)](https://arxiv.org/html/2501.14545v3#S3) · [Montgomery–Vaughan, author-posted Volume III draft, Theorem 30.1 and (30.10)–(30.12)](https://personal.science.psu.edu/rcv4/Vol3/Vol3.pdf)

## Signed correction at order \(1/L\)

The \(O_A(1/L)\) remainder above also has an identifiable leading coefficient if the archimedean term is kept signed and the prime number theorem is used one term further. Under the same positive-height conventions,
\[
 F_{\rm raw}(T,\alpha)=e^{-c}+\frac{\log L+c}{2L}
 -\frac{2(1+\log(2\pi))e^{-c}}{L}
 +o_A(1/L).
\]
This section is a paper derivation. The stronger source-level hypotheses in this calculation have not been kernel-verified here.

To recover the missing archimedean constant, use BGSTB 2024, Lemma 1, proof of (2.2) from Landau's full explicit formula (2.3). The contour combination is \(xR(3/2+it)-x^{-1}R(-1/2+it)\). The right-hand logarithmic derivative combines with the truncated prime sum to produce the tail of \(A_2\). The left-hand finite prime sum produces the head. The remaining logarithmic derivative is \(-x^{-1}\zeta'/\zeta(-1/2+it)\). The pole and trivial-zero differences have the respective bounds \(O(\sqrt x/(1+t^2))\) and \(O(x^{-5/2}/(t+2))\) from Lemma 1. These terms are locally bounded on \(0\le t\le1\), and the combined expression at prime-power \(x\) follows by continuity of the weight. [BGSTB, Acta Arithmetica 2024, §2](https://doi.org/10.4064/aa230612-20-3)

Put \(k=\log(2\pi)\) and \(\chi(s)=\pi^{s-1/2}\Gamma((1-s)/2)/\Gamma(s/2)\). The logarithmic derivative of \(\zeta(s)=\chi(s)\zeta(1-s)\) at \(s=-1/2+it\) gives
\[
 -\zeta'/\zeta(s)=-\chi'/\chi(s)+\zeta'/\zeta(3/2-it).
\]
By the complex Stirling formula for the two digamma factors, \(-\chi'/\chi(s)=\log(t+2)-k+O(1/(t+1))\) on \(t\ge0\). The two limiting imaginary arguments of the logarithms cancel. This identity motivates the centered logarithmic signal \(A_1^*(t)=(\log(t+2)-k)/x\). Its companion \(A_3^*\) consists of \(x^{-1}\zeta'/\zeta(3/2-it)\) and errors with absolute bounds
\[
 O\!\left(\frac1{x(t+1)}+\frac{\sqrt x}{1+t^2}
       +\frac{x^{-5/2}}{t+2}\right).
\]
Consequently \(\int_0^T|A_3^*|^2dt\ll_A T/L\). Its absolute pairing with \(A_2\) is \(O_A(T\sqrt{(1+\log L)/L})=o_A(T)\). In the pairing with \(A_1^*\), absolute integration of the three displayed errors costs
\(O((1+L)^2/x^2+x^{-1/2}+(1+L)^2/x^{7/2})=o_A(T)\).
For the remaining \(x^{-1}\zeta'/\zeta(3/2-it)\) contribution, integrate its absolutely convergent Dirichlet series against \(\log(t+2)-k\). Every frequency is \(\log n>0\); integration by parts gives \(O((1+L)/\log n)\), and \(\sum_{n\ge2}\Lambda(n)/(n^{3/2}\log n)<\infty\). Its entire pairing with \(A_1^*\) is \(O((1+L)/x^2)=o_A(T)\). The cross term of \(A_1^*\) and \(A_2\) is also \(o_A(T)\): the previous cross estimate handles the log term and the constant subtraction is bounded by the same absolutely convergent prime sum. Thus every cross term and both cutoff terms in the original formula cost \(o_A(T)\) after recentering.

For the prime diagonal use \(S(y)=y\log y-y+o(y)\), obtained by partial summation with the classical quantitative prime number theorem for \(\vartheta(y)\) and the same proper-prime-power estimate as above. Substituting \(t\log t-t\) in the two integrals for \(D(x)\) gives head main terms \(-\frac12\log x+\frac34+O(x^{-2})\) and tail main terms \(\frac32\log x-\frac34\). The constants cancel. The \(o(t)\) error contributes \(o(1)\) uniformly for \(x\ge e^{-A/2}\sqrt L\) as \(T\to\infty\). The mean-value spacing error \(O(x\log(2x))\) is \(o_A(T)\). Hence \(M_2=T\log x+o_A(T)\).

Finally,
\[
 \int_0^T(\log(t+2)-k)^2dt
   = T L^2-2(1+k)TL+O(T).
\]
The omitted lower endpoint is bounded and the shift of the upper endpoint from \(T\) to \(T+2\) costs \(O((1+L)^2)\). Divide by \(x^2=e^c L\). Since the raw-to-complex difference is \(o_A(1/L)\), the signed coefficient carries over to the actual ordinates. In particular the residual after removing both \(e^{-c}\) and \(\alpha\) has order \(1/L\) with a nonzero uniform coefficient on compact \(c\)-intervals. The spectral normalization here is \(TL/(2\pi)\); substituting the actual zero count as normalization would change this coefficient.

## A fourth term for the complex statistic with the prime diagonal retained

Return to the centered decomposition above and set \(q_n=\Lambda(n)n^{-3/2}\), \(p_n=\Lambda(n)r_n(x)n^{-1/2}\). The prime signal \(A_2=-\sum_n p_n n^{-it}\) has negative frequencies. In the centered remainder the logarithmic derivative contributes \(B=x^{-1}\zeta'/\zeta(3/2-it)=-x^{-1}\sum_m q_m m^{it}\), with positive frequencies. The mixed integral \(A_2\overline B\) has frequencies \(-\log(nm)\). Only \(n,m\ge2\) occur, so \(\log(nm)\ge\log4\). Absolute convergence and \(\sum p_n\le x\sum q_n\) give the uniform bound
\[
 \left|\int_0^T A_2(t)\overline{B(t)}\,dt\right|
 \le \frac{2}{x\log4}\sum_n p_n\sum_m q_m
 \le \frac{2}{\log4}\left(\sum_{n\ge2}q_n\right)^2 .
\]
This signed estimate saves the entire Cauchy–Schwarz cost formerly assigned to this pairing. Its frequency orientation comes directly from the functional equation at \(-1/2+it\).

Write \(E=A_3^*-B\). The pointwise error above gives \(\int_0^T |A_2 E|\,dt\ll (1+L)+x^{3/2}+x^{-3/2}(1+L)\) by the same absolute series majorant for \(A_2\). Also \(|B|\le x^{-1}\sum q_n\), so \(\int |B E|\ll (1+L)/x^2+x^{-1/2}+(1+L)x^{-7/2}\) and \(\int |E|^2\ll x+x^{-2}\) for \(x\ge2\). The two pairings with \(A_1^*\) have the integration-by-parts estimates already given above. Every one of these cross integrals is bounded by a fixed power of \(1+L\) throughout the bounded-shift transition.

There is a diagonal contribution from \(|B|^2\). Define the positive absolute constant
\[
 S_3=\sum_{n\ge2}\frac{\Lambda(n)^2}{n^3}.
\]
The infinite integer mean-value inequality applies since \(\sum n q_n^2<\infty\) and gives \(\int_0^T |B(t)|^2dt=(T S_3+O(1))/x^2\). The mean square of \(A_2\) remains \(T D(x)+O(x\log(2x))\). Evaluating the real antiderivative gives
\[
 \int_0^T(\log(t+2)-k)^2dt
   =T\big[L^2-2(k+1)L+(k+1)^2+1\big]+O_k((1+L)^2),
 \qquad k=\log(2\pi).
\]
All errors within the signal integral are \(O_A((1+L)^m)\) for some fixed \(m\), while the positive-height cutoff in BGSTB (3.4) costs \(O(\sqrt T+x)\). Consequently the complex form factor has the uniform retained-diagonal expansion
\[
 F_\sharp(T,\alpha)
   = e^{-c}+\frac{D(x)-2(k+1)e^{-c}}{L}
     +\frac{\big[(k+1)^2+1+S_3\big]e^{-c}}{L^2}
     +O_A\!\left(\frac1{\sqrt T\,L}\right).
\]
The \(T\)-dependent \(D(x)\) is kept exactly. Substituting only the established prime number theorem remainder for \(D(x)-\log x\) gives an uncertainty larger than this fourth term. The current raw-to-complex comparison also has a larger uncertainty than \(L^{-2}\). Under the positive Selberg estimate its explicit order is \(O_A((\log L)^2/L^{3/2})\), and internally the Ingham estimate gives \(O_A((\log L)^4/L^{3/2})\). The fourth term in this section is an analytic consequence for the complex statistic with this prime diagonal. [BGSTB positive-height cutoff, §3, equation (3.4)](https://arxiv.org/html/2501.14545v3#S3.E4) · [BGSTB full contour formula, §2](https://doi.org/10.4064/aa230612-20-3) · [Montgomery–Vaughan mean-value inequality](https://doi.org/10.1112/jlms/s2-8.1.73)

Summing the prime powers explicitly gives \(S_3=\sum_p(\log p)^2/(p^3-1)\). After primes up to \(N\), monotonicity of \((\log t)^2/t^3\) for \(t\ge2\) bounds the positive tail by
\[
 \frac{(\log N)^2/2+(\log N)/2+1/4}{N^2(1-N^{-3})}.
\]
At \(N=10^6\), a 30-decimal-place interval sum and this tail bound give
\(9.21403028314 < (k+1)^2+1+S_3 < 9.21403028326\).
An independent Wolfram evaluation through \(p\le10^4\) gave the partial value \(S_3=0.1604839909452533\) with tail at most \(4.72704\times10^{-7}\).

If the denominator is changed from \(T L/(2\pi)\) to the actual zero count \(N(T)\) while the phase parameter \(u\) stays fixed, the Riemann–von Mangoldt formula gives \(2\pi N(T)/T=L-h+O(L/T)\) with \(h=1+\log(2\pi)\). Consequently the retained-diagonal complex statistic in this normalization equals
\[
 e^{-c}(1-h/L)+\frac{D(x)}{L-h}
   +\frac{(1+S_3)e^{-c}}{L(L-h)}
   +O_A\!\left(\frac1{\sqrt T\,L}\right).
\]
This gives a direct conversion for comparisons with results that average by \(N(T)\). [Hasanalizade, Shen and Wong, Journal of Number Theory 235 (2022), Theorem 1.1](https://www-math.nsysu.edu.tw/~pjwong/stuff/CountingRiemannZeros.pdf)

## Quantitative remainder with the prime diagonal retained

The exponential sum over primes is visible even when \(x\) is only of order \(\sqrt{\log T}\). Keeping \(D(x)\) in the approximation avoids using a prime number theorem error inside the form-factor estimate. In the preceding centered calculation, the \(A_2,A_3^*\) cross term costs \(O_A(T\sqrt{(1+\log L)/L})\). The two diagonal errors and every other cross term obey this bound as well. Combining it with the reflected Selberg Gram bound gives
\[
 F_{\rm raw}(T,\alpha)
 =e^{-c}+\frac{D(x)-2(1+\log(2\pi))e^{-c}}{L}
  + O_A\!\left(\frac{(1+\log L)^2}{L^{3/2}}\right).
\]
This expression uses the exact absolutely convergent von Mangoldt diagonal at the transition. It distinguishes the prime error from the raw-to-complex comparison.

A numerical exponent can also be retained after replacing \(D(x)\) by \(\log x\). Write \(V(y)=(\log y)^{3/5}(\log\log y)^{-1/5}\) for sufficiently large \(y\). Bellotti's prime number theorem after Theorem 1.3 gives \(\pi(y)-\operatorname{li}(y)\ll y\exp(-dV(y))\) with \(d=0.212579\) rounded downward. Partial summation with weight \((\log p)^2\) shows that for each \(0<d'<d\),
\[
 S(y)=y\log y-y+O_{d'}(y\exp(-d'V(y))).
\]
To bound the integral part of partial summation, split at \(y^\lambda\), with \(\lambda<1\) sufficiently close to 1. The first part is polynomially smaller than \(y\), and the second has \(V(t)\ge(\lambda^{3/5}+o(1))V(y)\). Logarithmic factors and proper prime powers are absorbed by the strict margin in \(d'\). The same split in the head integral for \(D(x)\) and monotonicity in its tail give \(D(x)=\log x+O_{d''}(\exp(-d''V(x)))\) for any \(0<d''<d\). Uniformly in \(|c|\le A\), \(V(e^{c/2}\sqrt L)/V(L)\to2^{-3/5}\). Consequently for every \(0<\kappa<2^{-3/5}\cdot0.212579\), a threshold approximately \(0.1402498\), the signed three-term raw expansion has remainder
\[
 O_{A,\kappa}\!\left(\frac{\exp(-\kappa V(L))}{L}\right).
\]
The implicit constants and admissible heights depend on the strict margin. Johnston and Yang's Theorem 1.4 supplies a fully explicit alternative for the prime input starting at \(y=23\), with exponential coefficient \(0.1853\) and a factor \(0.027(\log y)^{1.801}\) in the relative theta error. [Bellotti, JMAA 536 (2024), introduction following Theorem 1.3](https://arxiv.org/html/2306.10680v1#S1) and [Johnston and Yang, JMAA 527 (2023), Theorem 1.4](https://doi.org/10.1016/j.jmaa.2023.127460)

A later published result permits a closed exponent. Bellotti, *Bulletin of the London Mathematical Society* 58 (2026), e70442, Theorem 1.5 and Corollary 1.6, supply \(\vartheta(y)-y\ll y\exp[-d_*V(y)]\) with
\[
 d_*=\left(\frac{5^6}{2^2\,3^4\,48.0718^3}\right)^{1/5}
       =0.212579202120942\ldots .
\]
The same Corollary applies to the relative prime-counting error, and its multiplicative factor \(\exp(55/48.0718)\) is constant. To keep this precise exponent, retain the logarithmic factor introduced by partial summation. The identity for \(\sum_{p\le y}(\log p)^2\) and the elementary proper-power estimate give \(S(y)=y\log y-y+O(y\log y\,e^{-d_*V(y)})\). For all sufficiently large \(y\), \(yV'(y)=o(1)\), so integrating \(t\log t\,e^{-d_*V(t)}\) up to \(x\) costs \(O(x^2\log x\,e^{-d_*V(x)})\). The tail integral follows directly from monotonicity of \(V\). The two Stieltjes endpoint terms involving \(S(x)\) cancel with the closed-head/open-tail convention. Therefore
\[
 D(x)-\log x\ll(\log x)e^{-d_*V(x)} .
\]
At \(x=e^{c/2}\sqrt L\), uniformly for bounded \(c\), expansion of the logarithmic denominator gives
\[
 V(x)=2^{-3/5}V(L)
 \left(1+\frac{\log2}{5\log\log L}
       +O_A\!\left((\log\log L)^{-2}+(\log L)^{-1}\right)\right).
\]
The excess over \(2^{-3/5}V(L)\) grows faster than \(\log\log L\), and absorbs the prefactor \(\log x\). Hence the signed retained-order transition with \(D(x)\) replaced by \(\log x\) has the closed bound
\[
 O_A\!\left(\frac{\exp[-0.140249969432186\ldots\,V(L)]}{L}\right),
 \qquad 0.140249969432186\ldots=2^{-3/5}d_*.
\]
The exact symbolic constant determines this estimate. The source PNT is published. The weighted-diagonal and closed-exponent transfers are analytical derivations in this note. [Bellotti, Theorem 1.5 and Corollary 1.6](https://arxiv.org/html/2508.02041v1#S1) · [Author's publication record](https://sites.google.com/view/chiarabellotti/research-publications)

A separate elementary reduction suffices to recover the narrow prime mean square without a global Montgomery–Vaughan mean-value import. For \(x\ge2\), truncate at \(N=\lceil x^{16}\rceil\). Absolute summability of \(\Lambda(n)n^{-5/4}\) and \(r_n(x)n^{-1/2}\le x n^{-3/2}\) give full coefficient mass \(O(x)\) and tail mass \(O(xN^{-1/4})\). Replacing the series with the polynomial and replacing its diagonal with the full diagonal each cost \(O(Tx^2N^{-1/4})\). For \(1\le m<n\le N\), the logarithmic spacing is at least \(1/N\), so integration of each off-diagonal phase costs at most \(2N\). This gives
\[
 M_2=TD(x)+O(Tx^2N^{-1/4}+Nx^2).
\]
For \(x\asymp_A\sqrt L\) both remainders are \(o_A(T)\). This shortcut is specific to the narrow range.

## Fixed interior frequencies and the endpoint for the complex statistic

The preceding signed decomposition also applies uniformly before specializing \(x\) to the transition. Chebyshev's bound \(\psi(y)\ll y\) gives \(\sum_{n\ge2}p_n\ll\sqrt x\) for \(x\ge2\). The closed head is at most \(\psi(x)/\sqrt x\). Partial summation bounds the tail by \(x\int_x^\infty t^{-3/2}\,dt\) up to an absolute constant. Thus the pairing of \(A_2\) with \(E\) costs \(O(x+(1+L)/\sqrt x)\). The centered logarithmic pairings cost \(O((1+L)^2/x^2+(1+L)/\sqrt x)\), and the logarithmic-derivative diagonal costs \(O(1/x^2)\) beyond \(T S_3/x^2\). The remaining squared and mixed \(E\) terms cost \(O(x+(1+L)/x^2)\). The arithmetic estimate for the untwisted prime-power support just before (2.28) in Garunkštis–Paliulionytė bounds the prime mean-square error by \(O(x\log\log(4x))\). It applies on \([0,T]\) by the integer mean-value theorem; treating \([0,1]\) separately costs \(O(x)\). These bounds and the positive-height cutoff yield, with absolute constants and \(h=1+\log(2\pi)\),
\[
 2\pi\mathcal F_{(0,T]}(x)
 =T D(x)+\frac{T}{x^2}\big[(L-h)^2+1+S_3\big]
 +O\!\left(\sqrt T+x\log\log(4x)+\frac{(1+L)^2}{x^2}
                         +\frac{1+L}{\sqrt x}\right),
 \quad 2\le x\le T.
\]
The arithmetic equalities for \(D(x)\) and \(S_3\), and the signed mixed estimate, refer to the actual prime coefficients. The distinct character theorem in the cited paper has a conductor restriction; it is the untwisted mean-value and prime-gap calculation that is used here. [BGSTB 2024, §2](https://doi.org/10.4064/aa230612-20-3) · [BGSTB corrected §3](https://arxiv.org/html/2501.14545v3#S3.E4) · [Garunkštis–Paliulionytė, Lemmas 2.3–2.4 and the calculation before (2.28)](https://web.math.pmf.unizg.hr/glasnik/forthcoming/pGM7479.pdf)

Fix \(0<a\le b<1\), put \(x=T^\alpha\), and let \(V(y)=(\log y)^{3/5}(\log\log y)^{-1/5}\). The quantified diagonal prime number theorem above, together with \(V(T^\alpha)/V(T)=\alpha^{3/5}+o_{a,b}(1)\), gives
\[
 \sup_{\alpha\in[a,b]}|F_\sharp(T,\alpha)-\alpha|
   \ll_{a,b,\kappa}\frac{\exp[-\kappa V(T)]}{\log T},
 \qquad 0<\kappa<0.212579\,a^{3/5}.
\]
Because \(b<1\), \(\log\alpha\le\log b<0\) throughout the interval. The identity \(V(T^\alpha)=\alpha^{3/5}V(T)(1+\log\alpha/\log\log T)^{-1/5}\) supplies a uniform excess of order \(V(T)/\log\log T\) beyond \(a^{3/5}V(T)\). By the closed Bellotti estimate above, the previous interior inequality also holds at the exact endpoint \(\kappa=d_*a^{3/5}\).

The remaining terms decay as powers of \(T\) on this fixed interval. At \(\alpha=1\), the prime-power spacing bound instead gives
\[
 F_\sharp(T,1)=1+O\big(\log\log(4T)/\log T\big).
\]
These are paper derivations for the corrected complex-zero statistic. For a fixed nonzero normalized frequency, the currently proved horizontal quartic majorant grows like \(\alpha^4L\). The fixed-support conclusions therefore require additional information to transfer them to the raw-ordinate PCC statistic. [Bellotti, prime number theorem after Theorem 1.3](https://arxiv.org/html/2306.10680v1#S1)

Under RH the raw and complex statistics agree, and the conditional bound \(\vartheta(y)=y+O(\sqrt y\log^2 y)\) gives \(D(x)=\log x+O(x^{-1/2}\log^3(2x))\) by the same head and tail partial summation. Thus at any fixed \(0<\alpha<1\) the preceding bound yields
\[
 F_{\rm raw}(T,\alpha)-\alpha
 \ll_\alpha T^{-\alpha/2}L^2
   +T^{\alpha-1}\frac{\log L}{L}
   +\frac{T^{-1/2}}{L}+T^{-2\alpha}L .
\]
The sharper RH theorem in Montgomery–Vaughan’s Volume III draft already contains the two principal terms on the right and omits the additional cutoff remainder. Here RH also supplies the prime number theorem error. The two principal polynomial exponents \(\alpha/2\) and \(1-\alpha\) coincide at \(\alpha=2/3\). [Schoenfeld, Mathematics of Computation 30 (1976), Theorem 10](https://doi.org/10.1090/S0025-5718-1976-0457374-X)

## Which Hilbert constant is needed

For distinct real frequencies with individual nearest-neighbor gaps \(\delta_j\), the repository proves the diagonal weighted Hilbert inequality with coefficient \(13\). The best published upper bound located for this general inequality is Preissmann's \(C=\pi\sqrt{1+(2/3)\sqrt{6/5}}\approx4.1324743621\). Two endpoints contribute \(2C\) in the Dirichlet-polynomial mean square. Rodgers's 2026 preprint shows that the optimal constant for *arbitrary irregular frequencies* is strictly larger than \(\pi\). This lower bound concerns the full class of configurations and says nothing about sharpness on the integer-log sequence alone. [Preissmann, L'Enseignement Mathématique 30 (1984), 95–113](https://doi.org/10.5169/seals-53823) and [Rodgers, arXiv:2608.12315](https://arxiv.org/abs/2608.12315)

At positive integer frequency \(n\), the smallest gap to all other integer logarithms is \(\log(1+1/n)\). For \(q\ge1\), the derivative of \(\log q-2(q-1)/(q+1)\) is \((q-1)^2/[q(q+1)^2]\). Applying the inequality to \(q=1+1/n\) shows \(\delta_n^{-1}\le n+1/2\). The offset is asymptotically tight since \(1/\log(1+1/n)=n+1/2+O(1/n)\). Consequently the infinite mean-square remainder for coefficients \(a_n\), assuming \(\sum |a_n|<\infty\) and \(\sum n|a_n|^2<\infty\), is bounded by \(2C\sum(n+1/2)|a_n|^2\). Taking \(C=13\) uses an existing repository proof and gives a coefficient \(39\) after the coarser replacement \(n+1/2\le3n/2\). The older spacing estimate \(1/(2n)\) produced \(52\) in this normalization. Keeping the support restricted to prime powers can lower spacing costs further.

For \(a_n=r_n(x)\Lambda(n)/\sqrt n\), the finite-to-infinite reduction uses \(n|a_n|^2\le (2/e)x^2\Lambda(n)/n^{3/2}\). Indeed \(\log n/\sqrt n\le2/e\), by applying \(\log t\le t-1\) at \(t=\sqrt n/e\). The majorant is summable. The checked repository version gives \(|M_2-TD(x)|\le (78/e)x^2\sum_{n\ge2}\Lambda(n)n^{-3/2}\) uniformly in \(T\). This is enough to deduce the centered transition from a scalar prime-diagonal PNT input. The following weighted-diagonal argument improves this to \(O(x\log(2x))\) on the full arithmetic cutoff range.

The scalar diagonal PNT also recovers the global \(O(x\log(2x))\) arithmetic mean-value error without separately estimating the summatory function of \(\Lambda^2\). Write \(p_n(y)=\Lambda(n)r_n(y)/\sqrt n\). For \(y\ge\max(x,n)\), \(|p_n(y)|^2=\Lambda(n)^2n/y^2\). Consequently
\[
 n|p_n(x)|^2\le3x^2\int_{\max(x,n)}^\infty
      \frac{|p_n(y)|^2}{y^2}\,dy .
\]
For \(n\ge x\) there is equality. For \(n\le x\) the right side is \(\Lambda(n)^2n/x\), which dominates \(\Lambda(n)^2 n^2/x^2\). Tonelli and the uniform bound \(D(y)\le\log y+C\) on \(y\ge x\ge2\) give
\[
 \sum_n n|p_n(x)|^2
 \le 3x^2\int_x^\infty D(y)y^{-2}\,dy
 \le 3x(\log x+1+C).
\]
The factor \(3\) is attained by the single-frequency majorization at \(n=x\). The mean-value bound then applies with whichever admissible Hilbert constant is supplied. Additional prime-power spacing information can sharpen this further.

The Lean declarations `weighted_primeWeight_sq_add_surplus`,
`weighted_primeWeight_sum_le_of_diagonal`, and `primeMeanSquare_error_le_linear_log`
formalize the coefficient identity, its summed bound, and the mean-value estimate.
`primeSignalMeanSquareSource_unconditional` supplies the arithmetic premise in the
BGSTB transition. For every fixed \(0<\alpha<1\),
`primeSignalEnergy_tendsto_subunit` yields
\[
   \frac{M_2(T,T^\alpha)}{T\log T}\longrightarrow \alpha.
\]
The complex pair sum retains its signed cutoff residual, and transfer to ordinate
pairs also requires horizontal control. [Lean source](../Analysis/MontgomeryPrimeMeanSquare.lean)

## Direct numerical check of the raw normalization

For \(c=0\) set \(T=\gamma_N\), retain every pair with \(i,j\le N\), and compute \((2\pi/(T\log T))\sum_{i,j}4\cos(u(\gamma_i-\gamma_j))/(4+(\gamma_i-\gamma_j)^2)\) with Wolfram's \(\operatorname{ZetaZero}\). The third column is the direct raw statistic and the last column is the signed scaled residual.

| \(N\) | \(T\) | \(F_{\rm raw}\) | \(L(F_{\rm raw}-1-\alpha)\) |
|---:|---:|---:|---:|
| 32 | 105.446623 | 0.336089323 | −3.86194704 |
| 64 | 169.911976 | 0.378932335 | −4.00742392 |
| 128 | 283.211186 | 0.413481534 | −4.17708712 |

The asymptotic scaled coefficient for this normalization is \(-2(1+\log(2\pi))\approx-5.67575413\). The small heights in the table test the cutoff, the phase and the normalization. The analytic arguments supply the limiting statement.

At these heights \(2<x=\sqrt L<3\), so only the prime power 2 lies in the closed head of the retained diagonal. The exact identity is \(D(\sqrt L)=L S_3+(\log2)^2(2/L-L/8)\). A separate Wolfram evaluation of the fourth-term approximation for the corresponding complex statistic gave the following comparison with the finite sums.

| \(N\) | \(D(\sqrt L)\) | Fourth-term approximation | Direct sum minus approximation |
|---:|---:|---:|---:|
| 32 | 0.67409394 | 0.35090049 | −0.01481117 |
| 64 | 0.70284144 | 0.38101681 | −0.00208447 |
| 128 | 0.73721908 | 0.41436049 | −0.00087896 |

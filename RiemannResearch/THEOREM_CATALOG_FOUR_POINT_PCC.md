# Recovering positive-gap PCC from fourth-order GUE tests

Write \(L_T=\log T/(2\pi)\). Sample \(t\) uniformly in \((0,T]\) and use the unfolded coordinates \(L_T(\gamma-t)\) of the zero occurrences with \(0<\gamma\le T\). Fix \(q\in\mathbb Q_{>0}\) and \(H=n+12\). Take the disjoint intervals \(A=[0,q)\) and \(B=[q,q+H)\). Write \(X,M\) for the two counts and \((m)_j=m(m-1)\cdots(m-j+1)\).

## The two arithmetic tests

Define \(S(x)=\sin(\pi x)/(\pi x)\), with \(S(0)=1\), and \(\rho_j(\mathbf x)=\det[S(x_i-x_k)]_{i,k=1}^j\). For each fixed \(q,H\), the sufficient fourth-order inputs are
\[
\begin{aligned}
\mathbb E_T[(M)_4]/H^4 &\longrightarrow H^{-4}\int_{B^4}\rho_4(\mathbf x)\,d\mathbf x,\\
\mathbb E_T[(X)_2(M)_2]/H^2 &\longrightarrow H^{-2}\int_{A^2\times B^2}\rho_4(\mathbf x)\,d\mathbf x .
\end{aligned}
\]
Both numerators sum over four distinct occurrence labels. Distinct labels at the same ordinate are retained. These bounded-box tests follow from vague convergence of the full fourth factorial measure because the target density is continuous and the box boundaries have Lebesgue measure zero. The list of required widths is countable. This application uses the randomly translated finite cutoff specified above.

On the sine-process side, the mean count in \(B\) equals \(H\). The matrix defining \(\rho_4\) is the Gram matrix of four unit vectors \(v_x(s)=e^{2\pi ixs}\) in \(L^2[-1/2,1/2]\). Its determinant lies between zero and one, so the first normalized target is at most one. The local sine pair mean is \(\int_{A^2}(1-S(x-y)^2)\,dx\,dy\). These facts specify the comparison-law inputs to the Lean theorem.

For disjoint windows the covariance of the pair counts equals the integral over \(A^2\times B^2\) of
\[
\rho_4(x_1,x_2,x_3,x_4)-\rho_2(x_1,x_2)\rho_2(x_3,x_4).
\]
On the model side, \(\rho_4(x,y,R,2R)\to 1-S(y-x)^2\) as \(R\to\infty\): the two distant points separate from each other and from both fixed points. The pointwise statement for the model and the integrated statement for actual zero statistics use different arguments. [Four-by-four sine determinant](Analysis/DysonFourPointCluster.lean)

## Removing two labels

Put \(e=1/H\), \(Z=eM\), \(W=e^2(M)_2\), and \(F=e^4(M)_4\). For any nonnegative integer count and \(H\ge12\), Lean proves the pointwise inequality
\[
 (W-1)^2\le(1+12e)F+3+12e-(4-2e)Z .
\]
The physical first moment tends to one by the actual zero-count mean at fixed widths \(q+H\) and \(q\). Combining this with the pure fourth-order test gives \(\limsup_{T\to\infty}\mathbb E_T(W-1)^2\le26/H\). The same estimate holds under the reference sine law. For \(P=(X)_2\), the elementary bound \(P^2\le36+6(X)_4\) shows that boundedness of the local fourth factorial moment suffices. Full fourth-correlation convergence on \(A^4\) supplies it. Fujii’s raw fourth-moment estimate also gives \(\sup_{T\gg1}\mathbb E_T P^2<\infty\) at each fixed \(q\). Cauchy–Schwarz now bounds \(|\mathbb E_T P-\mathbb E_T(PW)|\) by a constant depending on \(q\) times \(H^{-1/2}\) in the height limsup. The proof in Lean uses the equivalent weighted quadratic inequality. The mixed fourth-order test transfers \(\mathbb E(PW)\) at fixed \(H\). Letting \(H\) tend to infinity recovers the local pair mean.

Finally \(X^2=X+(X)_2\). The intensity and the recovered pair mean give the sine second moment at all positive rational widths. The existing theorem `positiveGapPCC_of_sineWindowMoment` gives ordinary positive-gap PCC uniformly on compact positive width intervals. Its treatment of ties uses the entire window second moment. The same input gives density one of simple critical-line zeros in `simple_critical_density_of_four_point_windows`. No simplicity or critical-line premise enters this argument.

## Scope and verification

[Comparison of factorial counts at orders four and two](Analysis/FourPointFactorialComparison.lean) · [Application to actual zero windows](Analysis/MontgomeryFourPointWindows.lean) · [Earlier sine-window implication](Analysis/MontgomeryWindowPairCorrelation.lean)

The Lean application quantifies over a comparison law and specifies its intensity, normalized fourth-factorial bound, local pair mean and integrability. The sine determinantal process satisfies these conditions by its correlation formulas. The arithmetic hypotheses on the actual ordinates are the two fourth-order limits and a bounded local fourth factorial moment. Full fourth-order convergence gives all three. The verified implication `boundedLocalFourthFactorial_of_fujii` also obtains the local bound from Fujii’s fixed-width moment estimate. The required limits for the actual zeros remain open here. A bound on the raw fourth moment alone supplies no four-point correlations. In particular \(X^4=(X)_4+6(X)_3+7(X)_2+X\).

[Arias de Reyna and Rodgers, GUE correlation hypothesis and Fujii's count bounds](https://arxiv.org/abs/2311.13441) · [Soshnikov, determinantal point fields](https://arxiv.org/abs/math/0002099)

## The three GLSS counts

Write \(N=N(T)\) for the total number of zero occurrences in \((0,T]\), \(N_s\) for the number of simple zeros at all real parts, and \(N_0^s\) for the number of simple critical-line zeros. The checked bijection in `simpleZeroCount_eq_card_copies` identifies ordinary simple zeros with their unique occurrence labels. Let \(H_T(\gamma)\) count every occurrence at a given ordinate and sum over distinct ordinates. For every real cutoff,
\[
2N-\sum_{\gamma}H_T(\gamma)^2\;\le\;N_0^s\;\le\;N_s\;\le\;N.
\]
The first inequality uses signed integer subtraction. An off-line zero has a reflected companion, while a multiple zero contributes at least two labels at its ordinate. Thus a singleton ordinate carries a simple critical-line zero. [Finite comparison and singleton proof](Analysis/GLSSZeroCounts.lean)

`glss_counts_of_horizontal_multiplicity` proves that \(\sum_\gamma H_T(\gamma)^2\sim N\) implies \(N_0^s\sim N\) and \(N_s\sim N\). Under `FourPointWindowTests`, `glss_counts_of_four_point_windows` gives ordinary positive-gap PCC and all three asymptotic equivalences with the actual \(N(T)\) denominator. This route has no separate Fujii hypothesis. The fourth-order zeta limits remain open.

For ordinary positive-gap PCC by itself, the paper uses Fujii's unconditional second-moment estimate. The Lean theorem `fujiiArgumentIncrementUpper_of_prop_two` specializes equation (5.6) to \(U=R/L_T\), with \(L_T=\log T/(2\pi)\), for the actual count discrepancy. The resulting logarithmic bound implies the required one-sided triangle bound in `shortWindowUpper_of_fujiiArgumentIncrement`. The combination with PCC is `glss_counts_of_positiveGapPCC`. **Open formalization obligation:** a proof of the Fujii estimate for the zeta discrepancy without an analytic hypothesis. [Goldston, Lee, Schettler and Suriajaya, §§5, 7–8](https://arxiv.org/html/2503.15449v4#S5)

# Strict microscopic zero pairs, local unfolding and the Dyson covariance

Put \(L_T=\log T/(2\pi)\), \(D_T=T L_T\), and let \(A_T(w)\) count all ordered pairs of nontrivial zero occurrences with both ordinates in \((0,T]\) and \(0<\gamma'-\gamma\le w\). This includes all neighbor ranks. Strict positivity omits every equal-ordinate pair. Define \(P_T(q)=A_T(q/L_T)/D_T\).

## Pair counts at the mean-spacing scale

For \(s=3/2-2^{-1/2}\cot(2^{-1/2})\), the cumulative simple critical-line theorem supplies at least a proportion \(s\) in the liminf. Distinct simple critical-line occurrences have different ordinates. Packing them in an interval of length \(T\) gives \(\liminf P_T(q)\ge s-1/q\). The repository also has the higher-rank bound \(k s-k(k+1)/(2q)\) for each nonnegative integer \(k\). The new bound applies when \(T_i\to\infty\) and \(L_{T_i}w_i\to q>0\) on any filter. The alternating Taylor bounds through degrees seven and eight give the sharper exact certificate \(s>1345001/2000000=0.6725005\). Consequently \(P_T(2)>345001/2000000\) and \(P_T(3/2)>35003/6000000\) eventually. Compact Orbit already records the bound \(7/1200\) at width \(3/2\), even for strict first neighbors. The finite packing bound in a selected band uses only its own length and counts pairs inside it. A cumulative density theorem by itself does not give that density in each moving short band.

Fujii's microscopic moment estimate implies a first-moment bound for the Cauchy rows. At every finite cutoff, the raw count is bounded by the total Cauchy row mass times \(1+(w\log T)^2\). The first row moment therefore gives \(A_T(w)\ll_Q N(T)\) for \(0\le w\log T\le Q\). The formal upper-bound theorem takes the analytic input `FujiiMicroscopicRowMoments` explicitly. Together these estimates give \(A_T(w_T)\asymp_q T\log T\) whenever \(L_Tw_T\to q>1/s\). In particular \(q>2000000/1345001\) suffices. A positive lower bound on each cutoff count is compatible with many two-point laws.

[Alpöge and Furman, Theorem A, preprint](https://arxiv.org/html/2608.13637v2) · [Fujii's estimate and the Cauchy-row consequence, Lamzouri, Lemmas 2.2–2.3](https://arxiv.org/html/2611.14486v1)

## Exact covariance criterion

Let \(C_T=\sum_y m_T(y)^2\), with all occurrences of ordinate \(y\) counted in \(m_T(y)\). Let \(V_T(q)\) be the repository's translated count variance, centered at the exact finite-height mean \(\mu_T(q)=qN(T)/D_T\). The sine kernel, after normalization to intensity one, gives the two-point density \(1-\operatorname{sinc}^2(\pi u)\), where \(\operatorname{sinc}(x)=\sin(x)/x\). Put
\[
K_T(q)=V_T(q)-q C_T/D_T,\qquad K_{\rm sine}(q)=-2\int_0^q(q-u)\operatorname{sinc}^2(\pi u)\,du .
\]
For each fixed positive width and all sufficiently large cutoffs,
\[
K_T(q)-K_{\rm sine}(q)=q^2-\mu_T(q)^2
+2\int_0^q\left[P_T(u)-\int_0^u(1-\operatorname{sinc}^2(\pi v))\,dv\right]du.
\]
Strict positive-gap PCC is equivalent to convergence of \(K_T(q)\) to \(K_{\rm sine}(q)\) for every positive rational \(q\). No separate estimate on \(C_T\) is needed in this equivalence. The analytic limit for the actual zeros is open here. Compact Orbit expresses the same open arithmetic transfer as the loss of mass from anchoring a translated window at an actual zero: the translated mass tends to \(q\) and the prime energy tends to the integrated sinc square. Its spectral rigidity result requires a determinantal spectral representation for the same subsequential pair law. The short-prime increment product in the microscopic Selberg trace note is asymptotic to \((q\eta)^2\) at fixed \(q\) and cutoff \(T^\eta\), with \(\eta\to0\) and \(\eta\log T\to\infty\). Its decay leaves the fixed-width covariance of the full count undetermined.

[Compact Orbit](https://riemann-compact-orbit.dreamymeter1.chatgpt.site/current-proofs.html) · [Microscopic Selberg trace and prime covariance](RIEMANN_MICROSCOPIC_SELBERG_TRACE_20261125.md) · [Goldston, Lee, Schettler and Suriajaya](https://doi.org/10.1112/mtk.70127)

## If the zero count itself has the sine-process limit

Sample the starting height uniformly in \((0,T]\) and write \(X_T(q)\) for the multiplicity-preserving count in the translated interval of physical width \(q/L_T\), with the same finite cutoff as above. Its exact mean tends to \(q\). Mean convergence gives intensity one. The assertion that the law of \(X_T(q)\) tends to the sine-process count law is stronger. The theorem `pcc_and_simple_density_of_weak_count_laws` needs only the one-interval weak laws for positive rational \(q\), their sine second moments, and the fixed-width Fujii fourth-moment bound. It yields both strict PCC and density one of simple critical-line zeros.

For the bounded continuous test \(f_M(x)=\min(x^2,M)\), one has \(0\leq x^2-f_M(x)\leq x^4/M\). Hence passage from weak convergence to the second moment costs at most \(C_q/M\) uniformly in large heights. Dominated convergence in the target law removes the cap. For the unit-intensity sine process the resulting second moment is
\[
q^2+q-2\int_0^q(q-u)\operatorname{sinc}^2(\pi u)\,du .
\]
The argument allows ties at finite height and makes no RH assumption. This establishes the implication from weak count laws. Establishing the actual weak limits at fixed microscopic width is the outstanding arithmetic problem. The full point-process GUE hypothesis asks for joint laws as well.

[Lean theorem on weak window-count laws](Analysis/MontgomeryWindowCountLaw.lean) · [Arias de Reyna and Rodgers on equivalent formulations of the GUE hypothesis](https://arxiv.org/abs/2311.13441)

## Moving heights and the Mellin comparison

For \(T_i\to\infty\), \(T_i\le c_i\le2T_i\), and \(Q_i\to q>0\), put \(w_i=2\pi Q_i/\log(c_i/(2\pi))\). Then \(L_{T_i}w_i\to q\), even if \(c_i/T_i\) oscillates. Subtracting the common center from both unfolded ordinates cancels exactly. Under PCC these physical widths give the stated sine integral for counts up to \(T_i\). The Mellin kernel's unitary coordinate change and phase gauge preserve the determinantal correlations of that model. Identifying the corrected covariance for zeta ordinates requires the arithmetic limit above. A density-one theorem on simple critical zeros still allows exceptions. The repository proves that adding a duplicate at one fixed actual ordinate is eventually invisible to every bounded strictly positive gap test. [Fixed-duplicate theorem](Analysis/MontgomeryFixedDuplicate.lean)

[Finite band packing](Analysis/MicroscopicOrdinatePacking.lean) · [Actual pair counts and Fujii comparison](Analysis/MontgomeryMicroscopicPacking.lean) · [Rational lower bounds](Analysis/MontgomeryTaylorMicroscopicDensity.lean) · [Covariance criterion](Analysis/MontgomeryMicroscopicCovariance.lean) · [Dyadic local unfolding](Analysis/MontgomeryLocalUnfolding.lean)

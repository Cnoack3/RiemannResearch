# Sparse deletion and the ordinary ordinate transfer

The following paper-level deductions use the cumulative multiset of nontrivial zeta zeros with \(0<\gamma\le T\). Every occurrence counts. Write \(N=N(T)\), \(L=\log T\), \(X_i=L|\beta_i-1/2|\), and let \(\mu\) put mass \(1/N\) on each occurrence. Fix a real even \(f\in C_c^2([-\theta,\theta])\). Define

\[
 G_T(B)=\frac1N\sum_{i,j\in B}
 \widehat f\!\left(i(\rho_i-\rho_j)L/(2\pi)\right)
 \frac4{4-(\rho_i-\rho_j)^2}.
\]

## The pair measure

Put \(k_{ij}=(1+L^2(\gamma_i-\gamma_j)^2)^{-1}\), \(K_i=\sum_jk_{ij}\), and give the ordered pair \((i,j)\) mass \(k_{ij}/N\) under \(\nu\). Lamzouri's Lemma 2.3 gives \(\mathbb E_\mu K^q\ll_q1\) for every fixed positive integer \(q\). Integration by parts twice in the Fourier transform and \(|4/(4-z^2)|\le4/3\) for \(|\Re z|\le1\) give a termwise majorant \(C_f k_{ij}\exp(\theta(X_i+X_j))\). See [Lamzouri, Lemmas 2.1–2.3, equations (3.4), (3.8), and Proposition 3.2](https://arxiv.org/html/2611.14486v1).

Let \(E\) have fraction \(\delta\), let \(D\) consist of the ordered pairs touching \(E\), and put \(Y_{ij}=(X_i+X_j)/2\). For any integer \(q>1\), put \(d=1-1/q\). For every collection \(S\) of occurrences, Hölder gives \(\nu(i\in S\text{ or }j\in S)\le2\mathbb E_\mu[1_S K]\ll_q\mu(S)^d\). In particular,

\[
 \nu(D\cap\{Y>v\})\ll_q \min\{\delta,\mu(X>v)\}^d.
\]

The implication \(Y>v\Rightarrow X_i>v\text{ or }X_j>v\) suffices. All constants are independent of the exceptional subset. The subset can vary with height and need not be reflection invariant for this absolute estimate.

## Fixed-support improvement

Set \(a_*=8/7\). Conrey–Baluyot and reflection give \(\mu(X>v)\ll_a e^{-av}\) for every fixed \(a<a_*\) with \(a>0\). Write \(c=2\theta\). For \(0<c<a_*\) and \(0<e<1-c/a_*\), choose fixed \(a<a_*\) and integer \(q\) with \(e<d-c/a\). Layer cake gives

\[
 |G_T(Z)-G_T(Z\setminus E)|
 \ll_{f,q,a}\delta^d+
 c\int_0^\infty e^{cv}\min(\delta,e^{-av})^d\,dv
 \ll_{f,e,\theta}\delta^e.
\]

Split the integral at \(v=a^{-1}\log(1/\delta)\). The zero-deletion case follows directly. In the range \(1/2<\theta<4/7\), Lamzouri's Proposition 3.2 states the power \((1-7\theta/4)/8\), with an additional analytic asymptotic error \(O_f(L^{-1/2})\). The direct estimate admits every fixed power below \(1-7\theta/4\). Adding Lemma 3.1 supplies the same analytic error for approximation by the limiting main term. This comparison concerns the explicit exponent in Proposition 3.2. It does not establish priority over every other argument.

## Polynomial rarity across the support boundary

The sharp Ingham–Chourasiya–Simonič log profile \(N(\sigma,T)\ll T^{Q(\sigma)}L^{2+Q(\sigma)}\), where \(Q(\sigma)=3(1-\sigma)/(2-\sigma)\), supplies a second tail. For \(\sigma=1/2+v/L\) one has \(1-Q=2(v/L)/(3/2-v/L)\ge4v/(3L)\). Divide by \(N\asymp TL\), use \(Q\le1\), and reflect. Uniformly over \(v\ge0\),

\[
 \mu(X>v)\ll L^2e^{-bv},\qquad b=4/3.
\]

See [Chourasiya and Simonič](https://arxiv.org/abs/2507.15184) and [the repository's Littlewood density module](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/ActualInghamLittlewoodDensity.lean).

Suppose \(\delta\le L^{-p}\) for fixed \(p>0\). If \(c=2\theta<b\), for every \(\eta>0\) the absolute deletion error is \(O_{f,p,\theta,\eta}(L^{-h+\eta})\), where

\[
 h=\inf_{x\ge0}\left[\max\{p,a_*x,bx-2\}-cx\right].
\]

Indeed, insert the two tails into pair-measure layer cake and put \(v=x\log L\). Its integrand, apart from constants and the Jacobian, is \(L^{-d\max(p,ax,bx-2)+cx}\). Choose \(d\) near one with \(db>c\), and \(a<a_*\) near \(a_*\). The linear pieces have at most two switches. Beyond a fixed large \(x\) there is geometric decay in \(x\log L\). On the fixed compact remainder the exponent tends uniformly to the stated exponent as \((d,a)\to(1,a_*)\). Absorb the Jacobian into \(L^\eta\). The limit constants can depend on \(\eta\).

| Rarity and support | Power \(h\) |
| --- | --- |
| \(0<p\le12,\quad c\le 8/7\) | \(p(1-7c/8)\) |
| \(0<p\le12,\quad 8/7\le c<4/3\) | \(12-21c/2\) |
| \(p\ge12,\quad 0<c<4/3\) | \(p-(3c/4)(p+2)\) |

The two density lines intersect at \(x=21/2\) and at height 12. For \(p\le12\) the switches are \(p/a_*\) and \(21/2\). For \(p\ge12\), the only switch on the upper envelope is \((p+2)/b\). Minimizing the affine expressions on these intervals proves the table, including the shared edges.

At \(\theta=4/7\), every \(p>12\) gives vanishing deletion error. Throughout \(4/7<\theta<2/3\), the sufficient condition is

\[
 p>\frac{6\theta}{2-3\theta}.
\]

For example, \(\theta=4/7,p=14\) gives \(h=2/7\), while \(\theta=3/5,p=20\) gives \(h=1/5\). At equality the envelope gives \(h=0\). These are boundaries for deductions from the stated upper profiles and arbitrary fixed local moments. They are not obstructions for actual zeta zeros. For example the scalar envelope allows a packet of proportion \(L^{-m}\) at \(Y=x\log L\), \(m=\max(p,a_*x,bx-2)\), attaining the logarithmic exponent \(cx-m\) for the absolute majorant. At \(c=b\) any fixed \(p\) leaves this envelope exponent equal to 2 on its final linear piece. A genuinely stronger tail or additional cancellation would be needed for that boundary by this argument. The conclusion above compares sparse-subset and full complex tests, and by BGSTB gives the limiting low-support formula for the retained complex tests. It is not a full ordinary-ordinate PCC.

## Centered ordinary-ordinate comparison

Set \(\epsilon_T=\mathbb E_\mu X^2\). For all fixed \(0<\theta<4/7\) and fixed \(0<e<1-7\theta/4\), the normalized difference between the full complex statistic and its Lorentz-weighted ordinary-ordinate counterpart is \(O_{f,\theta,e}(\epsilon_T^e)\). To verify the second-order cancellation, fix a vertical gap \(y=\gamma_i-\gamma_j\), and let

\[
 H(s)=\widehat f\bigl((-Ly+is)/(2\pi)\bigr)\,4\big/\bigl(4-(s/L+iy)^2\bigr).
\]

Take \(L\ge4\). For \(|s|\le2\), each of the first two derivatives of the entire transform in \(s\), and the transform itself, is \(O_f(k_{ij})\) by two integrations by parts applied to \(\alpha^j f(\alpha)\), \(j=0,1,2\). The rational factor and its first two \(s\)-derivatives are uniformly bounded since \(|s/L|\le1/2\) keeps distance from both poles. Thus \(H''(s)=O_f(k_{ij})\) uniformly. Reflect both zeros simultaneously, which preserves ordinate and multiplicity and sends \(s=L(\beta_i-\beta_j)\) to \(-s\). The half-sum of \(H(s)\) and \(H(-s)\) differs from \(H(0)\) by \(O_f(k_{ij}(X_i^2+X_j^2))\) whenever both marks are at most 1. On the complementary pairs the absolute Fourier bound applies, and \(m_i+m_j\ge1\) for \(m_i=\min(X_i^2,1)\). In both regimes the error is bounded by \(C_f k_{ij}(m_i+m_j)e^{cY}\).

The measure \(d\nu_m=(m_i+m_j)d\nu\) has total mass \(O_q(\min(1,\epsilon_T)^d)\) by Hölder and \(m_i\le1\). Its \(Y\)-tail is \(O_q(\mu(X>v)^d)\) since \(m_i+m_j\le2\). Repeat the same layer-cake argument with \(\min(1,\epsilon_T)\) replacing \(\delta\). This proves the stated transfer and also the preceding logarithmic table whenever \(\epsilon_T\le L^{-p}\). Unweighting the ordinary ordinate statistic costs \(O_f(L^{-1})\) by the shell bound in the existing research note. Even the condition \(\epsilon_T\to0\) is an open analytic premise. See [MellinModularQuadraticAttempt20261118, §7](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/MellinModularQuadraticAttempt20261118.md).


## Unconditional inverse-logarithmic abundance of smaller gaps

Let \(d_T(\lambda)\) be the proportion of internal consecutive gaps at height
\(T\) of size at most \(2\pi\lambda/\log T\), counting all zero occurrences.
Fix \(4/7\le\theta<2/3\). Suppose a normalized real even Schwartz test
has nonnegative frequency values, nonpositive Fourier transform on
\(|u|>\lambda\), and excess
\(f(0)+2\int_0^\theta \alpha f(\alpha)\,d\alpha>1\). Then
\[
 (\log T)^p d_T(\lambda)\longrightarrow +\infty
 \qquad \left(p>\frac{6\theta}{2-3\theta}\right).
\]

Indeed, if the assertion failed there would be a fixed finite \(C>0\)
and heights tending to infinity with \(d_T(\lambda)\le C(\log T)^{-p}\).
Mark both endpoints of every qualifying internal gap. The deletion
fraction is at most \(2C(\log T)^{-p}\). Every same-height block of size at
least two is removed in full, so the survivors are simple critical zeros
and are separated by more than the stated threshold. Choose
\(\theta<\theta'<2/3\) so close to \(\theta\) that the strict inequality
for \(p\) still holds at \(\theta'\). A nonnegative smooth cutoff of
\(f\), equal to it on \([-\theta,\theta]\) and supported in
\((-\theta',\theta')\), meets the full tested pair-correlation formula of
Lamzouri's Lemma 3.1. The rare deletion estimate proved above changes the
normalized pair sum by \(o(1)\). Positivity of the finite real-ordinate
form factor bounds the uncut test statistic from below by the cutoff
statistic. Its diagonal and off-diagonal signs bound it from above by one,
contradicting the strict excess. At \(\theta=4/7\) this argument needs
\(p>12\). The limit runs over all real heights tending to infinity.

[Explicit kernels and the finite separated-pair argument](SmallGapFourierCertificate.md) ·
[Lamzouri, Lemma 3.1 and Theorem 3.3](https://arxiv.org/html/2611.14486v1#S3)

## Power rarity in the height and unconditional polynomial counts

Put \(c=2\theta<2\) and \(x=v/L\), so \(0\le x\le1/2\). Suppose the single-occurrence tail is bounded by \(T^{-b(x)+\varepsilon}\), uniformly in this range for every fixed \(\varepsilon>0\). A piecewise envelope of such bounds can also be used. If the deleted fraction is \(O(T^{-p})\), the pair-measure layer cake above implies a power saving whenever
\[
  \inf_{0\le x\le1/2}\left(\max\{p,b(x)\}-cx\right)>0.
\]
Indeed, the exponent after Hölder is \(cx-d\max\{p,b(x)-\varepsilon\}\), with \(d=1-1/q\). Choose \(q\) fixed and large and then \(\varepsilon\) small to retain a strictly negative bound. The layer-cake Jacobian \(L\) is logarithmic. Constants in the single-occurrence tail and the deleted fraction also cost only an arbitrarily small fixed power of \(T\). The same strict margin allows a slightly larger compact support \(\theta'>\theta\), still below one.

Ingham–Chourasiya–Simonič gives \(b_I(x)=4x/(3-2x)\) uniformly, after absorbing its logarithms in \(T^\varepsilon\). For \(4/3\le c<2\), the crossing \(b_I(x)=cx\) away from zero is \(x_c=(3c-4)/(2c)\). Thus the displayed margin is strictly positive exactly when \(p>cx_c=3\theta-2\). The first row at \(\theta=0.757551\) has threshold 0.272653.

Guth–Maynard gives \(b_G(x)=(20x-2)/(11/2+5x)\). This theorem is stated at fixed abscissa with arbitrary positive power allowance. For a fixed fine mesh on \([0,1/2]\), apply it at the left endpoint of each interval, then use monotonicity of the count and uniform continuity of \(b_G\). A mesh chosen for a fixed error allowance supplies a single height threshold and constant. This reasoning uses no uniform dependence of the literature constants on the abscissa. For \(0<p/c<1/2\), the rational inequality
\[
  5p^2+(11c/2-20)p+2c<0
\]
implies the required strict margin. In fact, \(b_G(x)>cx\) is equivalent to \(5c x^2+(11c/2-20)x+2<0\). This convex polynomial is strictly negative at both \(p/c\) and \(1/2\), hence everywhere between them. Below \(p/c\) one has \(p>cx\), and compactness gives a single strict margin. At \(\theta=0.879554\) the threshold is approximately 0.43049920547. [Guth–Maynard, Theorem 1.2](https://arxiv.org/abs/2405.20552)

A far-strip coefficient \(A(\sigma)\le2\) in \(N(\sigma,T)\ll_\varepsilon T^{A(\sigma)(1-\sigma)+\varepsilon}\) supplies the simpler tail \(b(x)\ge2x\) there. If this holds at all fixed \(x>d_0\), any \(p>c d_0\) suffices. Choose \(d>d_0\) with \(p>cd\). Below \(d\) the deletion fraction has a fixed power margin; above \(d\) the margin from the far tail is at least \((2-c)d\). The same finite-left-mesh argument is valid on \([d,1/2]\), including its last interval; the reference exponent \(2x\) is Lipschitz. This also follows from any bounded normalized critical-weight moment on that far strip by Markov's inequality. It requires no fixed zero-free half-plane.

For the published curve, take \(d_0=9/32\). On \(25/32<\sigma\le7/8\), Tao–Trudgian–Yang's tabulated bound and Bourgain use coefficients \(9/(8(2\sigma-1))\) or \(3/(2\sigma)\), both at most 2 on their respective intervals. Huxley's \(3/(3\sigma-1)\) is at most 2 on the remaining range. One can also use the repository's far-strip critical-weight estimate above \(9/32\). Therefore \(p>9\theta/16\) suffices. For the independently verified Lewko curve, take \(d_0=1/4\) using only the branch \(\sigma>3/4\), where \(A(\sigma)=3/(2\sigma)<2\). This gives \(p>\theta/2\). Neither deduction invokes the stronger Lewko branch at its excluded endpoint. [Tao–Trudgian–Yang, Table 11.1 and references](https://teorth.github.io/expdb/blueprint/zero-density-chapter.html) · [Published DOI](https://doi.org/10.1090/mcom/4138) · [Lewko public registry, proof commit and independent checker reports](https://palomar-registry.org/entry?id=PALOMAR-2026-10-11-000010&version=1)

For any of these margins, assuming \(T^p d_T(\lambda)\) remains bounded on a subsequence permits deletion of both endpoints of every qualifying internal adjacent gap. The exceptional proportion is \(O(T^{-p})\). The compactly tested full sum converges by Lamzouri's Lemma 3.1; the preceding estimate transfers it to the separated survivors with an error tending to zero. The larger integrable Gaussian test dominates the compact cutoff in the nonnegative real form factor. Its exact Fourier-side sign and unit diagonal give an upper bound of one, contradicting the certified objective greater than one. Hence \(T^p d_T(\lambda)\to\infty\), or equivalently the qualifying count divided by \(T^{1-p}\log T\) tends to infinity. This polynomial lower count uses the full complex tested formula and the actual consecutive-occurrence deletion; it does not require RH or one-log Selberg density at \(2\theta\). [Lamzouri, equations (3.1)–(3.5) and Lemma 3.1](https://arxiv.org/html/2611.14486v1#S3) · [Explicit Fourier witnesses and checked rows](SmallGapFourierCertificate.md)

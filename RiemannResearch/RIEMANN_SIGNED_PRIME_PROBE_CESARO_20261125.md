# Signed von Mangoldt probes at actual zeta-zero ordinates

## An unconditional cancellation between adjacent width ranges

Use natural logarithms. Set \(L=\log T/(2\pi)\), \(D_T=TL\), and count every nontrivial zero with its analytic multiplicity. If \(m_y\) is the number of occurrences at the same positive ordinate \(y\le T\), put \(C_T=D_T^{-1}\sum_y m_y^2\). Let \(E=N-M_\Gamma\), where \(N(t)\) counts ordinates in \((0,t]\) and \(M_\Gamma\) is the integral of the smooth gamma density used by the Lean repository. Define
\[
 A_T(q)=D_T^{-1}\sum_{0<\gamma\le T}
 \{E(\min(T,\gamma+q/L))-E(\gamma)\},\qquad
 B_T(q)=\int_0^q|\Phi_T(u)|^2\,du,\qquad R_T=A_T+B_T .
\]
The sum uses occurrences. Its strict left endpoint omits every zero-gap pair. Let
\[
 d_\Lambda=\sum_{n\ge2}\frac{\Lambda(n)^2}{n^2}
 =\sum_p\frac{(\log p)^2}{p^2-1}>0,\qquad s_T=\frac{Q}{(\log T)^2}.
\]

**Theorem.** For every positive width \(Q=Q(T)\to\infty\), the following two quantities both equal \(d_\Lambda s_T+o(1+s_T)\):
\[
 F_T(Q)=\frac{2}{Q}\int_0^Q R_T(q)\,dq+C_T-1,\qquad
 \Delta_T(Q)=\frac1Q\left(\int_Q^{2Q}R_T(q)\,dq-\int_0^QR_T(q)\,dq\right).
\]
In particular, the difference between the two adjacent width averages of the actual signed statistic tends to zero **if and only if** \(Q=o((\log T)^2)\). At \(Q/(\log T)^2\to\alpha>0\) it tends to \(\alpha d_\Lambda\), and at supercritical widths its ratio to \(s_T\) tends to \(d_\Lambda\). Neither statement assumes RH, simplicity, a DPP model for the zeros, or PCC. Cancellation at every **fixed** positive rational width is precisely ordinary positive-gap PCC and is open.

Write \(\mathcal A_Q f=(2/Q)\int_0^Q f(q)\,dq\); thus \(\mathcal A_Q1=2\). The factor 2 accounts for the two orders of a positive-distance pair. The factor \(C_T\) in the first formula is the complete horizontal diagonal, including distinct zeros at equal heights. The second formula eliminates it algebraically, without estimating its limiting value.

## Prime arithmetic at fixed and moving widths

Put \(w_n=\Lambda(n)/(n\log T)\) and \(x_n=\log n/\log T\), for \(1\le n\le T\). Then \(\Phi_T(u)=\sum_{n\le T}w_n e^{2\pi i u x_n}\). In terms of \(\operatorname{sinc}(v)=\sin(v)/v\), with value 1 at zero, finite multiplication and integration give the exact identity
\[
 B_T(q)=q\sum_{m,n\le T}w_m w_n\,
 \operatorname{sinc}(2\pi q(x_n-x_m)).
\]
Conjugate terms pair into real cosines, and the terms with \(m=n\) contribute \(q w_n^2\). By the classical Mertens estimate \(\sum_{n\le x}\Lambda(n)/n=\log x+O(1)\), the weighted atoms at \(x_n\) tend weakly to Lebesgue measure on \([0,1]\). Partial summation against \(e^{2\pi i u x}\) gives uniform convergence on compact \(u\)-intervals to
\[
 \Phi(u)=e^{\pi i u}\operatorname{sinc}(\pi u).
\]
Thus \(B_T(q)\to I(q):=\int_0^q\operatorname{sinc}^2(\pi u)\,du\) at each fixed \(q\ge0\).

For \(q>0\), integration by parts gives
\[
 I(q)=\frac{\operatorname{Si}(2\pi q)}{\pi}
       +\frac{\cos(2\pi q)-1}{2\pi^2q}.
\]
A second integration gives the exact sine-hole average
\[
 J(Q)=\mathcal A_Q I=
 \frac{2\operatorname{Si}(2\pi Q)}{\pi}
 +\frac{\cos(2\pi Q)-1+\operatorname{Ci}(2\pi Q)-\gamma_{\!E}-\log(2\pi Q)}
        {\pi^2Q}.
\]
In particular \(J(Q)=1-\log Q/(\pi^2Q)+O(1/Q)\) for \(Q\ge1\). Wolfram Language verified these formulas by differentiation and the zero-width boundary limits. Its Taylor calculation yields \(V_{\sin}(q)=q-q^2+\pi^2q^4/18+O(q^6)\) for \(V_{\sin}(q)=q[1-J(q)]\). The zero-statistic estimates below use analytic number theory.

Let \(H_T(q)=B_T(q)-I(q)\) and \(\ell=\log T\). The checked M17 results give, uniformly for \(q\ge0\) and \(\ell\ge2\),
\[
 |H_T(q)|\ll \ell^{-1}+q/\ell^2,\qquad
 H_T(q)/(q/\ell^2)\longrightarrow d_\Lambda\quad\text{if }q/\ell\to\infty .
\]
It follows that \(\mathcal A_Q B_T=1+d_\Lambda s_T+o(1+s_T)\) for every \(Q\to\infty\). Indeed, write \(\mathcal A_Q H_T=2\int_0^1H_T(xQ)\,dx\). Along a subsequence with \(s_T\to0\) the uniform bound suffices. If \(s_T\to\alpha\in(0,\infty]\), then for each \(x>0\) the ratio \(H_T(xQ)/(x s_T)\) tends to \(d_\Lambda\). The uniform bound divided by \(s_T\) allows dominated convergence on \([0,1]\), giving \(\mathcal A_Q H_T/s_T\to 2d_\Lambda\int_0^1x\,dx=d_\Lambda\). Subsequence compactness of \(s_T/(1+s_T)\) gives the stated form even for oscillating widths.

[Finite probe and its continuum limit](Analysis/MontgomeryPrimeProbeEnergy.lean) · [Sharp-width estimates](Analysis/MontgomeryPrimeProbeSharpWidths.lean) · [Prime-power diagonal](Analysis/MontgomeryPrimeProbeDiagonalMean.lean)

## An oriented triangle identity for the actual copies

On the real line let \(\mu\) be the atomic counting measure on the positive ordinates through \(T\), let \(\nu=M_\Gamma'(t)\mathbf1_{(0,T]}(t)\,dt\), and put \(\eta=\mu-\nu\). The smooth measure can be signed on a bounded initial interval. All three measures have finite total variation at fixed \(T\). For \(h=Q/L>0\) set
\[
 K_h(u)=(1-|u|/h)_+,\qquad
 H_h(\sigma,\tau)=\iint_{x<y}K_h(y-x)\,d\sigma(x)\,d\tau(y).
\]
Exact averaging of the clipped, right-continuous increments gives \(D_T\mathcal A_Q A_T=2H_h(\mu,\eta)\). Also
\[
 \frac1h\int_{\mathbb R}\eta((t,t+h])^2\,dt
 =\iint K_h(y-x)\,d\eta(x)\,d\eta(y)
 =\sum_y m_y^2+2H_h(\eta,\eta).
\]
The first equality uses the length of intersection of two intervals of length \(h\). In the second, the only atoms of \(\eta\) come from \(\mu\). Combining the two exact equalities yields
\[
 \boxed{\mathcal A_Q A_T+C_T=
 \frac1{TQ}\int_{\mathbb R}\eta((t,t+h])^2dt
 +\frac{2}{TL}H_h(\nu,\eta).}
\]
The order of the arguments in the last term matters. The base of \(A_T\) is sampled at zero occurrences. Its partner is a forward, clipped discrepancy increment.

## Bounding the smooth term and the two endpoints

For \(0\le y\le T\), put \(G_T(y)=\eta((0,y])\). The Riemann–von Mangoldt formula and the classical bound on the continued argument give \(\sup_{[0,T]}|G_T|\ll\log(2T)\), also at the right-limit endpoints. The smooth density differs on \(t\ge1\) from \((2\pi)^{-1}\log(t/(2\pi))\) by \(O(t^{-2})\), and is bounded on \([0,1]\). Thus on \([0,T]\) it is the sum of \(g(t)=(2\pi)^{-1}\log(\max(1,t)/(2\pi))\) and a remainder with uniformly bounded \(L^1\) norm. Extend both functions by zero. The total variation of \(g\mathbf1_{[0,T]}\) is \(O(\log(2T))\), including its boundary jumps.

Writing \(\kappa_h(u)=(1-u/h)\mathbf1_{(0,h)}(u)\), the cross term is \(\int \phi_h(y)d\eta(y)\) with \(\phi_h=\kappa_h*(M_\Gamma'\mathbf1_{[0,T]})\). Since \(\|\kappa_h\|_1=h/2\) and its total variation is 2, convolution of the two density terms gives \(\|\phi_h\|_\infty+\operatorname{Var}(\phi_h)\ll h\log(2T)+1\). Stieltjes integration by parts against \(G_T\) gives
\[
 \frac{|H_h(\nu,\eta)|}{TL}\ll \frac{Q}{T}+\frac1T .
\]

For \(h\le T\) the portion of the squared-window integral differing from the ordinary untruncated increment integral on \([0,T]\) is confined to \([-h,0]\) and \([T-h,T]\). Both integrands there are bounded by \(O(\log^2(2T))\), from the same cumulative discrepancy estimate up to \(2T\). Hence the discrepancy in the integrals is \(O(h\log^2(2T))\).

Let \(S(t)=\pi^{-1}\arg\zeta(1/2+it)\) with its classical continued-argument convention. Away from zero ordinates, \(G(t)=N(t)-M_\Gamma(t)\) and \(S(t)\) differ by a constant up to a bounded function \(r\) with \(r(t)=O(t^{-1})\) at infinity. This weaker comparison already follows from the classical Riemann–von Mangoldt formula and integrating the \(O(t^{-2})\) gamma-density remainder. Thus \(\|r(\cdot+h)-r\|_{L^2(0,T)}\le2\|r\|_{L^2(0,\infty)}=O(1)\). Endpoint conventions for \(S\) in its Lebesgue moments have no effect. The sampled increment in the exact triangle identity always uses the right-continuous count.

[Actual cumulative discrepancy](Analysis/ActualZeroDiscrepancy.lean) · [Sampled increment and gamma comparison](Analysis/MontgomerySampledArgumentError.lean) · [GLSS, §§3 and 5](https://arxiv.org/pdf/2503.15449)

## The published mean-square input and the moving conclusion

For \(0<h\le1\), Fujii's unconditional increment estimate in Goldston–Lee–Schettler–Suriajaya, Proposition 2 (5.6), gives
\[
 \int_0^T [S(t+h)-S(t)]^2\,dt
 =\frac{T}{\pi^2}\log(2+Q)+O\big(T\sqrt{\log(2+Q)}\big).
\]
The bounded \(L^2\) correction just described is absorbed by this error. For \(1<h\le T\), Selberg's unconditional second moment \(\int_0^{2T}S(t)^2\,dt\ll T\log\log(3T)\) bounds the increment integral by the same order. In the oriented identity these estimates give the following uniform conclusions for sufficiently large \(T\):
\[
\begin{aligned}
 \mathcal A_Q A_T+C_T
 &=\frac{\log(2+Q)}{\pi^2Q}
 +O\left(\frac{\sqrt{\log(2+Q)}}{Q}+\frac{Q+L}{T}\right)
 &&(1\le Q\le L),\\
 |\mathcal A_Q A_T+C_T|
 &\ll\frac{\log\log(3T)}{Q}+\frac{Q+L}{T}
 &&(L<Q\le TL).
\end{aligned}
\]
In particular \(\mathcal A_Q A_T+C_T\to0\) for every \(Q\to\infty\) with \(Q=o(T)\). For \(1\le Q\le L\) the two explicit logarithmic terms from \(A_T\) and \(J(Q)\) cancel. M17 then yields \(|F_T(Q)|\ll\sqrt{\log(2+Q)}/Q\) in this whole range.

For completeness, \(C_T=O(1)\) unconditionally by GLSS (6.2) at width 1, since strict-positive counts are nonnegative. Also \(|A_T(q)|\ll\log(2T)\) uniformly in every \(q\), since every increment is clipped at \(T\) and \(N(T)/(TL)=O(1)\). If \(Q\ge\sqrt T\), these coarse bounds give \((\mathcal A_Q A_T+C_T)/(1+s_T)\to0\). On \(Q<\sqrt T\) the preceding two uniform estimates give the same conclusion. Adding the prime result proves the all-width formula for \(F_T\). Finally
\[
 \Delta_T(Q)=F_T(2Q)-F_T(Q).
\]
The collision and unit terms cancel exactly, while the prime contribution is \(d_\Lambda(2s_T-s_T)\). Its positive coefficient proves the claimed “if and only if” by taking a subsequence on which \(s_T\) stays away from zero.

[GLSS, unconditional variance and horizontal diagonal](https://arxiv.org/pdf/2503.15449) · [Goldston, Selberg's unconditional moments, Theorem 8 (10.6)](https://arxiv.org/pdf/math/0412313)

## Two refinements and an unsmoothed consequence

**The prime diagonal below the critical scale.** Even when \(s_T\to0\), the ratio \(F_T(Q)/s_T\) tends to \(d_\Lambda\) provided
\[
 \frac{Q}{\log T\,(\log\log T)^{1/4}}\longrightarrow\infty .
\]
The same is true of \(\Delta_T(Q)/s_T\). To see the gain, put \(h=Q/L\). For \(1\le h\le T\), Selberg’s \(L^2\) approximation in Goldston’s Theorem 8 (10.5), at cutoff \(Y=2T\), approximates both endpoints of the increment by the same prime sum. The total remainder in \(L^2(0,T)\) is \(O(\sqrt T)\). For \(a_p=(p^{ih}-1)/\sqrt p\), the Montgomery–Vaughan mean-value theorem (4.6) gives
\[
 \frac1T\int_0^T\left|\sum_{p\le Y}a_p p^{it}\right|^2dt
 =\sum_{p\le Y}|a_p|^2+O(1).
\]
Indeed \(T^{-1}\sum_{p\le Y}p|a_p|^2\ll1\). The integral of the square without complex conjugation, divided by \(T\), is \(O(T^{-1}(\sum_{p\le Y}p^{-1/2})^2)=O(1)\), since \(\log(p p')\ge\log4\). Taking the imaginary part therefore gives
\[
 W_T(Q)=\frac1{\pi^2}\sum_{p\le2T}\frac{1-\cos(h\log p)}p
             +O(\sqrt{\log\log(3T)}),
 \qquad W_T(Q)=\frac1T\int_0^T[S(t+h)-S(t)]^2dt .
\]
The error includes the cross term with Selberg’s remainder. By partial summation using the classical PNT error \(\pi(x)-\operatorname{Li}(x)=O(x/\log^3x)\), \(|\sum_{p\le Y}p^{-1}\cos(h\log p)|\ll1+h\). The main integral is uniformly bounded for \(h\ge1\) by integration by parts after putting \(v=\log x\). The error integral is \(O((1+h)\int_2^\infty dx/(x\log^3 x))\). Mertens’ prime harmonic sum now gives
\(W_T(Q)=\log\log T/\pi^2+O(\sqrt{\log\log(3T)}+h)\).
The corresponding term in \(J(Q)-1\) has numerator \(-\log Q/\pi^2\), and \(\log Q=\log\log T+\log h-\log(2\pi)\). In the normalized sum the uncancelled error is
\[
 O\left(\frac{\sqrt{\log\log(3T)}+h+\log(2+h)}{Q}
         +\frac{Q+L}{T}\right).
\]
The comparison between conventional and gamma-centered argument moments contributes \(O(\sqrt{\log\log(3T)}/(\sqrt T\,Q))\), which is absorbed here. For \(Q<\sqrt T\), division by \(s_T\) sends every term to zero under the stated fourth-root hypothesis. For larger \(Q\) the uniform bound on every sampled increment suffices. On the prime side, \(Q/\log T\to\infty\) and the dominated convergence argument still applies after dividing by \(s_T\), even for \(s_T\to0\), since the bound becomes \(O(\log T/Q+x)\) at \(q=xQ\). This proves the refinement.

**Other width weights.** For a fixed real function \(w\) of bounded variation on \([0,1]\),
\[
 2\int_0^1 w(x)R_T(xQ)\,dx+(C_T-1)\int_0^1 w(x)\,dx
 = 2d_\Lambda s_T\int_0^1 xw(x)\,dx+o_w(1+s_T).
\]
For the proof, the primitive \(x[\mathcal A_{xQ}R_T+C_T-1]\), defined as zero at \(x=0\), differs uniformly from \(d_\Lambda s_T x^2\) by \(o(1+s_T)\). If uniformity were to fail, take a subsequence \(x_T\to x_0\). For \(x_T Q\to\infty\), the already proved all-width formula applies to \(x_T Q\). For bounded \(x_T Q\), use \(x_T\to0\) and uniform boundedness on compact widths. The latter follows from GLSS (6.2) at a larger fixed width and monotonicity of strict pair counts, the bounded slope of the normalized sampled smooth term and M17. Stieltjes integration by parts against \(w\) gives the displayed assertion. In particular \(w(x)=6x^2-6x+1\) has both mean and first moment zero. Its signed width average tends to zero throughout \(Q\to\infty,\ Q=O((\log T)^2)\), including the critical scale. The adjacent-range difference is the piecewise constant, zero-mean case after rescaling.

**Pointwise relative cancellation at all growing widths.** The same proof also yields
\[
 \frac{A_T(q(T))+B_T(q(T))}{q(T)}\longrightarrow0
 \quad\text{whenever }q(T)\to\infty .
\]
In fact \(|\int_0^v A_T|\ll v\) for \(1\le v\le2\sqrt T\) by the two centered bounds and \(C_T=O(1)\). Write \(A_T=P_T-M_T\), with \(P_T\) the nondecreasing strict-pair count and \(M_T\) the normalized sampled smooth increment. The bound \(\sup_{[0,T]}|M_\Gamma'|\ll L\) makes \(M_T\) uniformly Lipschitz as a function of width. Thus \(A_T(v)\ge A_T(u)-K(v-u)\) for \(v\ge u\). On \(4\le q\le\sqrt T\), left and right averages over intervals of length \(\sqrt q\) give \(|A_T(q)|\ll\sqrt q\). For \(q>\sqrt T\) use \(|A_T(q)|\ll\log T\). Finally \(B_T(q)\le1/2+O(1/\log T+q/(\log T)^2)\) by M17. This relative limit controls the signed statistic without averaging. The fixed-width PCC test requires its absolute error to vanish.

## What remains at a fixed width

Let \(P_T(q)\) be the normalized count of ordered pairs with strictly positive unfolded difference at most \(q\), and let \(G_{\sin}(q)=q-I(q)\). For each fixed \(q>0\), the repository gives
\[
 A_T(q)+B_T(q)=P_T(q)-G_{\sin}(q)+o(1).
\]
Convergence of the left side to zero at all positive rational \(q\) is equivalent to ordinary positive-gap PCC.

There is an equivalent formulation in Lebesgue variance. Set \(W_T(q)=T^{-1}\int_0^T[S(t+q/L)-S(t)]^2\,dt\). The exact oriented identity and the bounds on clipping and smooth centering imply, at every fixed \(q>0\),
\[
 \mathcal A_q R_T=1-C_T+\frac{W_T(q)-V_{\sin}(q)}{q}+o_q(1).
\]
Thus ordinary PCC is equivalent to \(W_T(q)-q(C_T-1)\to V_{\sin}(q)\) for all positive rational \(q\). For the converse, \(B_T\to I\) uniformly on compact widths, and the sampled smooth increments converge uniformly there to \(q\). The latter follows by monotonicity for the elementary smooth main on all but finitely many low copies, or by a uniform Lipschitz bound and pointwise convergence for the exact gamma main. Therefore convergence of these primitives is precisely convergence of \(\int_0^qP_T\) to \(\int_0^qG_{\sin}\). Left and right rational secants of these convex primitives recover their continuous limiting derivative \(G_{\sin}(q)\). The forward direction also follows by integrating the converging counts, bounded on any finite interval by the count at a larger rational endpoint.

Equivalently, one may require \(W_T(q)\to V_{\sin}(q)\) alone for all rational \(q>0\). Indeed strict-pair nonnegativity, the finite triangle identity and the smooth comparison give \(\limsup_T C_T\le q+V_{\sin}(q)/q\) under that hypothesis. Sending rational \(q\downarrow0\) gives an upper bound of 1, while \(C_T\ge N(T)/(TL)\to1\) in the liminf. In the other direction, ordinary PCC implies \(C_T\to1\) by GLSS, and the centered equivalence then yields the variance limit. Fujii's fixed-\(q\) error is \(O_q(1)\) after division by \(T\), so the needed limiting value is an additional microscopic estimate.

Montgomery's original Fourier result assumes RH and restricts the test spectrum. Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh obtain an unconditional restricted-frequency result for complex zero differences. A fixed interval cutoff of the ordinates has unbounded Fourier support. Lagarias–Rodgers moreover exhibit a discrete sine process on the half-integer lattice that agrees with the sine process on their band-limited tests, although it has no strictly positive gaps less than \(1/2\). A proof of fixed-width cancellation needs new actual-zero information.

[Checked fixed-width signed comparison](Analysis/MontgomeryCofinalPrimeProbeTrace.lean) · [Montgomery's original paper](https://public.websites.umich.edu/~hlm/paircor1.pdf) · [Unconditional complex-zero theorem](https://arxiv.org/abs/2306.04799) · [Lagarias–Rodgers, Lemma 4.6 and §4.5](https://arxiv.org/abs/1905.12123)

## A fixed-width prime computation and the missing tail

There is an unconditional computation inside the microscopic variance itself. Define the classical Selberg prime polynomial and its actual remainder by
\[
 X_T(t)=-\frac1\pi\sum_{p\le2T}\frac{\sin(t\log p)}{\sqrt p},
 \qquad Y_T(t)=S(t)-X_T(t),\qquad \delta_h f(t)=f(t+h)-f(t).
\]
This auxiliary polynomial uses weights \(p^{-1/2}\). The earlier \(\Phi_T\) has weights \(\Lambda(n)/(n\log T)\). For fixed \(q>0,\ h=q/L\), the mean-value calculation in the fourth-root refinement has errors tending to zero **for the polynomial itself**. Its normalized conjugate error is \(O(\pi(2T)/T)\); the nonconjugate error is \(O((\sum_{p\le2T}p^{-1/2})^2/T)=O(1/\log^2T)\) by partial summation and the prime number theorem. Mertens’ estimate for \(\sum_{p\le x}(\log p)/p\) then gives
\[
 \frac1T\int_0^T(\delta_hX_T)^2\,dt\ \longrightarrow\
 V_{\rm low}(q)=\frac1{\pi^2}\int_0^1\frac{1-\cos(2\pi qx)}x\,dx .
\]
The test function \((1-\cos(2\pi qx))/x\) extends continuously to zero, and the cutoff \(\log(2T)/\log T\) tends to one. The previously derived sine model satisfies the exact decomposition
\[
 V_{\sin}(q)=V_{\rm low}(q)+V_{\rm high}(q),\qquad
 V_{\rm high}(q)=\frac1{\pi^2}\int_1^\infty\frac{1-\cos(2\pi qx)}{x^2}\,dx>0 .
\]
Indeed, for \(z=2\pi q\), the two integrals before the factor \(\pi^{-2}\) are \(\gamma_E+\log z-\operatorname{Ci}(z)\) and \(1-\cos z+z(\pi/2-\operatorname{Si}(z))\). Wolfram Language verified their sum against the exact \(q[1-J(q)]\) formula.

Consequently an explicit remaining fixed-width test, necessary and sufficient for ordinary PCC when imposed at every positive rational \(q\), is
\[
 \frac1T\int_0^T\left[(\delta_hY_T)^2+
                2(\delta_h X_T)(\delta_hY_T)\right]dt
   \longrightarrow V_{\rm high}(q).
\]
The integral on the right is the high-frequency part of the sine **model**. Identifying it with the indicated actual second moment and cross term is the open step. In particular, discarding the remainder would give the wrong target.

One can already bound the remainder for the actual zeros at a fixed width. Nonnegativity of the strict-pair count gives \(W_T(q)\ge q C_T-q^2+o_q(1)\) from the oriented triangle identity and fixed-width smooth comparison. Since \(\liminf C_T\ge1\) and \(V_{\rm low}(q)\le q^2\),
\[
 \liminf_{T\to\infty}\frac1T\int_0^T
 [(\delta_hY_T)^2+2(\delta_hX_T)(\delta_hY_T)]\,dt
 \ \ge q-q^2-V_{\rm low}(q)\ \ge q-2q^2 .
\]
The reverse triangle inequality in \(L^2(dt/T)\) further gives, for \(0<q<1/2\),
\[
 \liminf_{T\to\infty}\frac1T\int_0^T(\delta_hY_T)^2\,dt
 \ \ge(\sqrt{q-q^2}-\sqrt{V_{\rm low}(q)})^2
 \ \ge(\sqrt{q-q^2}-q)^2>0 .
\]
At \(q=1/4\) the combined residual has lower bound \(1/8\), and the squared remainder alone has lower bound \((2-\sqrt3)/8\). These bounds concern fixed microscopic intervals of the actual zeros and use no conjecture.

## Microscopic Fourier characters and a modular count criterion

Write \(L=\log T\), \(D=TL/(2\pi)\), \(h=2\pi q/L\) and \(t_i=\gamma_i\).
For each zero occurrence set \(v_i=\min(T,t_i+h)\),
\(K_i=N(t_i,v_i]\), and \(G_i=\mathrm{smoothCount}(v_i)-\mathrm{smoothCount}(t_i)\).
All occurrences at the base height are excluded from \(K_i\). Every occurrence
at the upper endpoint is included.

### What the circle map sees

The exact sampled discrepancy increment is \(K_i-G_i\). At every integer
frequency \(k\), its character is exactly \(\exp(-2\pi i kG_i)\).
For fixed \(q>0\) the empirical distribution modulo one therefore converges
to the point mass at \(-q\bmod 1\). On \(\delta T\le t_i\le(1-\delta)T\)
the clipped gamma increment tends uniformly to \(q\), by Stirling's estimate
for the derivative of the gamma main term. Riemann–von Mangoldt gives
asymptotic mass \(2\delta\) for the discarded strips when \(0<\delta<1/2\).
The characters have modulus one, so taking \(\delta\downarrow0\) proves
convergence even in mean chordal distance. The modular identity erases
\(K_i\) exactly, including unusually large neighbor counts.

For an ordinate character \(f_u(t)=\exp(iut)\) use the same clipping and set
\(A_T^{f_u}=D^{-1}\sum_i(f_u(v_i)-f_u(t_i))\). For \(u=\log(n/m)\), let
\(M(n,m)\) denote the repository's centered rational FMZ main term. Then
\[
 L^2 A_T^{f_u}(q)\ \longrightarrow\ 4\pi^2 i q u\,M(n,m).
\]
Indeed the raw sum differs from
\((e^{iuh}-1)\sum_i e^{iu t_i}\) by at most
\(|u|h\,N(T-h,T]\). The raw difference is bounded for fixed \(u,q\).
Multiply the centered rational FMZ limit by \(L(e^{iuh}-1)\to2\pi iqu\).
At \(u=0\) the increment vanishes identically. For \(n>1,\ m=1\),
the limit becomes \(-2\pi i q\,(\log n)\Lambda(n)/\sqrt n\).

For a moving finite Fourier test \(f_T(t)=\sum_j c_j e^{iu_jt}\) one has
\[
 |A_T^{f_T}(q)|\le {N(0,T]\over D}\,{2\pi q\over L}
                         \sum_j |c_j|\,|u_j|.
\]
Consequently any such family with sampled error
\(A_T^{f_T}(q)-A_T(q)\to0\) that recovers the proposed nonzero sine deficit
must satisfy
\[
 \liminf_{T\to\infty}L^{-1}\sum_j|c_j|\,|u_j|
 \ \ge\ {1\over 2\pi q}\int_0^q
                   \left({\sin\pi x\over\pi x}\right)^2 dx .
\]
This gives a quantitative restriction on direct approximation by one-point
FMZ tests. The upper and lower ends of the observation interval are the same
in this inequality as in the signed pair statistic.

For the original real-valued discrepancy, removing the upper clipping changes
\(A_T(q)\) by \(O(\log T/T)\), uniformly whenever \(0\le h\le1\).
Only the last physical unit interval contributes, with \(O(\log T)\) base
occurrences. The all-heights discrepancy estimate bounds the change of
each row by \(O(\log T)\); division by \(D\) gives the claim.

### A single harmonic retaining the neighbor count

For integer \(m\ge2\) define
\[
 H_{T,m}(q)=\frac{m}{2\pi D}\sum_i\sin(2\pi K_i/m),\qquad
 U_{3,T}(q)=D^{-1}\sum_i K_i^3 .
\]
Only the first character of the integer count modulo \(m\) is used. The
following signed error bound is valid at finite height:
\[
 0\le P_T(q)-H_{T,m}(q)
       \le \frac{2\pi^2}{3m^2}U_{3,T}(q).
\]
It follows by summing \(x-x^3/6\le\sin x\le x\) for \(x=2\pi K_i/m\).
A second-moment form gives the upper bound
\(\pi D^{-1}\sum_i K_i^2/m\).
At each fixed \(q\) the third moment is uniformly bounded for all sufficiently
large \(T\). Every neighbor counted by \(K_i\) has Cauchy weight at least
\(1/(1+(2\pi q)^2)\). Apply Lamzouri, Lemma 2.3, with moment exponent 3
and \(N(T)/D\to1\). This last published analytic input is external to the
Lean finite inequality.

It follows that for *any* preassigned integer-valued \(m(T)\to\infty\), however
slowly, ordinary positive-gap PCC is equivalent to
\[
 \lim_{T\to\infty}H_{T,m(T)}(q)
 =q-\int_0^q\left(\frac{\sin \pi x}{\pi x}\right)^2dx
 \quad\text{for every positive rational }q .
\]
For the explicit integer modulus \((1+N(T))^2\), the elementary estimates
\(K_i\le N(T)\) and \(\sum_i K_i^3\le N(T)^4\) alone yield a uniform
error \(\le 2\pi^2/(3D)\) for every positive width. The limiting value of
the signed modular statistic on the actual zero occurrences remains open.
To express the same test on one fixed orbit, let \(\alpha\) be irrational
and \(z_\alpha(t)=e^{2\pi i\alpha N(0,t]}\). Choose integers \(r_j,a_j\)
such that \(\epsilon_j=r_j\alpha-a_j\ne0\) tends to zero, for instance by
continued fractions. For each row,
\[
 z_\alpha(v_i)^{r_j}\overline{z_\alpha(t_i)^{r_j}}
    =e^{2\pi i\epsilon_j K_i}.
\]
The imaginary part divided by \(2\pi\epsilon_j\) has the same error bound
with \(1/m^2\) replaced by \(\epsilon_j^2\), since \(\sin(x)/x\) is even.
Orbit density supplies the frequencies. To obtain the conjecture one must
compute the linear coefficient of the signed return statistic at those
frequencies. Mere convergence of the unscaled character to one holds for
every bounded first moment and leaves that coefficient undetermined.

The fixed orbit can also be applied directly to the real discrepancy. Set
\(w_\alpha(t)=e^{2\pi i\alpha S_*(t)}\) and
\[
 Z_{i,j}=w_\alpha(v_i)^{r_j}\overline{w_\alpha(t_i)^{r_j}}\,e^{2\pi i a_j G_i}.
\]
The integer \(a_jK_i\) drops out, so \(Z_{i,j}=e^{2\pi i\epsilon_j(K_i-G_i)}\)
exactly. The gamma density on \([0,T]\) is \(O(1+\log T)\), hence
\(\max_i|G_i|=O_q(1)\). The same third-moment argument gives the signed
error estimate
\[
 \left|A_T(q)-\frac{1}{2\pi\epsilon_j D}\sum_i\Im Z_{i,j}\right|
 \le \frac{(2\pi\epsilon_j)^2}{6D}\sum_i |K_i-G_i|^3
 \ll_q \epsilon_j^2 .
\]
Thus along *any* \(j=j(T)\to\infty\) the linear term at the return frequencies
would have to be \(-\int_0^q\mathrm{sinc}^2(\pi x)\,dx\). This last display
uses the paper's convention \(\mathrm{sinc}(v)=\sin(v)/v\).

Fujii's shifted-argument estimate bounds the normalized sampled shift by a
constant. The sine coefficient requires an asymptotic at fixed unfolded width.

[Ford–Meng–Zaharescu, one-point modular sampling](https://arxiv.org/abs/1511.06814) ·
[Lamzouri, Lemma 2.3](https://arxiv.org/html/2611.14486v1#S2) ·
[Fujii, pp. 85–86, right-continuous argument and shifted discrete bound](https://rikkyo.repo.nii.ac.jp/record/8721/files/AA00610867_53-01_05.pdf)

## Verification scope

The finite prime kernel, fixed-width limit and pointwise moving-width arithmetic used above have Lean proofs in the linked repository modules. The unconditional use of Fujii's and Selberg's second moments, the oriented measure identity with its uniform endpoint estimates, and the microscopic equivalence with conventional argument variance are proved here as mathematical deductions. The two companion modules treat the averaged prime estimate and the signed transfer for the actual normalized statistics. The signed transfer retains the centered actual-zero estimate as an explicit hypothesis. The classical estimates furnishing it above are external analytic inputs to Lean.

[Averaged prime probe](Analysis/MontgomeryPrimeProbeCesaro.lean) · [Signed Cesàro trace](Analysis/MontgomerySignedCesaroTrace.lean)

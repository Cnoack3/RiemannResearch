# A sharp rate from the first horizontal moment to the second

Give each occurrence of a positive-ordinate zero up to height \(T\) mass \(1/N(T)\), counting its analytic multiplicity. Put
\[
 X_T=|\beta-\tfrac12|\log T,\qquad m_T=\mathbb E_T X_T,\qquad
 q_T=\mathbb E_T X_T^2 .
\]
The subcritical Selberg estimates, symmetry about the critical line and Riemann–von Mangoldt give, for each fixed \(0<a<8/7\), a constant \(C_a>0\) and a height \(T_a\) such that
\[
 \mathbb P_T(X_T\ge x)\le C_a e^{-ax}\qquad (T\ge T_a,\ x>0).
\]
The tail vanishes for \(x\ge\tfrac12\log T\). The constants can depend on \(a\). [Baluyot, *On the Zeros of Riemann's Zeta-function*, Theorem 1.2.1](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320)

For any sequence of heights with \(T\to\infty\) and \(m_T\to0\),
\[
 \boxed{\displaystyle q_T\le (7/8+o(1))\,m_T\log(1/m_T).}
\]
The product on the right is defined as zero at \(m_T=0\), when \(X_T=0\) almost surely. The coefficient \(7/8\) is optimal for these analytic inputs in the class of arbitrary probability distributions.

## A direct size-biased proof

Fix \(0<a<b<8/7\). Integrating the derivative of \(x e^{ax}\) against the tail gives
\[
 \mathbb E_T[X_Te^{aX_T}]
 \le C_b\int_0^\infty(1+ax)e^{-(b-a)x}\,dx
 =\frac{C_b b}{(b-a)^2}=:K_{a,b}
\]
uniformly for \(T\ge T_b\). When \(m_T>0\), weight the original law by \(X_T/m_T\) and denote expectation under this probability law by \(\mathbb E_T^\#\). Convexity of the exponential gives
\[
 \exp(a q_T/m_T)
 =\exp(a\,\mathbb E_T^\# X_T)
 \le\mathbb E_T^\#e^{aX_T}
 =\frac{\mathbb E_T[X_Te^{aX_T}]}{m_T}
 \le\frac{K_{a,b}}{m_T}.
\]
Thus \(q_T\le(m_T/a)\log(K_{a,b}/m_T)\) at every sufficiently large height. Divide by \(m_T\log(1/m_T)\), take the limsup as \(m_T\to0\), then let \(a\uparrow8/7\).

## The exact finite-probability inequality

Let \(X\ge0\) have mean \(m>0\) and survival function \(S(x)=\mathbb P(X>x)\) bounded by \(Ce^{-ax}\), with \(a,C>0\). For all sufficiently small \(m\), there is a unique \(r>0\) such that
\[
 p=Ce^{-ar},\qquad m=p(r+1/a),\qquad 0<p\le1.
\]
The decreasing function \(r\mapsto Ce^{-ar}(r+1/a)\) tends to zero and its derivative is \(-aCr e^{-ar}\). Define \(S_*(x)=\min(p,Ce^{-ax})\) for \(x\ge0\). This is a survival function with mass \(1-p\) at zero. Conditional on a positive value, \(X_*\) has the law of \(r\) plus an exponential variable of rate \(a\).

Both survival functions have integral \(m\). On \([0,r]\), \(S-S_*=S-p\) is decreasing. On \([r,\infty)\), \(S-S_*\le0\). There is consequently a crossing point \(x_0\in[0,r]\) with \(S-S_*\ge0\) to its left and \(S-S_*\le0\) to its right, up to a possible boundary value. It follows that
\[
 \int_0^\infty x(S-S_*)\,dx
 =\int_0^\infty (x-x_0)(S-S_*)\,dx\le0 .
\]
Tonelli's moment formula gives the **attained optimum**
\[
 \mathbb E X^2\le p(r^2+2r/a+2/a^2)
 =\frac{m}{a}\left(t+\frac1t\right),\qquad t=1+ar.
\]
In particular \(t-\log t=\log(1/m)+1+\log(C/a)\). With \(a,C\) fixed this gives
\[
 t=\log(1/m)+\log\log(1/m)+1+\log(C/a)+o(1).
\]
Apply this inequality for each fixed \(a<8/7\), take the height limsup, and then send \(a\uparrow8/7\). There is no choice of an endpoint \(C_{8/7}\) in this argument.

The same crossing argument applies to the nondecreasing weight \(x^{s-1}\) for every real \(s>1\). The extremizer \(X_*\) simultaneously maximizes each such moment. Since \(r\to\infty\), its conditional \(s\)-th moment is \(r^s(1+o(1))\) by dominated convergence against the exponential law. Hence
\[
 \limsup_{\substack{T\to\infty\\m_T>0}}
 \frac{\mathbb E_T X_T^s}{m_T(\log(1/m_T))^{s-1}}
 \ \le\ (7/8)^{s-1}
\]
along any family on which \(m_T\to0\).

## Actual-zero normalization

Set \(H_T=T^{-1}\sum_{0<\gamma\le T}(\beta-\tfrac12)_+\) and
\(R_T=N(T)/(T\log T/(2\pi))\). Reflection gives \(m_TR_T=4\pi H_T\) exactly, and \(R_T\to1\). Thus \(H_T\to0\) implies
\[
 q_T\le(7\pi/2+o(1))H_T\log(1/H_T).
\]
The repository already checks the corresponding qualitative equivalence in
<code>ActualZeroOrdinate.oneSidedHeightMean_tendsto_zero_iff_quadratic</code>. The inequality above supplies the rate on the quadratic horizontal term in that criterion. The published and manuscript positive constants bounding \(H_T\) do not imply \(H_T\to0\).

There is also an elementary RH criterion at a faster scale. If \(V(T)=\sum_{0<\gamma\le T}|\beta-\tfrac12|\), then \(T m_T=(2\pi/R_T)V(T)\). The nonnegative quantity \(V(T)\) is nondecreasing. One off-line zero contributes a fixed positive amount at every subsequent height, and reflection and conjugation give an off-line zero of positive ordinate whenever RH fails. Thus \(\liminf_{T\to\infty}T m_T=0\) is equivalent to RH.

## Stronger coefficients when the first moment falls faster

Write \(L=\log T\), \(\ell=\log L\), \(M=\log(1/m_T)\). The actual Ingham–Littlewood bound in the repository gives the normalized survival envelope \(S_T(x)\le C L^2 e^{-4x/3}\). Its powers of \(L\) come from the unnormalized \(T L^3\) count and \(N(T)\asymp TL\). Apply the exact finite-probability inequality with \(a=4/3\) and height-dependent \(C L^2\). Its equation becomes \(t-\log t=M+2\ell+O(1)\), so \(t=M+2\ell+O(\log(M+2\ell))\). Consequently, if \(M/\ell\to\lambda\in(0,\infty]\),
\[
  \limsup \frac{q_T}{m_T M}
  \le \min\left(\frac78,\frac34\left(1+\frac2\lambda\right)\right).
\]
The bounds agree when \(\lambda=12\). For \(\ell=o(M)\), the coefficient is at most \(3/4\).

If \(M/L\to p\in(0,1]\), a fixed-strip zero density exponent gives a further improvement. Suppose the unnormalized count on \(\Re\rho\ge\sigma\) is \(\ll_{\sigma,\epsilon}T^{d(\sigma)+\epsilon}\) for each fixed \(\epsilon>0\). If \(d(\sigma)<1-p\), split the second moment at \(X=(\sigma-\tfrac12)L\). The lower part is at most \((\sigma-\tfrac12)Lm_T\). Reflection and \(X\le L/2\) bound the upper part by \(O(L T^{d(\sigma)+\epsilon-1})=o(m_T M)\) after taking \(\epsilon\) below the fixed exponent gap. Therefore
\[
 \limsup \frac{q_T}{m_T M}\le\frac{\sigma-\tfrac12}{p}.
\]
For \(p=1\), the physical support gives this bound with \(\sigma=1\). The Ingham exponent \(3(1-\sigma)/(2-\sigma)\) yields \(3/(4+2p)\) after taking admissible \(\sigma\) down to \((1+2p)/(2+p)\).

The next table uses the combined density envelope in <code>ActualZeroOrdinate.lewkoGuthMaynardCoefficient_eq</code>, conditional on the registered Lewko bound and the published Guth–Maynard bound as typed in the repository. Each entry gives the infimum \(\sigma_*(p)\), hence the coefficient \((\sigma_*(p)-1/2)/p\). Neighboring formulas agree at each displayed shared boundary. [Lewko, registered proof and source](https://palomar-registry.org/entry?id=PALOMAR-2026-10-11-000010&version=1) · [Guth and Maynard, *New large value estimates for Dirichlet polynomials*](https://arxiv.org/abs/2405.20552)

| Range of \(p\) | \(\sigma_*(p)\) |
| --- | --- |
| \(0<p\le 5/17\) | \((1+2p)/(2+p)\) |
| \(5/17\le p\le 5/14\) | \((15+3p)/(25-7p)\) |
| \(5/14\le p\le 2/5\) | \((5+4p)/9\) |
| \(2/5\le p\le 4/9\) | \((12+3p)/(20-5p)\) |
| \(4/9\le p\le 1/2\) | \(3/4\) |
| \(1/2\le p\le1\) | \(3/(5-2p)\) |

For the constant row take fixed abscissae **strictly above** \(3/4\), then send them down to \(3/4\). This retains the endpoint discontinuity of the density estimate. Any separately supplied zero-free strip \(\beta\le B_*\), including the repository's external continuum-contact hypothesis, gives the additional coefficient \((B_*-\tfrac12)/p\) directly from the support. Take the smaller available bound.

## Sharpness and thresholds that grow with height

Let \(A=8/7\). Give \(X_r\) the value \(r\) with probability \(p_r=e^{-Ar}\), and zero otherwise. This family satisfies even the endpoint exponential tail. Since \(m_r=rp_r\) and \(\mathbb E X_r^2/m_r=r\), the limiting coefficient is \(1/A=7/8\). The same example attains \((7/8)^{s-1}\) for every fixed \(s>1\). This is an abstract optimality result for the input inequalities.

Replacing \(p_r\) by \(e^{-Ar+\sqrt r}\) for large \(r\) still gives a uniform finite tail constant for each fixed \(a<A\), since \(\sup_r e^{-(A-a)r+\sqrt r}<\infty\). Now
\[
 A\,\mathbb E X_r^2/m_r-\log(1/m_r)=\sqrt r+\log r .
\]
Thus a universal endpoint remainder of order \(\log\log(1/m)\) needs further control of the near-endpoint constants.

Pair these abstract laws with heights for which \(r=o(\log\log T)\), for instance \(\log\log T=r^2\). Their positive atoms are inside the physical range. Both tails also satisfy the \(CL^2 e^{-4x/3}\) bound because \(p_r e^{4r/3}/L^2\to0\). The examples therefore preserve the optimal general coefficient in the presence of the Ingham estimate. They lie in the regime \(M=o(\ell)\), where the faster-decay estimates do not apply.

For both examples \(\mathbb E(X_r-u)_+\le m_r\to0\) at every fixed strike \(u\ge0\). They satisfy the limiting shifted-mollifier stop-loss constraints in the horizontal-moment note. Compact uniform estimates and their unspecified slowly expanding windows do not locate the effective strike \(r\asymp (7/8)\log(1/m_T)\). An endpoint remainder would follow, for example, from an all-threshold finite-height bound \(S_T(x)\le C e^{-8x/7}\) with an absolute \(C\). The subcritical bounds already give the sharp leading rate above.

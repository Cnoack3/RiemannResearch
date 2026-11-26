# Canonical lifts, reciprocal repairs and signed RH criteria

Use physical sites \(n\ge1\), \(Z=\zeta(2)\), \(P_n=1/[n(n+1)]\), and \(Q_n=1/(Zn^2)\).

## Nested CRT periods and positive variation

For \(L\mid M\), let \(U\) synthesize the old divisor family and \(W\) the new family after orthogonal projection off the old span in \(Q\). The joined family \(\Phi=(U,W)\) is a basis of the period-\(M\) trial space. Write \(h_M=1-\mathbf1_{M\mid n}\) and \(\Delta f(n)=f(n)-f(n-1)\) with zero anchor. For \(A_{ij}=\langle\Phi_j,\Delta\Phi_i\rangle_Q\) and \(\beta_i=\langle h_M-F_L,\Delta\Phi_i\rangle_Q\), the coefficients of \(F_M-F_L\) solve \(A(x,y)=\beta\). The old block is invertible and eliminating it gives the unique Schur-complement solution. In particular,
\[
 E_M-E_L=2\langle F_L,Ux\rangle_Q+\|Ux\|_Q^2+\|Wy\|_Q^2.
\]
For a predicted lift \(w=F_L+\Phi z\), the residual is \(\rho=\beta-Az\). Set \(w_i=\Phi A^{-1}e_i\) and \(\varepsilon=\sum_i|\rho_i|\|w_i\|_Q\). Subtracting the predicted energy and the signed response from \(E_M\) leaves precisely \(\|\sum_i\rho_iw_i\|_Q^2\), which lies in \([0,\varepsilon^2]\). A second radius uses a finite signed divisor sum, with the optimal shift-defect constant for anchored periodic sequences. The period bound gives \(\limsup_{2\mid M}E_M/M\le Z/(8\zeta(3))\) as \(M\to\infty\). At prime periods \(E_p\sim Z(\log(2\pi)-\gamma)p/(\log p)^2\). The proofs and explicit divisor formula are in the period note. [Signed interval](QCRTCanonicalGrowthCertificate.lean) · [Period bounds, prime asymptotic and inverse-free radius](CanonicalGrowthResidualCertificates20261113.md)

Let \(L(m)=\operatorname{lcm}(1,\ldots,m+2)\) and sample any cutoffs \(m_j\to\infty\). The positive variation \(V_j^+\) of \(\log(1+E_{L(m_i)})\) through \(i=j\) dominates the last value minus the first. For a right zero \(\rho\) with \(\beta=\Re\rho>1/2\), the Mellin lower bound on \(E_{L(m_j)}\) therefore gives
\[
 V_j^+\ge(2\beta-1)\log(m_j+2)+\log\log(m_j+2)-O_{\rho,m_0}(1)
\]
eventually. A zero lower limit for \(V_j^+/\log(m_j+2)\) on one such sampling implies RH. [Sampled variation theorem](QCRTPositiveLogVariation.lean)

## Which family has vanishing metric discrepancy?

The discrepancy \(R(f)=Z\|f\|_Q^2-\|f\|_P^2=\sum_{n\ge1} f(n)^2/[n^2(n+1)]\) is a squared norm. It vanishes asymptotically for cofinal signed averages of the centered Möbius residuals with bounded absolute coefficient masses. For full Möbius candidates with coefficient sum tending to \(c\), the limit is \(c^2(Z-1)\). The uncentered CRT collocation lifts satisfy the strictly positive lower bound
\[
 \liminf_{\substack{L\to\infty\\2\mid L}}R(F_L)
 \ge \frac{Z^2(3-\sqrt5)^2}{64(Z-1)} .
\]
It follows already from the difference-energy identity and the divisor moments at 1 and 2. The proof also gives positive discrepancy for cofinal signed blocks of these even-period lifts with bounded absolute coefficient mass and total coefficient tending to a nonzero limit. [Möbius limit in Lean](QCanonicalCofinalGram.lean) · [CRT lower bound and signed blocks](QCanonicalCofinalGramResearch20261015.md)

## A Vinogradov–Korobov upper bound for the complete minimum

For \(H\ge1\), let \(V_H(\alpha)\) be the minimum over the span of the residue
packets with conductors \(2,\ldots,H+1\) of
\[
 J_\alpha(v)=\|D(v-1)\|_Q^2+\alpha\|v\|_Q^2,\qquad
 Q(n)=\frac{1}{\zeta(2)n^2},\quad (Df)(n)=\frac{f(n)}{n}\quad(n\ge1).
\]
With all logarithms natural, set
\[
 U_x=\frac{(\log x)^{3/5}}{(\log\log x)^{1/5}},\qquad
 \kappa=\left(\frac{5}{3(53.99)^3}\right)^{1/5}.
\]
For all sufficiently large integers \(H\), the paper bound at the exact
leading coefficient is
\[
 V_H(H^{-2})\le \frac{12}{\zeta(2)H^2}
 +\frac{1040(1+1/e)}{\zeta(2)H}\exp(-\kappa U_H).
\]

Let \(M(x)=\sum_{n\le x}\mu(n)\). Lee and Leong's Theorem 1.1,
equation (11), gives \(|M(x)|/x<25.85(\log x)\exp(-\kappa_xU_x)\) for
\(x\ge\exp(\exp(10.01))\), where
\[
 \kappa_x=\kappa\left(1-\frac{\log 53.99}{\log\log x}\right)^{-1/5}.
\]
Convexity yields \(\kappa_x-\kappa\ge
\kappa\log(53.99)/(5\log\log x)\). Since \(U_x/(\log\log x)^2\to\infty\),
the exponent gain \((\kappa_x-\kappa)U_x\) eventually exceeds
\(\log\bigl(25.85\log x\,(1+\kappa U_x)\bigr)\).
Thus \(|M(y)|\le\varepsilon_H y\) for every \(y\ge H\), with
\(\varepsilon_H=e^{-\kappa U_H}/(1+\kappa U_H)\), using eventual monotonicity
of \(U_y\). Writing \(s=1+\kappa U_H\) and using \((\log s)/s\le1/e\) gives
\[
 \varepsilon_H\left(1+\log\frac{1}{\varepsilon_H}\right)
 = e^{-\kappa U_H}\left(1+\frac{\log s}{s}\right)
 \le(1+1/e)e^{-\kappa U_H}.
\]
The complete-energy transfer bounds the squared Pareto norm of the
exact-head Möbius trial by \(3+260H\varepsilon_H(1+\log(1/\varepsilon_H))\).
The balanced complete cost is at most \(4/(\zeta(2)H^2)\) times this norm
squared, proving the estimate. Its height threshold is qualitative.
Dividing the remainder by \(H^{-2}\) leaves \(H\exp(-\kappa U_H)\to\infty\).
The cofinal linear-cost condition requires a further estimate.

[Lee–Leong, Theorem 1.1, equation (11)](https://arxiv.org/pdf/2208.06141)

The Lean theorem `fullValue_le_mertens_envelope` gives the transfer for any regularization and any smaller trial window. `fullValue_eventual_vk_of_leeLeong` formalizes each strict rate below the endpoint from the stated Lee–Leong premise. [Complete minimum](QReciprocalFullMinimizer.lean)

## Primorial forcing modulo the carry subspace

Write \(S_n\) for the full finite primorial stage, \(P_n\) for its
\(Q\)-orthogonal projection, and \(K_n\) for its carry subspace. Put
\(Z=\zeta(2)\), \(a=1017/2000\), \(Bf(j)=f(j)/(j+1)\), and
\[
 c_n=P_nB(1-P_n1),\qquad A_n=I-P_nB\big|_{S_n},\qquad
 g_n=\operatorname{dist}_Q(c_n,A_nK_n).
\]
The distance uses the complete \(Q\) norm. The stage metric identity is
\(\langle v,w\rangle_P=Z\langle v,A_nw\rangle_Q\) for \(v,w\in S_n\).
Thus \(W_n=S_n\cap K_n^{\perp_P}=S_n\cap(A_nK_n)^{\perp_Q}\), and
\(g_n=\|P^Q_{W_n}c_n\|_Q\) by finite-dimensional orthogonal decomposition.

Let \(d_n\) be the matched stage displacement and \(s_n=P^P_{W_n}d_n\)
its Schur lift. The fixed-point equation gives \(A_nd_n=c_n\). For every
\(w\in W_n\),
\[
 \langle w,s_n\rangle_P=\langle w,d_n\rangle_P=Z\langle w,c_n\rangle_Q.
\]
Consequently the self-forcing \(F_n=\|s_n\|_P^2\) is the squared Pareto
dual norm of this functional. The four-site coercivity bound and the
upper metric comparison give
\(aZ\|w\|_Q^2\le\|w\|_P^2\le Z\|w\|_Q^2\) throughout \(S_n\).
Taking the supremum of the squared dual quotient on \(W_n\) yields
\[
 \boxed{Zg_n^2\le F_n\le (Z/a)g_n^2.}
\]
If \(W_n=\{0\}\), both quantities vanish. The upper estimate is valid
with \(g_n\) replaced by \(\|c_n-A_nz\|_Q\) for any \(z\in K_n\);
taking \(z=0\) recovers the original correction estimate. Thus
\(\liminf_n g_n=0\) is equivalent to \(\liminf_n F_n=0\) and implies
RH by the cofinal self-forcing theorem. Decay of this distance for actual
primorial stages remains an arithmetic hypothesis.

The original iterative endpoint and its posterior bound continue to apply, so the minimum of all three estimates is valid. [Carry-adjusted bound and iterative endpoints](QPrimorialSchurForcing.lean)

## Signed reciprocal-head repairs

Let \(V\) be the closed all-conductor legal space, \(d=P_V^Q1-P_V^P1\) the physical difference of its two fits, \(r_Q=1-P_V^Q1\), and \(t_N=(I-H_N)r_Q\), where \(H_N\) keeps the first \(N\) sites. Put \(Bf(n)=f(n)/(n+1)\). For any legal \(f_N\) agreeing with \(Bd\) through site \(N\), legal orthogonality kills \(\langle f_N,r_Q\rangle_Q\), and interpolation kills \(\langle Bd-f_N,H_Nr_Q\rangle_Q\). The displacement identity now reads
\[
 A:=\|d\|_P^2/Z=\langle Bd-f_N,t_N\rangle_Q.
\]
Taking absolute values proves the product criterion, even when only the infimum of the complete error-tail products is zero. Keeping the sign gives
\[
 (N+2)|\langle f_N,t_N\rangle_Q+A|
 \le \|(I-H_N)d\|_Q\,\|t_N\|_Q\longrightarrow0.
\]
Indeed \(t_N\) is supported above \(N\), where the multiplier of \(B\) is at most \(1/(N+2)\). Hence every choice of legal exact repairs yields the same signed limit. Under RH the residual vanishes. If RH fails, \(A>0\) and the pairings are eventually strictly negative. This proves the equivalence with cofinal nonnegative repair pairings. [Repair identities and RH criterion](QFullReciprocalRepairCriterion.lean)

## Consecutive prime packets

Write \(r_P=1-P_V^P1\) and \(T=dQ/dP=(1+1/n)/Z\) on physical sites. For distinct primes \(p,q\), the Möbius formula \(J_{pq}(n)=(n\bmod pq)-(n\bmod p)-(n\bmod q)\) gives \(e(n)=1+J_{pq}(n)/n=0\) below \(m=\min(p,q)\) and \(0\le e\le2\) everywhere. Since \(J_{pq}\in V\), \(\langle r_P,J_{pq}\rangle_P=0\), and \(\langle r_P,1\rangle_P=\|r_P\|_P^2\). Therefore
\[
 \left|Z\langle r_P,TJ_{pq}\rangle_P+\|r_P\|_P^2\right|
 =|\langle r_P,e\rangle_P|
 \le 2m^{-1/2}\|\mathbf1_{[m,\infty)}r_P\|_P=o(m^{-1/2}).
\]
Here \(P([m,\infty))=1/m\). Along any prescribed subsequence of consecutive prime pairs tending to infinity, the negative normalized pairing thus tends to \(\|r_P\|_P^2\). RH is equivalent to cofinal nonnegative pairings there, even with a nonnegative tolerance tending to zero. Proving those signs for the actual residual would establish RH. [Consecutive-prime criteria](MixedPacketDensityTests.lean)

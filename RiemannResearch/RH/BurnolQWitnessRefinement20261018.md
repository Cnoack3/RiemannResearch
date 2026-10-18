# Burnol: discrete transfer and an improved off-critical Q witness

Date: 2026-10-18. Status: independently derived mathematical proof, **not Lean verified**. This is the analytic appendix to the research record. No claim of historical novelty is made.

## 1. Strongest statement first

Write
\[
P(n)=\frac1{n(n+1)},\qquad Q(n)=\frac1{\zeta(2)n^2},\qquad
g_d(n)=\frac{n\bmod d}{d},\quad n\ge1,\ d\ge2.
\]
Use complex Hilbert spaces; the conclusions also apply to real legal combinations. Suppose
\[
\zeta(\rho)=0,\qquad \tfrac12<\beta=\Re\rho<1.
\]
Define
\[
\Delta_\rho(n)=n^{-\rho}-(n+1)^{-\rho},\qquad
S_\rho=\sum_{n\ge1}n^2|\Delta_\rho(n)|^2,
\qquad
B(\beta)=\sum_{n\ge1}\frac1{n^{2\beta}(n+1)}.
\]
Then \(0<S_\rho<\infty\), \(1/2<B(\beta)<1\), and every finite legal combination \(F=\sum_d c_dg_d\), and every \(F\) in their closed linear span in \(L^2(Q)\), satisfies
\[
\boxed{
\|1-F\|_Q^2
\ge \frac1{\zeta(2)S_\rho}
\ge \frac{2\beta-1}{\zeta(2)|\rho|^2B(\beta)}
\ge \frac{4\beta(2\beta-1)}{\zeta(2)|\rho|^2(2\beta+1)}.
}
\]
The first denominator is the exact norm of the stated dual witness; it is not asserted to be the full optimal approximation error. The last bound strictly improves the elementary transported bound
\((2\beta-1)/(\zeta(2)|\rho|^2)\), because \(4\beta/(2\beta+1)>1\) when \(\beta>1/2\). The intermediate \(B(\beta)\) bound is stronger still.

The exact identities behind this statement are
\[
L_\rho(f):=\sum_{n\ge1}f(n)\Delta_\rho(n),\qquad
\|L_\rho\|_{(L^2(Q))^*}^2=\zeta(2)S_\rho,
\]
\[
L_\rho(1)=1,\qquad
L_\rho(g_d)=-\zeta(\rho)(d^{-\rho}-d^{-1})=0,
\]
and the exact cell-envelope identity
\[
\boxed{
\sum_{n\ge1}\frac n{n+1}
\int_{1/(n+1)}^{1/n}t^{2\beta-2}\,dt
=\frac{B(\beta)}{2\beta-1}.
}
\]

## 2. Proof: discrete embedding and Mellin annihilation

For \(f:\mathbb N_{\ge1}\to\mathbb C\), define
\[
(Jf)(t)=f(\lfloor1/t\rfloor),\quad 0<t\le1,
\]
and extend \(Jf\) by zero for \(t>1\). Endpoint conventions do not affect any integral. The reciprocal cells
\(C_n=(1/(n+1),1/n]\) have lengths \(P(n)\), so
\[
\|Jf\|_{L^2(0,\infty)}^2=\|f\|_P^2
\le\zeta(2)\|f\|_Q^2.
\]
If \(x=n+u\), \(0\le u<1\), and \(n=kd+r\), \(0\le r<d\), then
\(\{x/d\}-d^{-1}\{x\}=r/d\). Consequently
\[
Jg_d(t)=\left\{\frac1{dt}\right\}-\frac1d\left\{\frac1t\right\},\quad t>0.
\]
Both sides vanish for \(t>1\).

For \(\Re s=\beta>1/2\), the function \(t^{s-1}\) is square integrable on \((0,1)\), because
\(\int_0^1t^{2\beta-2}dt=(2\beta-1)^{-1}\). Thus
\(\int_0^1Jf(t)t^{s-1}dt\) is absolutely convergent for every \(f\in L^2(Q)\). Integration cell by cell gives
\[
L_s(f)=s\int_0^1Jf(t)t^{s-1}dt.
\]
This also proves absolute convergence of the series defining \(L_s(f)\); alternatively, weighted Cauchy--Schwarz below proves it.

The standard fractional-part Mellin identity is
\[
\int_0^\infty\left\{\frac\theta t\right\}t^{s-1}dt
=-\theta^s\frac{\zeta(s)}s,
\quad 0<\Re s<1,\quad\theta>0.
\]
The range \(0<\Re s<1\) ensures absolute convergence at both endpoints. Applying the identity to the displayed formula for \(Jg_d\) yields
\[
L_s(g_d)=-\zeta(s)(d^{-s}-d^{-1}).
\]
At the assumed zero \(s=\rho\), this is zero. Telescoping gives
\(L_\rho(1)=\lim_{N\to\infty}[1-(N+1)^{-\rho}]=1\).

## 3. Proof: exact dual norm and finite energy

With the convention \(\langle f,h\rangle_Q=\sum_nf(n)\overline{h(n)}Q(n)\), the Riesz representative is
\[
h_\rho(n)=\zeta(2)n^2\overline{\Delta_\rho(n)}.
\]
Its squared norm is exactly \(\zeta(2)S_\rho\), provided the latter is finite. Weighted Cauchy--Schwarz consequently gives
\[
|L_\rho(f)|^2\le\zeta(2)S_\rho\|f\|_Q^2.
\]

For finiteness, set \(a=2\beta-1>0\). On each reciprocal cell,
\[
\frac{\Delta_\rho(n)}\rho=\int_{C_n}t^{\rho-1}dt.
\]
Cauchy--Schwarz on that cell gives
\[
\frac{|\Delta_\rho(n)|^2}{|\rho|^2}
\le \frac1{n(n+1)}\int_{C_n}t^{a-1}dt.
\]
Therefore
\[
\frac{S_\rho}{|\rho|^2}
\le\sum_{n\ge1}\frac n{n+1}\int_{C_n}t^{a-1}dt
=\frac1a\sum_{n\ge1}\frac n{n+1}\bigl(n^{-a}-(n+1)^{-a}\bigr).
\]
To evaluate this envelope, put \(A_n=n/(n+1)\), \(b_n=n^{-a}\). Finite summation by parts gives
\[
\sum_{n=1}^N A_n(b_n-b_{n+1})
=\frac12+\sum_{n=2}^N\frac{n^{-a}}{n(n+1)}
-\frac N{N+1}(N+1)^{-a}.
\]
The last term tends to zero. Hence the sum is
\[
\frac12+\sum_{n\ge2}\frac1{n^{a+1}(n+1)}=B(\beta),
\]
proving
\(S_\rho\le |\rho|^2B(\beta)/(2\beta-1)<\infty\).
The term \(n=1\) in \(B(\beta)\) is \(1/2\), and the remaining terms are positive. Since \(2\beta>1\), termwise comparison with
\(\sum_{n\ge1}1/[n(n+1)]=1\) gives \(B(\beta)<1\). Also \(S_\rho>0\), because otherwise every \(\Delta_\rho(n)\) would vanish, contradicting their telescoping sum 1.

Finally \(L_\rho(1-F)=1\) for legal \(F\). Cauchy--Schwarz gives the first bound. Continuity of \(L_\rho\) extends annihilation to the closed legal span.

For a finite numerical certificate, any integer \(M\ge1\) gives the explicit tail estimate
\[
\boxed{
S_\rho\le\sum_{n=1}^M n^2|\Delta_\rho(n)|^2
+\frac{|\rho|^2 M^{1-2\beta}}{2\beta-1}.
}
\]
Indeed, \(\Delta_\rho(n)=\rho\int_n^{n+1}x^{-\rho-1}dx\) implies
\(n^2|\Delta_\rho(n)|^2\le |\rho|^2n^{-2\beta}\), and the positive decreasing tail satisfies
\(\sum_{n>M}n^{-2\beta}\le\int_M^\infty x^{-2\beta}dx\).
Interval-certified evaluations of the finite sum therefore suffice to give a rigorous upper bound on the exact witness denominator.

## 4. Proof of the elementary improvement

For \(t\in C_n\), \(t\le1/n\), hence
\[
\frac n{n+1}\le\frac1{1+t}\le1-\frac t2,
\qquad 0<t\le1.
\]
The second inequality follows by multiplying by \(1+t\):
\((1-t/2)(1+t)-1=t(1-t)/2\ge0\).
Integrating the envelope yields
\[
\frac{B(\beta)}{2\beta-1}
\le\int_0^1t^{2\beta-2}(1-t/2)dt
=\frac1{2\beta-1}-\frac1{4\beta}
=\frac{2\beta+1}{4\beta(2\beta-1)}.
\]
All denominators are positive. Inverting the resulting bound for \(S_\rho\) establishes the last inequality in Section 1. No special-function representation is needed.

## 5. Burnol's lower bound transferred to legal P and Q atoms

Burnol's paper uses \(K=L^2(0,\infty;dt)\), target \(\chi=1_{(0,1]}\), and
\[
B_\lambda=\operatorname{span}\bigl\{t\mapsto\{\theta/t\}:\lambda\le\theta\le1\bigr\},
\quad D(\lambda)=\operatorname{dist}(\chi,B_\lambda).
\]
Let \(S\subseteq\{2,\dots,L\}\), and define the squared discrete distances
\[
\varepsilon_P(S)=\inf_{F\in\operatorname{span}\{g_d:d\in S\}}\|1-F\|_P^2,
\quad
\varepsilon_Q(S)=\inf_{F\in\operatorname{span}\{g_d:d\in S\}}\|1-F\|_Q^2.
\]
The embedding identity shows that \(JF\in B_{1/L}\). Thus
\[
\boxed{\varepsilon_P(S)\ge D(1/L)^2.}
\]
The pointwise comparison
\[
\frac1{\zeta(2)}P(n)\le Q(n)\le\frac2{\zeta(2)}P(n)
\]
gives
\[
\boxed{\varepsilon_Q(S)\ge\frac{D(1/L)^2}{\zeta(2)}.}
\]
The inequality direction matters: the continuous space is larger. An upper bound for Burnol's continuous distance does not by itself supply an upper bound for either discrete distance, still less for squarefree-only approximation.

Let
\[
C_{\rm B}=\sum_{\substack{\zeta(\rho)=0\\\Re\rho=1/2\text{, distinct}}}
\frac{m_\rho^2}{|\rho|^2}.
\]
Burnol's theorem gives the unconditional statement
\(\liminf_{\lambda\downarrow0}D(\lambda)^2\log(1/\lambda)\ge C_{\rm B}\).
Under RH this sum runs over every nontrivial zero. If RH fails, the positive limiting approximation obstruction makes the rescaled distance diverge, so the lower-bound statement remains valid. Consequently, for any sequence \(L_j\to\infty\) and any \(S_j\subseteq\{2,\dots,L_j\}\),
\[
\liminf_j(\log L_j)\varepsilon_P(S_j)\ge C_{\rm B},
\qquad
\liminf_j(\log L_j)\varepsilon_Q(S_j)\ge C_{\rm B}/\zeta(2).
\]

In the squarefree primorial setup,
\(L_M=\prod_{j\le M}p_j\) and \(S_M=\{d:d\mid L_M,\ d>1\}\), the relevant cutoff is \(L_M\). The logarithm is
\(\log L_M=\sum_{j\le M}\log p_j\), **not** \(\log M\), and is not automatically the logarithm of the number \(2^M-1\) of legal atoms. In the alternative squarefree cutoff \(S_N=\{d\le N:d\text{ squarefree},d\ge2\}\), the correct logarithm is \(\log N\).

## 6. Research meaning and remaining gap

1. The Q witness is a quantitative obstruction attached to a hypothetical off-critical zero. Its strengthened constant comes from compressing the Mellin kernel onto reciprocal cells before measuring its dual norm in Q. It uses the actual Q geometry rather than only global norm equivalence.
2. Every stated lower bound applies to all-conductor and squarefree legal spaces, since each witness annihilates every legal atom individually. No squarefree closure equivalence is needed for the bounds.
3. A rigorously computed candidate with error \(e\) excludes a zero \(\rho\) whenever the displayed Q lower bound exceeds \(e\). This is a valid zero-exclusion certificate; it is not an RH proof.
4. Burnol's lower bound forbids error \(o(1/\log L)\) for legal candidates with maximal conductor at most \(L\). Faster decay in a stage index can only be assessed after its conductor growth is specified.
5. Proving any unconditional upper bound \(\varepsilon_Q(S_j)\to0\) for legal spaces would rule out all zeros with real part greater than one half by the witness above. Obtaining that upper bound, or an equivalent arithmetic energy estimate, remains the RH-level task. Neither the polynomial toy model nor a lower bound supplies it.
6. A finite family of off-critical zero witnesses can be combined through its exact Gram matrix. This offers a stronger computable lower certificate but requires its own matrix analysis; no multi-zero estimate is claimed as already formalized here.

## 7. Historical source checks

- Jean-François Burnol, *A lower bound in an approximation problem involving the zeros of the Riemann zeta function*, March 2001, arXiv:math/0103058. The uploaded paper was read locally. https://arxiv.org/abs/math/0103058
- Sandro Bettin, J. Brian Conrey, David W. Farmer, *An optimal choice of Dirichlet polynomials for the Nyman--Beurling criterion*, arXiv:1211.5191, 2012; published 2013. https://arxiv.org/html/1211.5191v1

The latter paper obtains the optimal \(1/\log N\) asymptotic for the logarithmically tapered Möbius Dirichlet polynomial assuming RH and a negative second moment bound on \(\zeta'(\rho)\). Its moment assumption also forces simple zeros. It does not furnish an unconditional upper estimate suitable for proving RH. Any transfer of its Dirichlet-polynomial candidate into centered legal atoms must explicitly handle the additional normalization term; it should not be identified with the legal discrete optimizer without that work.

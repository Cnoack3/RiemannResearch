# A projection-stability obstruction inside legal squarefree subspaces

This is a paper proof, not a Lean-verified result. It does **not** refute the
canonical initial squarefree stages. It rules out an estimate derived solely
from squarefree legality, inclusion of the parity atom, and actual residual
forcing.

Let
\[
 Q(n)=\frac1{\zeta(2)n^2},\qquad g_j(n)=\frac{n\bmod j}{j},\qquad
 Bf(n)=\frac{f(n)}{n+1},\qquad a(n)=\frac n{(8+\log n)^2}.
\]
All inner products and norms below are in \(L^2(Q)\). Write \(z=\zeta(2)\),
so \(1<z<2\).

## Theorem

For each prime \(d>3\), define the two-dimensional legal squarefree subspace
\[
 W_d=\operatorname{span}\{g_2,\ g_3+10\sqrt d\,g_d\},
\]
with orthogonal projection \(P_d\), actual residual \(r_d=(I-P_d)1\), and
actual smoothed correction \(b_d=P_dBr_d\). Then:

1. \(\|r_d\|\le1/2\), \(\|b_d\|\le1/8\), and the raw source has
   \(\mathcal D(\sqrt a\,Br_d)\le1/128\).
2. With \(n_d=(d+1)/2\),
   \[
   |b_d(2n_d)-b_d(n_d)|\longrightarrow\infty.
   \]
   Hence no common prime-increment constant works for all these legal
   subspaces, even just at the prime two.
3. \(\mathbb E_Q[a b_d^2]\to\infty\). Consequently
   \(\mathcal D(\sqrt a\,b_d)\to\infty\), using the paper Poincare
   inequality from the handoff.
4. Therefore there is no constant \(C\) valid for all legal squarefree
   subspaces containing \(g_2\) in the proposed transfer estimate
   \[
   \mathcal D(\sqrt a\,PBr)
   \le C\bigl(\mathcal D(\sqrt a\,Br)+\|r\|^2\bigr),
   \qquad r=(I-P)1.
   \]

The same weighted-moment divergence holds with
\(a_k(n)=n/(c+\log n)^k\), for every fixed \(c>0,k>1\).

## 1. High-conductor estimates

For \(d\ge2\),
\[
 0\le g_d(n)\le\min(n/d,1).
\]
The exact first \(d-1\) terms give
\[
 \frac{d-1}{zd}\le d\|g_d\|^2\le\frac3z.
 \tag{A}
\]
For the upper bound, split at \(d\) and use
\(\sum_{n\ge d}n^{-2}\le1/(d-1)\). Thus the head contributes
\((d-1)/(zd)\le1/z\), and the tail contributes at most
\(d/[z(d-1)]\le2/z\).

Likewise
\[
 \mathbb E_Qg_d\le\frac1z
 \left(\frac{H_{d-1}}d+\frac1{d-1}\right),
 \qquad \sqrt d\,\mathbb E_Qg_d\longrightarrow0.
 \tag{B}
\]
In particular, for every bounded fixed \(f\),
\(\langle f,\sqrt d\,g_d\rangle\to0\).

Set \(R=10\), \(t_d=R\sqrt d\,g_d\). Its ordinary norm remains bounded
and bounded away from zero, but its reciprocal-weighted norm vanishes:
\[
 \langle t_d,Bt_d\rangle
 =R^2d\mathbb E_Q\frac{g_d^2}{X+1}
 \le R^2\mathbb E_Qg_d\longrightarrow0.
 \tag{C}
\]
Here \(d g_d(n)/(n+1)\le n/(n+1)\le1\).
Also
\[
 0\le\langle t_d,BJ\rangle\le R/\sqrt d,
 \qquad J=\mathbf1_{2\mid n},
 \tag{D}
\]
since \(g_d(n)/(n+1)\le1/d\).

## 2. Orthogonal coordinates and the actual forcing

Since \(Q(X\text{ odd})=3/4\),
\[
 \|g_2\|^2=3/16,\quad\langle1,g_2\rangle=3/8,
 \quad P_{\operatorname{span}(g_2)}1=2g_2,
 \quad r_2=1-2g_2=J.
\]
Let \(P_2\) be this one-dimensional projection, and put
\[
 \lambda=\frac{\langle g_3,g_2\rangle}{\|g_2\|^2},\quad
 h=(I-P_2)g_3=g_3-\lambda g_2,\quad
 q_d=\frac{\langle t_d,g_2\rangle}{\|g_2\|^2},
 \quad u_d=h+t_d-q_dg_2.
\]
Then \(u_d\perp g_2\) and \(W_d=\operatorname{span}(g_2)\oplus
\operatorname{span}(u_d)\). Moreover \(q_d\to0\),
\(0\le\lambda\le2\), and \(|h(n)|\le1\) for every \(n\).

Write
\[
 G_d=\|u_d\|^2,\quad a_d=\langle J,u_d\rangle,\quad
 D_d=\langle u_d,BJ\rangle,\quad E_d=\langle u_d,Bu_d\rangle.
\]
The following estimates hold:
\[
 \liminf G_d\ge R^2/z,\qquad\limsup G_d\le1+3R^2/z,
 \tag{E}
\]
\[
 a_d\to a=\langle J,g_3\rangle\in[0,1/4],
 \tag{F}
\]
\[
 D_d\ge D=\langle g_3,BJ\rangle\ge\frac1{18z},
 \tag{G}
\]
\[
 E_d\to E=\langle h,Bh\rangle\le\tfrac12\|h\|^2\le1/2.
 \tag{H}
\]
For (E), expand
\[
 G_d=\|h\|^2+\|t_d\|^2+2\langle h,t_d\rangle-q_d^2\|g_2\|^2
\]
and apply (A)-(B). For (F), \(Jg_2=0\), so
\(a_d=\langle J,g_3\rangle+\langle J,t_d\rangle\).
For (G), again \(Jg_2=0\), so
\(D_d=D+\langle t_d,BJ\rangle\ge D\); the single integer \(n=2\)
contributes \((2/3)(1/3)/(4z)=1/(18z)\).
For (H), apply (C), \(q_d\to0\), and Cauchy--Schwarz in the positive
quadratic form \(\langle f,Bf\rangle\).

Consequently, for all sufficiently large primes \(d\), we may use the
explicit bounds
\[
 50/z\le G_d\le M:=303,\quad 0\le a_d\le1/2,
 \quad0\le E_d\le1,\quad0\le q_d\le1.
 \tag{I}
\]
The upper bound follows from \(1+300/z<301\); the harmless constant 303
absorbs the vanishing cross terms.

Now compute the residual and projected correction in these orthogonal
coordinates:
\[
 r_d=J-\frac{a_d}{G_d}u_d,
 \qquad b_d=\gamma_d g_2+\beta_d u_d,
 \qquad
 \boxed{\beta_d=\frac{D_dG_d-a_dE_d}{G_d^2}}.
 \tag{J}
\]
This uses the actual \(r_d=(I-P_d)1\); the source has not been chosen
independently of the projection.

By (G), (I), and \(z<2\),
\[
 D_dG_d-a_dE_d
 \ge\frac{25}{9z^2}-\frac12
 \ge\frac{25}{36}-\frac12=\frac7{36}.
\]
Therefore
\[
 \boxed{\beta_d\ge\beta_0:=\frac7{36M^2}>0.}
 \tag{K}
\]

Since \(W_d\) contains \(g_2\), \(\|r_d\|\le\|J\|=1/2\).
As \(P_dr_d=0\),
\[
 b_d=P_d(B-\tfrac14I)r_d,
 \qquad\|b_d\|\le\tfrac14\|r_d\|\le1/8.
\]
The two components in (J) are orthogonal, so
\[
 |\gamma_d|\le\frac1{2\sqrt3}<1,
 \qquad0<\beta_d\le\frac1{8\sqrt{G_d}}\le1/40.
\]
Consequently we have the uniform pointwise decomposition
\[
 b_d(n)=\beta_dR\sqrt d\,g_d(n)+w_d(n),\qquad |w_d(n)|\le1,
 \tag{L}
\]
because
\(w_d=\gamma_dg_2+\beta_d(h-q_dg_2)\) and
\(|g_2|\le1/2, |h|\le1,q_d\le1\).

## 3. Divergence of the prime-two increment

For odd \(d\), let \(n_d=(d+1)/2\). Then
\[
 g_d(n_d)=\frac{d+1}{2d},\qquad g_d(2n_d)=1/d,
 \qquad g_d(2n_d)-g_d(n_d)=-\frac{d-1}{2d}.
\]
Using (K)-(L),
\[
 |b_d(2n_d)-b_d(n_d)|
 \ge\beta_0R\sqrt d\,\frac{d-1}{2d}-2
 \ge\frac{\beta_0R}4\sqrt d-2\longrightarrow\infty.
\]
The denominator \(\log2\) in a prime-increment estimate is fixed.
In fact the same example defeats every fixed polylogarithmic increment
bound \(L\log2\,(6+\log(2n_d))^m\), since \(\sqrt d\) dominates each
fixed power of \(\log d\).

## 4. Divergence of weighted energy and failure of transfer

For
\(I_d=\{\lceil d/4\rceil,\ldots,\lfloor d/2\rfloor\}\),
there are at least \(d/8\) integers once \(d\ge16\), and
\(g_d(n)=n/d\ge1/4\) on this interval. Thus, for sufficiently large \(d\),
\[
 b_d(n)\ge\beta_0R\sqrt d/4-1
 \ge K\sqrt d,\qquad K:=\beta_0R/8,\quad n\in I_d.
\]
Since \(n\le d\),
\[
 Q(n)a(n)=\frac1{zn(8+\log n)^2}
 \ge\frac1{zd(8+\log d)^2}.
\]
It follows that
\[
 \boxed{\mathbb E_Q[a b_d^2]
 \ge\frac{K^2d}{8z(8+\log d)^2}\longrightarrow\infty.}
\]
The identical calculation gives \(\gg d/(c+\log d)^k\) for any fixed
profile exponent \(k>1\).

Each individual \(b_d\) is bounded and periodic, so its weighted moment
is finite. Its mean after multiplication by \(\sqrt a\) satisfies
\[
 |\mathbb E_Q[\sqrt a\,b_d]|^2\le A\|b_d\|^2\le A/64,
 \quad A=\mathbb E_Qa<\infty.
\]
The handoff's extended Poincare inequality therefore gives
\[
 \mathcal D(\sqrt a\,b_d)\ge\mathbb E_Q[a b_d^2]-A/64\to\infty.
\]
On the other hand, its raw-source estimate gives
\[
 \mathcal D(\sqrt a\,Br_d)\le\|r_d\|^2/32\le1/128,
 \quad
 \mathcal D(\sqrt a\,Br_d)+\|r_d\|^2\le33/128.
\]
No common transfer constant can satisfy the proposed estimate for this
family.

## Why this does not settle the canonical problem

Every \(W_d\) consists of legal squarefree combinations and contains the
parity atom. However it ties the coefficients of \(g_3\) and \(g_d\)
together. It does **not** contain \(g_3\) as an independent direction,
and these subspaces do not form the canonical increasing initial spans.
A canonical stage containing conductors 2, 3, and \(d\) has the additional
independent direction that this construction deliberately omits.

Thus the result isolates a real bottleneck: legality, parity orthogonality,
the quarter contraction, and the universally bounded raw source are
insufficient to prove the desired stability. A successful argument must
use the additional arithmetic/completeness structure of the canonical
squarefree stages, or a weaker cofinal-head property specific to them.

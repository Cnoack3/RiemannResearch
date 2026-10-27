# Uniform control when one conductor is added to a fixed legal space

Paper result; not Lean-verified. The constant depends on the entire fixed
initial space. It does not supply a bound uniform over canonical stages.

Let \(Q(n)=1/(\zeta(2)n^2)\), \(g_d(n)=(n\bmod d)/d\), and
\(Bf(n)=f(n)/(n+1)\). Fix any finite-dimensional space \(U\) consisting of
bounded functions (in particular, any fixed finite legal squarefree span).
For \(d\ge2\), put
\[
 W_d=U+\operatorname{span}(g_d),\quad
 r_d=(I-P_{W_d})1,\quad b_d=P_{W_d}Br_d.
\]
Then there is a finite constant \(C_U\), independent of \(d,n\), such that
\[
 \boxed{|b_d(n)|\le C_U(1+\log n)\qquad(d\ge2,\ n\ge1).}
\]
In the squarefree setting, simply restrict \(d\) to squarefree integers.

## Proof

Write \(z=\zeta(2)\), \(\ell_d=1+\log d\), and fix an orthonormal basis
\(e_1,\ldots,e_k\) of \(U\). Each basis function is bounded.
The elementary bounds
\[
 0\le g_d(n)\le\min(n/d,1),\quad
 \frac{d-1}{zd^2}\le\|g_d\|^2\le\frac3{zd},\quad
 \mathbb E_Qg_d=O(\ell_d/d)
\]
follow by splitting the sum at \(d\). Therefore
\[
 |\langle e_i,g_d\rangle|\le\|e_i\|_\infty\mathbb E_Qg_d,
 \quad \|P_Ug_d\|+\|P_Ug_d\|_\infty=O_U(\ell_d/d).
 \tag{1}
\]
Let
\[
 u_d=(I-P_U)g_d,\quad G_d=\|u_d\|^2,
 \quad r_U=(I-P_U)1.
\]
The function \(r_U\) is bounded. By (1),
\[
 G_d=\|g_d\|^2-\|P_Ug_d\|^2\asymp_U1/d
 \tag{2}
\]
for all sufficiently large \(d\). Thus these \(u_d\) are nonzero.
Define
\[
 a_d=\langle r_U,u_d\rangle=\langle r_U,g_d\rangle,
 \quad D_d=\langle u_d,Br_U\rangle,
 \quad E_d=\langle u_d,Bu_d\rangle.
\]
Boundedness of \(r_U\) gives
\[
 a_d=O_U(\ell_d/d).
 \tag{3}
\]
Furthermore, \(g_d(n)/(n+1)\le1/d\), so
\[
 |\langle g_d,Br_U\rangle|\le\|r_U\|_\infty/d.
\]
Combining this with (1) gives
\[
 D_d=O_U(\ell_d/d).
 \tag{4}
\]
Finally,
\[
 \langle g_d,Bg_d\rangle\le\mathbb E_Qg_d/d
 =O(\ell_d/d^2),
\]
and the quadratic triangle inequality in the positive form induced by
\(B\), together with \(B\le I/2\), gives
\[
 0\le E_d\le2\langle g_d,Bg_d\rangle+
 2\langle P_Ug_d,BP_Ug_d\rangle
 =O_U(\ell_d^2/d^2).
 \tag{5}
\]

Because \(W_d=U\oplus\operatorname{span}(u_d)\), its actual residual and
correction satisfy
\[
 r_d=r_U-\alpha_du_d,\qquad\alpha_d=a_d/G_d=O_U(\ell_d),
\]
\[
 b_d=P_UBr_d+\beta_du_d,
 \qquad\beta_d=\frac{D_d-\alpha_dE_d}{G_d}.
\]
Equations (2)-(5) imply
\[
 \beta_d=O_U(\ell_d)+O_U(\ell_d^3/d)=O_U(\ell_d),
 \tag{6}
\]
since \(\ell_d^2/d\) is bounded.

For every orthogonal projection \(P\), if \(r=(I-P)1\), then
\[
 PBr=P(B-I/4)r,\qquad\|PBr\|\le\|r\|/4\le1/4.
\]
Consequently \(\|P_UBr_d\|\le1/4\), since \(P_UBr_d=P_Ub_d\). Finite dimensionality of the fixed
bounded-function space \(U\) supplies a uniform sup-norm bound on this
term. Also (1) and (6) imply
\(\|\beta_dP_Ug_d\|_\infty=O_U(\ell_d^2/d)=O_U(1)\).
Therefore, uniformly over large \(d\),
\[
 |b_d(n)|\le C_U\bigl(1+\ell_d\min(n/d,1)\bigr).
\]
For \(n\ge1\),
\[
 (1+\log d)\min(n/d,1)\le2+\log n.
\]
Indeed, for \(d\le n\) this is immediate. For \(d>n\), write
\(d=nx\), \(x>1\), and use
\((1+\log n+\log x)/x\le1+\log n+1/e\).
This proves the claimed envelope for all sufficiently large \(d\).
The finitely many remaining \(d\) can be absorbed into \(C_U\), since
each \(b_d\) belongs to the bounded-function space \(W_d\).

## Consequence and remaining bottleneck

For every fixed \(k>3\),
\[
 \sup_{d\ge2}\mathbb E_Q\left[
 \frac{X}{(c+\log X)^k}b_d(X)^2\right]<\infty
 \qquad(c>0).
\]
This follows from the envelope and convergence of
\(\sum_{n\ge2}1/[n(\log n)^{k-2}]\).

The result controls an arbitrarily distant new conductor once the previous
space is fixed. For canonical stages, however, that previous space grows.
The proof uses boundedness constants for an orthonormal basis of \(U\),
namely quantities such as \(\sum_i\|e_i\|_\infty^2\). No bound uniform in
that growing space has been proved. Those constants encode precisely the
inverse-Gram/conditioning difficulty in the original research agenda.

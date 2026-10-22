# Coefficient stabilization and exact characterization of the Möbius limits

September 18, 2026. Self-contained written proof. No RH assumption, approximation-to-one assumption, or Lean verification is used. The assertion that the limiting coefficients actually equal the Möbius targets is not proved.

Formalization update (September 19, 2026): the combined Lean development has passed kernel checking; the RH hypotheses remain open.

## Setting

Let
\[
w_n=\frac1{n(n+1)},\qquad
H=\left\{f:\mathbb N_{\ge1}\to\mathbb R:
\sum_{n\ge1}w_nf(n)^2<\infty\right\},
\qquad
\langle f,h\rangle_H=\sum_{n\ge1}w_nf(n)h(n).
\]
The constant sequence \(\mathbf1\) has squared norm one, since the weight series telescopes. Every coordinate evaluation is continuous:
\[
|f(j)|\le\sqrt{j(j+1)}\,\|f\|_H.
\tag{1}
\]
When a difference at zero is needed, extend each sequence by \(f(0)=0\); in particular the extended target has \(\mathbf1(0)=0\).

For \(d\ge2\), define
\[
g_d(n)=\frac{n\bmod d}{d}
      =\frac nd-\left\lfloor\frac nd\right\rfloor.
\]
These bounded sequences belong to \(H\). Put
\[
V_N=\operatorname{span}_{\mathbb R}\{g_2,\ldots,g_N\},\qquad
W=\overline{\bigcup_{N\ge2}V_N}^{\,H}.
\]
Let \(P_N\) be the orthogonal projection of \(\mathbf1\) onto \(V_N\), and set
\[
E_N=\|\mathbf1-P_N\|_H^2.
\]
We will prove that the expansion \(P_N=\sum_{d=2}^Nc_{N,d}g_d\) is unique.

These are exact projections for the full infinite Pareto norm. They are not defined by truncating the norm, and the results do not automatically apply to rounded computational witnesses.

## Theorem

There are \(P_\infty\in W\), \(r_\infty=\mathbf1-P_\infty\in W^\perp\), and \(E_\infty=\|r_\infty\|_H^2\) such that:

1. \(P_N\to P_\infty\) strongly in \(H\), and exactly
   \[
   E_N=E_\infty+\|P_\infty-P_N\|_H^2.
   \tag{2}
   \]
2. For every fixed \(m\ge2\), the coefficient \(c_{N,m}\), defined for \(N\ge m\), converges to a real number \(c_{\infty,m}\).
3. The limiting coefficient has the exact finite formula
   \[
   \boxed{c_{\infty,m}=-\mu(m)+
   \sum_{k\mid m}\mu(m/k)
   \bigl(r_\infty(k)-r_\infty(k-1)\bigr).}
   \tag{3}
   \]
4. With the explicit constant \(C_m\) defined below,
   \[
   |c_{N,m}-c_{\infty,m}|^2\le C_m^2(E_N-E_\infty),
   \tag{4}
   \]
   and
   \[
   |c_{\infty,m}+\mu(m)|^2\le C_m^2E_\infty.
   \tag{5}
   \]
5. The following statements are equivalent:
   \[
   \boxed{
   \bigl[\forall m\ge2,\ c_{\infty,m}=-\mu(m)\bigr]
   \iff r_\infty=0
   \iff E_\infty=0
   \iff \mathbf1\in W
   \iff E_N\longrightarrow0.
   }
   \tag{6}
   \]

All five conclusions, including the equivalence, are unconditional. They do not assert that the equivalent conditions in (6) hold.

## Proof: exact coefficient recovery

For any sequence \(f\), extended by \(f(0)=0\), define the finite linear functional
\[
L_m(f)=\sum_{k\mid m}\mu(m/k)\bigl(f(k)-f(k-1)\bigr).
\tag{7}
\]
For a finite legal sum \(F=\sum_{d\ge2}c_dg_d\), put \(s=\sum_dc_d/d\). The floor differences give exactly
\[
F(n)-F(n-1)=s-\sum_{\substack{d\mid n\\d\ge2}}c_d.
\tag{8}
\]
If \(m\ge2\), then
\[
\begin{aligned}
L_m(F)
&=s\sum_{k\mid m}\mu(m/k)
-\sum_{\substack{d\mid m\\d\ge2}}c_d
  \sum_{\substack{k\mid m\\d\mid k}}\mu(m/k)\\
&=-c_m.
\end{aligned}
\tag{9}
\]
Here the first divisor sum vanishes. The inner sum in the second expression is
\(\sum_{j\mid m/d}\mu((m/d)/j)\), equal to one when \(d=m\) and zero otherwise. Missing coefficients are interpreted as zero. In particular
\[
L_m(g_d)=-\mathbf1_{m=d}\qquad(m,d\ge2).
\tag{10}
\]
Applying (9) to a zero linear combination proves linear independence of the legal atoms, and hence uniqueness of all finite coefficients.

For an explicit continuity constant, define for \(j\ge1\)
\[
\beta_{m,j}=
\begin{cases}\mu(m/j),&j\mid m,\\0,&j\nmid m,\end{cases}
\qquad
A_{m,j}=\beta_{m,j}-\beta_{m,j+1}.
\]
Grouping the finite terms of (7), with \(f(0)=0\), gives
\[
L_m(f)=\sum_{j=1}^mA_{m,j}f(j).
\]
Thus, on putting
\[
\boxed{C_m^2=\sum_{j=1}^m j(j+1)A_{m,j}^2,}
\tag{11}
\]
weighted Cauchy–Schwarz gives
\[
|L_m(f)|^2\le C_m^2\|f\|_H^2.
\tag{12}
\]
In fact \(C_m\) is the exact operator norm of \(L_m\): its Riesz representer is the finitely supported sequence \(v_m(j)=j(j+1)A_{m,j}\). This representer has squared norm \(C_m^2\). It is nonzero because \(A_{m,m}=1\).

Finally, because the extended target has first difference equal to one at \(n=1\) and zero elsewhere,
\[
L_m(\mathbf1)=\mu(m).
\tag{13}
\]
Combining (9) and (13) already gives, for \(r_N=\mathbf1-P_N\), the exact finite identity
\[
c_{N,m}+\mu(m)=L_m(r_N)\qquad(N\ge m).
\tag{14}
\]

## Proof: strong projection convergence and coefficient stabilization

For \(M\ge N\), projection orthogonality implies
\[
P_M-P_N\perp V_N.
\]
Indeed, for \(v\in V_N\subseteq V_M\), both \(\langle P_M,v\rangle\) and \(\langle P_N,v\rangle\) equal \(\langle\mathbf1,v\rangle\). Therefore
\[
\|P_M-P_N\|_H^2=\|P_M\|_H^2-\|P_N\|_H^2.
\tag{15}
\]
Also
\[
E_N+\|P_N\|_H^2=\|\mathbf1\|_H^2=1.
\tag{16}
\]
Consequently the squared projection norms increase to a limit at most one. Equation (15) makes \((P_N)\) Cauchy. Completeness of \(H\) gives a strong limit \(P_\infty\in W\).

For any \(v\in V_M\), \(\langle\mathbf1-P_N,v\rangle=0\) for all \(N\ge M\). Passing to the limit and then using density of the union shows \(r_\infty=\mathbf1-P_\infty\perp W\). Hence \(P_\infty\) is exactly the projection onto \(W\).

The decomposition
\[
\mathbf1-P_N=r_\infty+(P_\infty-P_N)
\]
has orthogonal summands. This proves (2), including \(E_N\downarrow E_\infty\).

By (9) and continuity of \(L_m\),
\[
c_{N,m}=-L_m(P_N)\longrightarrow-L_m(P_\infty)=:c_{\infty,m}.
\tag{17}
\]
This proves unconditional coefficient stabilization. Equation (12) and the exact energy difference give
\[
|c_{M,m}-c_{N,m}|^2\le C_m^2(E_N-E_M)
\qquad(M\ge N\ge m),
\tag{18}
\]
and, on letting \(M\to\infty\), prove (4).

## Proof: exact limiting values and their characterization

Using \(P_\infty=\mathbf1-r_\infty\) in (17), followed by (13), gives
\[
c_{\infty,m}=-\mu(m)+L_m(r_\infty).
\tag{19}
\]
Expanding the finite functional proves (3), and (12) proves (5).

If \(r_\infty=0\), formula (19) gives all the desired values. For the converse, assume solely that
\[
c_{\infty,m}=-\mu(m)\quad\text{for every }m\ge2.
\tag{20}
\]
Then \(L_m(r_\infty)=0\) for every \(m\ge2\). Define
\[
a(n)=r_\infty(n)-r_\infty(n-1),\qquad
b(n)=\sum_{k\mid n}\mu(n/k)a(k).
\]
Condition (20) says \(b(n)=0\) for \(n\ge2\), whereas \(b(1)=r_\infty(1)\). Finite Möbius inversion gives
\[
a(n)=\sum_{d\mid n}b(d)=r_\infty(1)
\quad\text{for every }n\ge1.
\]
Telescoping now gives the exact sequence identity
\[
r_\infty(n)=n\,r_\infty(1).
\tag{21}
\]
Since \(r_\infty\in H\), this forces \(r_\infty(1)=0\): otherwise its squared norm would be
\[
r_\infty(1)^2\sum_{n\ge1}\frac{n}{n+1}=\infty.
\]
Thus \(r_\infty=0\). The remaining equivalences in (6) follow from (2) and the orthogonal projection characterization. This completes the proof.

## Examples of the residual correction

For illustration, all the following identities are exact:
\[
\begin{aligned}
c_{\infty,2}&=1+r_\infty(2)-2r_\infty(1),\\
c_{\infty,3}&=1+r_\infty(3)-r_\infty(2)-r_\infty(1),\\
c_{\infty,4}&=r_\infty(4)-r_\infty(3)-r_\infty(2)+r_\infty(1).
\end{aligned}
\]
In particular \(C_2^2=14\), so
\[
|c_{N,2}-c_{\infty,2}|^2\le14(E_N-E_\infty),
\qquad
|c_{\infty,2}-1|^2\le14E_\infty.
\]
The correction terms have not been shown to vanish.

## Scope and remaining assertion

This proof uses only finite divisor identities and elementary Hilbert-space geometry. In particular it requires no estimate for Möbius summatory functions, no subpolynomial energy bound, and no infinite Ramanujan expansion.

The coefficient limits are recovered by continuous finite-coordinate functionals. Their existence does not assert convergence of an infinite series \(\sum_{d\ge2}c_{\infty,d}g_d\) to \(P_\infty\). No such series representation is used.

The same inversion argument proves that the functionals \(L_m\), \(m\ge2\), jointly separate points of \(H\). This does not establish density of the legal atoms \(g_d\); the functionals' Riesz representers and the legal atoms are different families.

The precise remaining assertion is
\[
\forall m\ge2,\quad L_m(r_\infty)=0.
\]
By the theorem this is equivalent to vanishing of the actual projection residual. It is not asserted here, and no unconditional convergence rate to the Möbius values is claimed. The central results have since been formalized in `MobiusHilbertCoordinates.lean` and `MobiusCoefficientStabilization.lean`; see `RH_Coefficient_Lean_Integration_2026-09-19.md` for the verification record and conditional RH connection.

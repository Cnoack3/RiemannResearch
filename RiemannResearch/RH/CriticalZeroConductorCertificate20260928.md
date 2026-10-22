# Critical-zero certificates for the arithmetic projection DPP

**Status: rigorous on-paper results; no Lean verification is claimed for this note.**

The argument below uses the established residue Mellin identity and a zero of the Riemann zeta function on the critical line. It makes no RH assumption and requires no estimate on inverse Gram coefficients. It gives explicit finite-conductor lower bounds, a multizero certificate, and an infinite-mean entrance-time theorem. These are restrictions on possible convergence rates, not the upper bounds needed to prove RH.

The parameter is the conductor \(L_N=\operatorname{lcm}(2,\ldots,N)\). This is a weaker asymptotic scale than the classical \(\log N\) Nyman–Beurling lower bounds of Burnol. The contribution here is the direct finite certificate, its explicit constant, and its exact translation to the arithmetic DPP; no novelty over the classical theory is asserted.

## 1. Definitions and the claims

Let
\[
w_n=\frac1{n(n+1)},\qquad
H=\ell^2(\mathbb N_{\ge1},w),\qquad
g_d(n)=\frac{n\bmod d}{d},
\]
\[
V_N=\operatorname{span}_{\mathbb R}\{g_2,\ldots,g_N\},\qquad
D_N=\|\mathbf1-P_{V_N}\mathbf1\|_H^2,\qquad N\ge2.
\]
Let \(Q_N\) be the counting-measure kernel of the orthogonal projection onto \(UV_N\), where
\[
(Uf)(n)=\sqrt{w_n}\,f(n).
\]
Let \(\Xi_N\) have this projection DPP law, and set
\[
p_N=\mathbb P(1\notin\Xi_N)=1-Q_N(1,1).
\]

We may complexify \(H\) and \(V_N\) when constructing annihilating vectors. This does not change any distance from a real target or the projection kernel: for real \(f,u,v\),
\[
\|f-(u+iv)\|_H^2=\|f-u\|_H^2+\|v\|_H^2.
\]
All matrix adjoints below are conjugate transposes, and \(x^*x\) is the Euclidean squared norm.

Fix a zero \(\rho=\tfrac12+it\) of \(\zeta\), and write
\[
a_\rho=\frac{|1-2^{-\rho}|}{|\rho|}>0.
\]
The positivity follows from \(|2^{-\rho}|=2^{-1/2}<1\).

**Theorem 1: explicit finite bounds.** If \(L\ge2\) is any common multiple of \(2,\ldots,N\), then
\[
\boxed{D_N\ge\frac1{|\rho|^2(\log L+24)}}\tag{1}
\]
and
\[
\boxed{
 p_N\ge
 \frac{2}{(1+4/L^2)^2}
 \frac{\bigl(a_\rho-3L^{-3/2}\bigr)_+^2}{\log L+24}.
}\tag{2}
\]
Here \(x_+=\max(x,0)\).

**Theorem 2: finite collections of critical zeros.** For every finite set \(Z\) of distinct critical-line zeros,
\[
\boxed{
\liminf_{N\to\infty}(\log L_N)D_N
\ge\sum_{\rho\in Z}\frac1{|\rho|^2}
}\tag{3}
\]
and
\[
\boxed{
\liminf_{N\to\infty}(\log L_N)p_N
\ge2\sum_{\rho\in Z}\frac{|1-2^{-\rho}|^2}{|\rho|^2}.
}\tag{4}
\]
No simplicity assumption is made: each distinct zero is used once. In particular, when \(t\ne0\), using both \(\rho\) and \(\overline\rho\) doubles the single-zero constants.

**Theorem 3: infinite mean.** In every coupling in which the first-site occupation indicators increase with \(N\), let
\[
\tau_1=\inf\{N\ge2:1\in\Xi_N\},
\qquad\inf\varnothing=\infty.
\]
Then
\[
\boxed{\mathbb E[\tau_1]=\infty.}\tag{5}
\]
This applies, in particular, to any nested coupling of the complete DPP configurations. A monotone coupling of the first-site indicators alone always exists, as proved below. Thus the statement does not require a new construction of a spatial coupling.

## 2. The Mellin annihilator

For \(\Re s>0\), \(s\ne0\), define the Mellin cell
\[
m_s(n)=\int_n^{n+1}x^{-s-1}\,dx
=\frac{n^{-s}-(n+1)^{-s}}s.
\tag{6}
\]
For the critical zero under consideration,
\[
|m_\rho(n)|\le\int_n^{n+1}x^{-3/2}\,dx\le n^{-3/2}.
\tag{7}
\]
Consequently all sums below involving a bounded periodic sequence and \(m_\rho(n)\) converge absolutely.

The residue Mellin formula is
\[
\sum_{n\ge1}g_d(n)m_s(n)
=\frac{\zeta(s)}s\bigl(d^{-1}-d^{-s}\bigr),
\qquad 0<\Re s<1.
\tag{8}
\]
For completeness, the fractional-part identity
\[
g_d(\lfloor x\rfloor)=\{x/d\}-d^{-1}\{x\},\qquad x\ge1,
\]
follows on writing \(x=n+u\), \(0\le u<1\). Euler summation gives
\[
I(s):=\int_1^\infty\{x\}x^{-s-1}\,dx
=\frac1{s-1}-\frac{\zeta(s)}s,
\qquad \Re s>0,\ s\ne1.
\]
Also, for \(0<\Re s<1\), substitution \(x=du\) gives
\[
\int_1^\infty\{x/d\}x^{-s-1}\,dx
=d^{-s}\left(\frac{1-d^{s-1}}{1-s}+I(s)\right).
\]
Subtracting \(d^{-1}I(s)\) proves (8). Evaluating at \(s=\rho\) yields the exact annihilation
\[
\sum_{n\ge1}g_d(n)m_\rho(n)=0.
\tag{9}
\]
The sum without a residue factor telescopes:
\[
\sum_{n\ge1}m_\rho(n)=\frac1\rho.
\tag{10}
\]

The formal full-space Mellin vector \(\overline{m_\rho(n)}/\sqrt{w_n}\) is not square summable; its squared modulus is asymptotic to \(1/n\). We do not use it as an element of \(\ell^2\). Instead we compress its absolutely convergent functional to the finite space of periodic functions.

## 3. Exact compression to residue classes

Fix a common multiple \(L\) of the moduli \(2,\ldots,N\). For \(1\le r\le L\), define
\[
W_L(r)=\sum_{k\ge0}w_{r+kL},
\qquad
A_{\rho,L}(r)=\sum_{k\ge0}m_\rho(r+kL).
\tag{11}
\]
The sums converge absolutely, \(W_L(r)>0\), and
\[
\sum_{r=1}^LW_L(r)=1,
\qquad
\sum_{r=1}^LA_{\rho,L}(r)=\frac1\rho.
\tag{12}
\]
The map from \(L\)-periodic functions to \(\mathbb C^L\),
\[
f\longmapsto \bigl(\sqrt{W_L(r)}f(r)\bigr)_{r=1}^L,
\tag{13}
\]
is an isometry. Let \(\overline Q_{N,L}\) be the Euclidean orthogonal projection onto the span of the vectors
\[
\bigl(\sqrt{W_L(r)}g_d(r)\bigr)_{r=1}^L,
\qquad 2\le d\le N.
\]
Residue \(r=L\) is included: every feature vanishes there, so the corresponding row and column of \(\overline Q_{N,L}\) are zero.

Define the column vector
\[
c_{\rho,L}(r)=\frac{\overline{A_{\rho,L}(r)}}{\sqrt{W_L(r)}},
\qquad
S_{\rho,L}=c_{\rho,L}^*c_{\rho,L}
=\sum_{r=1}^L\frac{|A_{\rho,L}(r)|^2}{W_L(r)}.
\tag{14}
\]
This conjugation convention is fixed throughout. For a feature column \(u_d(r)=\sqrt{W_L(r)}g_d(r)\), absolute convergence and periodicity give
\[
c_{\rho,L}^*u_d
=\sum_{r=1}^LA_{\rho,L}(r)g_d(r)
=\sum_{n\ge1}m_\rho(n)g_d(n)=0.
\]
Thus
\[
\overline Q_{N,L}c_{\rho,L}=0.
\tag{15}
\]
Let \(b_L=(\sqrt{W_L(r)})_{r=1}^L\), the image of \(\mathbf1\). By (12),
\[
c_{\rho,L}^*b_L=\frac1\rho.
\]
In particular, \(S_{\rho,L}>0\). Since \(c_{\rho,L}\) is in the orthogonal complement of the feature space, Cauchy–Schwarz gives
\[
\boxed{D_N\ge\frac1{|\rho|^2S_{\rho,L}}.}\tag{16}
\]

There is a second exact consequence. For the first standard basis vector \(e_1\in\mathbb C^L\),
\[
1-\overline Q_{N,L}(1,1)
\ge\frac{|c_{\rho,L}^*e_1|^2}{S_{\rho,L}}
=\frac{|A_{\rho,L}(1)|^2}{W_L(1)S_{\rho,L}}.
\tag{17}
\]
The physical-site and residue-class occupancy probabilities are different. An orthonormal basis of periodic feature functions gives the exact relation
\[
Q_N(1,1)=\frac{w_1}{W_L(1)}\overline Q_{N,L}(1,1),
\qquad w_1=\frac12.
\tag{18}
\]
Combining (17)–(18),
\[
\boxed{
 p_N\ge1-\frac{w_1}{W_L(1)}
 +\frac{w_1}{W_L(1)^2}
  \frac{|A_{\rho,L}(1)|^2}{S_{\rho,L}}.
}\tag{19}
\]
The first term is nonnegative. Formula (19) retains the exact conditional-lift correction.

## 4. Proof of the constant \(24\)

Integral comparison gives
\[
\sum_{k\ge1}k^{-3/2}\le3,
\qquad
\sum_{k\ge1}k^{-2}\le2.
\]
For \(1\le r\le L\), (7) therefore implies
\[
|A_{\rho,L}(r)-m_\rho(r)|
\le\sum_{k\ge1}(r+kL)^{-3/2}
\le3L^{-3/2},
\tag{20}
\]
and
\[
0\le W_L(r)-w_r
\le\sum_{k\ge1}(r+kL)^{-2}
\le2L^{-2}.
\tag{21}
\]
Using \(W_L(r)\ge w_r\),
\[
\begin{aligned}
S_{\rho,L}
&\le\sum_{r=1}^Lr(r+1)
       \bigl(r^{-3/2}+3L^{-3/2}\bigr)^2\\
&=\sum_{r=1}^L\left(\frac1r+\frac1{r^2}\right)
 +6L^{-3/2}\sum_{r=1}^L\left(r^{1/2}+r^{-1/2}\right)
 +9L^{-3}\sum_{r=1}^Lr(r+1).
\end{aligned}
\tag{22}
\]
The three terms have the following bounds when \(L\ge2\):
\[
\sum_{r=1}^L\frac1r\le\log L+1,
\qquad\sum_{r=1}^L\frac1{r^2}\le2;
\]
\[
\sum_{r=1}^Lr^{1/2}\le L^{3/2},
\qquad\sum_{r=1}^Lr^{-1/2}\le2\sqrt L;
\]
\[
9L^{-3}\sum_{r=1}^Lr(r+1)
=\frac{3(L+1)(L+2)}{L^2}\le9.
\]
Hence the cross term is at most \(6+12/L\le12\), and
\[
\boxed{S_{\rho,L}\le\log L+24.}\tag{23}
\]
Substituting in (16) proves (1).

For the first-site bound, (20) and (6) give
\[
|A_{\rho,L}(1)|
\ge\bigl(a_\rho-3L^{-3/2}\bigr)_+.
\]
Also (21) implies
\[
\frac{w_1}{W_L(1)^2}
\ge\frac{1/2}{(1/2+2L^{-2})^2}
=\frac2{(1+4/L^2)^2}.
\]
Discarding the nonnegative first term in (19) and using (23) proves (2).

## 5. Several zeros: the exact matrix certificate

Let \(Z=\{\rho_1,\ldots,\rho_k\}\) consist of distinct critical-line zeros. Form the \(L\times k\) matrix \(C_L\) whose columns are \(c_{\rho_j,L}\). Its Gram matrix is
\[
H_L=C_L^*C_L,
\qquad
(H_L)_{\rho\sigma}
=\sum_{r=1}^L
\frac{A_{\rho,L}(r)\overline{A_{\sigma,L}(r)}}{W_L(r)}.
\tag{24}
\]
Thus these are row-Gram entries for the unconjugated \(A\)-values, obtained from the explicitly conjugated columns \(C_L\).

If \(H_L\) is invertible, the orthogonal projection onto \(\operatorname{range}C_L\) is \(C_LH_L^{-1}C_L^*\). This range is contained in \(\ker\overline Q_{N,L}\), so
\[
I-\overline Q_{N,L}\succeq C_LH_L^{-1}C_L^*.
\tag{25}
\]
Define column vectors
\[
v=(1/\rho)_{\rho\in Z},
\qquad a_L=(A_{\rho,L}(1))_{\rho\in Z}.
\]
Because \(C_L^*b_L=v\) and \(C_L^*e_1=a_L/\sqrt{W_L(1)}\), (25) gives the precise quadratic inequalities
\[
\boxed{D_N\ge v^*H_L^{-1}v}\tag{26}
\]
and
\[
\boxed{
 p_N\ge1-\frac{w_1}{W_L(1)}
 +\frac{w_1}{W_L(1)^2}a_L^*H_L^{-1}a_L.
}\tag{27}
\]
We next prove that \(H_L\) is invertible for all sufficiently large \(L\) and determine its leading term.

## 6. Complete proof of the Gram asymptotic

For fixed critical-line points \(\rho,\sigma\), we claim
\[
(H_L)_{\rho\sigma}
=\sum_{r=1}^L\frac{m_\rho(r)\overline{m_\sigma(r)}}{w_r}+O(1),
\tag{28}
\]
where the first error bound may be chosen independently of the two ordinates.

Indeed, write \(b_\rho(r)=A_{\rho,L}(r)-m_\rho(r)\). By (7) and (20),
\[
\left|A_{\rho,L}(r)\overline{A_{\sigma,L}(r)}
-m_\rho(r)\overline{m_\sigma(r)}\right|
\le6r^{-3/2}L^{-3/2}+9L^{-3}.
\]
After dividing by \(W_L(r)\ge w_r\) and summing, the right side is at most \(12+9=21\), by the estimates in (22). The denominator replacement contributes at most
\[
\begin{aligned}
\sum_{r=1}^L|m_\rho(r)m_\sigma(r)|
 \left|\frac1{W_L(r)}-\frac1{w_r}\right|
&\le2L^{-2}\sum_{r=1}^Lr^{-3}[r(r+1)]^2\\
&=2L^{-2}\sum_{r=1}^L(r+2+r^{-1})\\
&\le1+\frac7L\le\frac92.
\end{aligned}
\]
Here we used \(\sum_{r\le L}1/r\le L\). Thus the absolute difference in (28) is at most \(26\) for every \(L\ge2\).

Next, the fundamental theorem of calculus gives
\[
\left|m_\rho(r)-r^{-\rho-1}\right|
\le\frac{|\rho+1|}{2}r^{-5/2}.
\tag{29}
\]
To see this, bound the derivative of \(x^{-\rho-1}\) on \([r,r+1]\) by \(|\rho+1|r^{-5/2}\) and integrate the resulting bound \(|\rho+1|(x-r)r^{-5/2}\). Multiplication of (29) for the two fixed points, followed by \(w_r^{-1}=r(r+1)\), yields
\[
\frac{m_\rho(r)\overline{m_\sigma(r)}}{w_r}
=r^{-1-i(t_\rho-t_\sigma)}+O_{\rho,\sigma}(r^{-2}).
\tag{30}
\]
The error is summable. Equations (28)–(30) show
\[
(H_L)_{\rho\sigma}
=\sum_{r=1}^Lr^{-1-i(t_\rho-t_\sigma)}+O_{\rho,\sigma}(1).
\tag{31}
\]
When \(\rho=\sigma\), the sum is \(\log L+O(1)\). When \(\rho\ne\sigma\), the real number \(\Delta=t_\rho-t_\sigma\) is nonzero. For \(f(x)=x^{-1-i\Delta}\), integral comparison gives
\[
\left|\sum_{r=1}^Lf(r)-\int_1^Lf(x)\,dx\right|
\le1+|1+i\Delta|,
\]
while
\[
\left|\int_1^Lx^{-1-i\Delta}\,dx\right|
=\left|\frac{L^{-i\Delta}-1}{-i\Delta}\right|
\le\frac2{|\Delta|}.
\]
Consequently
\[
\boxed{H_L=(\log L)I_k+E_L,
\qquad\sup_{L\ge2}\|E_L\|<\infty,}\tag{32}
\]
where the bound depends only on the fixed finite set \(Z\). In particular, \(H_L\) is positive definite for all sufficiently large \(L\), and
\[
(\log L)H_L^{-1}\longrightarrow I_k
\quad\text{in operator norm}.
\tag{33}
\]

Since \(L_N\ge N\), we have \(L_N\to\infty\). By (20)–(21),
\[
a_{L_N}\longrightarrow
\left(\frac{1-2^{-\rho}}\rho\right)_{\rho\in Z},
\qquad W_{L_N}(1)\longrightarrow\frac12.
\tag{34}
\]
Multiplying (26)–(27) by \(\log L_N\), discarding the nonnegative lift term in (27), and using (33)–(34) proves (3)–(4).

## 7. Joint-hole determinant bound

The same matrix certificate controls any fixed finite collection of sites. Let \(B=\{n_1,\ldots,n_b\}\subset\mathbb N_{\ge1}\). Define the positive semidefinite \(b\times b\) matrix
\[
\mathcal C_Z[B](n,m)
=\sum_{\rho\in Z}
\frac{\overline{m_\rho(n)}m_\rho(m)}{\sqrt{w_nw_m}},
\qquad n,m\in B.
\tag{35}
\]
The conjugations in (35) agree with the choice of the columns of \(C_L\).

For all sufficiently large \(N\), \(L_N>\max B\), so these sites represent distinct residue classes. Write
\[
J_L=\operatorname{diag}_{n\in B}
\sqrt{\frac{w_n}{W_L(n)}}.
\]
The exact physical-to-class relation on this block is
\[
Q_N[B]=J_L\overline Q_{N,L}[B]J_L.
\]
As \(0\preceq J_L^2\preceq I_B\), compression of (25) gives
\[
\begin{aligned}
I_B-Q_N[B]
&=I_B-J_L^2+J_L(I_B-\overline Q_{N,L}[B])J_L\\
&\succeq Y_LH_L^{-1}Y_L^*,
\end{aligned}
\tag{36}
\]
where \(Y_L=J_L C_L[B,:]\), that is,
\[
Y_L(n,\rho)=
\frac{\sqrt{w_n}\,\overline{A_{\rho,L}(n)}}{W_L(n)}.
\]
The right side is positive semidefinite. For fixed \(n\), (20)–(21) imply
\[
Y_L(n,\rho)\longrightarrow
\frac{\overline{m_\rho(n)}}{\sqrt{w_n}}.
\]
Together with (33), this proves the matrix convergence
\[
(\log L)Y_LH_L^{-1}Y_L^*\longrightarrow\mathcal C_Z[B].
\tag{37}
\]
Determinants are monotone on positive semidefinite matrices under Loewner order. Applying this to (36) and using (37),
\[
\liminf_{N\to\infty}(\log L_N)^b
\det(I_B-Q_N[B])\ge\det\mathcal C_Z[B].
\]
For a DPP the probability that all sites of \(B\) are absent is \(\det(I_B-Q_N[B])\). Thus
\[
\boxed{
\liminf_{N\to\infty}(\log L_N)^{|B|}
\mathbb P(B\cap\Xi_N=\varnothing)
\ge\det\mathcal C_Z[B].
}\tag{38}
\]
One can obtain the DPP hole formula directly from the inclusion-determinant formula by finite inclusion–exclusion and the principal-minor expansion of \(\det(I-Q_N[B])\). Bound (38) is nontrivial when \(\mathcal C_Z[B]\) is positive definite; we make no automatic nondegeneracy claim for arbitrary \(B\) and \(Z\).

## 8. Proof of infinite expected entrance time

One critical-line zero suffices. Since \(a_\rho>0\), choose \(L_0\) such that
\[
3L^{-3/2}\le a_\rho/2\qquad(L\ge L_0).
\]
For \(L\ge2\), \(1+4/L^2\le2\). Thus (2) gives, eventually along \(L=L_N\),
\[
p_N\ge\frac{a_\rho^2}{8(\log L_N+24)}.
\tag{39}
\]
The elementary conductor bound
\[
L_N\le N!\le N^N
\]
implies \(\log L_N\le N\log N\). For all sufficiently large \(N\), also \(24\le N\log N\), hence
\[
\boxed{p_N\ge\frac{a_\rho^2}{16N\log N}}.
\tag{40}
\]

The subspaces \(V_N\) increase, so \(Q_N(1,1)\) increases and \(p_N\) decreases. On a probability space carrying \(U\sim\operatorname{Uniform}[0,1]\), the indicators
\[
I_N=\mathbf1_{\{U\le Q_N(1,1)\}}
\]
are increasing and have exactly the required first-site marginals. Their entrance time satisfies \(\mathbb P(\tau_1>N)=p_N\). The same equality holds in every coupling with increasing first-site indicators, including every nested spatial coupling.

By the extended-valued tail-sum identity,
\[
\mathbb E[\tau_1]=\sum_{n\ge0}\mathbb P(\tau_1>n).
\]
The series \(\sum_{N\ge2}(N\log N)^{-1}\) diverges, as is seen by integrating \(1/(x\log x)\). Equation (40) therefore proves (5).

This conclusion is unconditional because a critical-line zero is known to exist. Where the repository's RH-to-first-site-saturation implication is available, RH would imply \(\tau_1<\infty\) almost surely, while (5) would still give an infinite expectation. An infinite expectation does not imply positive probability of infinite entrance time and creates no contradiction with RH.

## 9. Scope and references

The finite inequalities (16), (19), (26), and (27) are explicit certificates formed from absolutely convergent sums. They avoid inverse-Gram estimates for the residue features by using an independently constructed subspace of their orthogonal complement. The multizero asymptotic is a finite-dimensional Gram calculation. The DPP conclusion retains the distinction between a selected residue class and its selected physical lift.

These results are lower bounds. They do not prove \(D_N\to0\), \(p_N\to0\), or vanishing inverse-Gram corrections. The sharper \(\log N\) lower-bound scale in classical Nyman–Beurling theory is an external benchmark, not a theorem proved or used in this argument.

1. J.-F. Burnol, *A lower bound in an approximation problem involving the zeros of the Riemann zeta function*, Advances in Mathematics 170 (2002), 56–70, [arXiv:math/0103058](https://arxiv.org/abs/math/0103058). This supplies the classical stronger asymptotic Nyman–Beurling benchmark; the elementary finite-conductor proof above is independent of it.
2. J. B. Hough, M. Krishnapur, Y. Peres, and B. Virág, *Determinantal Processes and Independence*, Probability Surveys 3 (2006), 206–229, [arXiv:math/0503110](https://arxiv.org/abs/math/0503110). Standard background for projection DPPs, inclusion determinants, and counting laws.

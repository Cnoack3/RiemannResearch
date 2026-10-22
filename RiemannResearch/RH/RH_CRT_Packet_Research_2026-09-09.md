# Legal Pareto packets and exact Schur-complement energies

Research note — 9 September 2026

Formalization companion: [RHChatFormalization.md](RHChatFormalization.md). This preserves the original informal research argument; consult the companion for the Lean status of each claim.

**Status.** This note develops an explicit improvement to the legal correction packets, proves its optimality within a specified class of fixed seeds, and derives exact global energy and coordinate recursions. It also proves that substantial arithmetic cross terms are unavoidable. It does **not** establish a uniform global energy bound, prove the required approximation of 1, or prove the Riemann Hypothesis. The arguments below are ordinary mathematics, independently checked in parts; no Lean was used. Results derived here carry no claim of literature novelty.

## 1. The space, legal packets, and the target

Work over the real Hilbert space
\[
H=\left\{f:\mathbb N_{>0}\to\mathbb R:
\|f\|^2=\sum_{k\ge1}\frac{f(k)^2}{k(k+1)}<\infty\right\}.
\]
Set \(w_k=1/[k(k+1)]\), and extend every sequence by \(f(0)=0\) when applying a dilation. The constant target 1 refers to the positive coordinates; its anchored extension has value 0 at coordinate 0.

Define
\[
r_a(k)=k\bmod a,\qquad
(T_mf)(k)=m f(\lfloor k/m\rfloor).
\]
All positive integer dilation indices \(m\) are allowed. The only generator ratios used here are 2 and 3:
\[
g_{a,m}=T_mr_a=r_{am}-r_m,\qquad a\in\{2,3\}.
\]
Let
\[
S=\operatorname{span}_{\mathrm{finite}}\{g_{2,m},g_{3,m}:m\ge1\},
\qquad V=\overline S^{\,H}.
\]

Telescoping the weights gives the exact identities
\[
\|1\|^2=1,\quad
\|T_m f\|^2=m\|f\|^2,\quad
\langle1,T_mf\rangle=\langle1,f\rangle,\quad
\langle1,r_a\rangle=\log a.
\]
The last identity follows by summation by parts from
\(\Delta r_a(j)=1-a\,1_{a\mid j}\), and
\(H_M-H_{\lfloor M/a\rfloor}\to\log a\).

The target is to construct finite legal \(F_N\) with
\[
F_N(k)=1\quad(1\le k\le N),\qquad
\sup_N\|F_N\|^2<\infty.
\tag{1}
\]
This suffices for \(1\in V\). Indeed, boundedness and eventual agreement on every coordinate imply \(F_N\rightharpoonup1\): first test against finitely supported sequences, then use their density and the common norm bound. A closed linear subspace is weakly closed.

This argument does not assert that the particular sequence \(F_N\) converges strongly. The minimum-norm interpolants \(v_N\in V\), however, satisfy
\[
\|v_M\|^2=\|v_N\|^2+\|v_M-v_N\|^2,\qquad M\ge N,
\tag{2}
\]
because the affine head constraints are nested. Their bounded costs make them strongly Cauchy, with limit 1. Pythagoras supplies this implication; it does not supply the missing bound in (1).

[Bagchi’s Theorem 1](https://arxiv.org/pdf/math/0607733) identifies RH with 1 belonging to the closed span of all residue sequences \(r_a\) in this weighted space. Since every legal generator is \(r_{am}-r_m\), the bound (1) would imply RH. The argument here does not require a converse for the restricted two-ratio system.

## 2. Exact CRT weights and the full Schur complement

For a finite collection of legal columns \(a_1,\ldots,a_d\), choose a common period \(Q>N\). Write \(A_{rj}=a_j(r)\), using representatives \(1,\ldots,Q\). Define
\[
W_Q(r)=\sum_{\ell\ge0}w_{r+\ell Q},\qquad
\tau_{Q,N}(r)=W_Q(r)-1_{r\le N}w_r.
\]
Each \(\tau_{Q,N}(r)\) is strictly positive. If \(Ac\) equals 1 on the head,
\[
\|Ac\|^2=\frac N{N+1}+c^\top Kc,\qquad
K=A^\top\operatorname{diag}(\tau_{Q,N})A.
\tag{3}
\]
This is an equality with the complete infinite tail included.

Let \(c_0\) be feasible and let the columns of \(Z\) form a basis for the kernel of the head constraint matrix. After removing redundant function columns, put
\[
G=Z^\top KZ,\qquad q=Z^\top Kc_0.
\]
When there are free directions, \(G\) is positive definite, and
\[
\begin{aligned}
(c_0+Zb)^\top K(c_0+Zb)
={}&c_0^\top Kc_0-q^\top G^{-1}q\\
&+(b+G^{-1}q)^\top G(b+G^{-1}q).
\end{aligned}
\tag{4}
\]
With no free directions, omit the last two terms involving \(G\). Thus the exact optimized tail cost is
\[
\mathcal E_N=c_0^\top Kc_0-q^\top G^{-1}q.
\tag{5}
\]
The intended arithmetic theorem remains \(\sup_N\mathcal E_N<\infty\) for a specified sequence of legal column spaces.

Uniform CRT averages do not replace these weights. The exact decomposition
\[
W_Q(r)=\frac1Q+\varepsilon_Q(r),\qquad
\sum_{r=1}^Q\varepsilon_Q(r)=0
\]
gives
\[
\langle a_i,a_j\rangle
=\frac1Q\sum_{r=1}^Q a_i(r)a_j(r)
+\sum_{r=1}^Q\varepsilon_Q(r)a_i(r)a_j(r).
\tag{6}
\]
The second term is the weighted CRT defect, including every cross term. It is not automatically small: \(W_Q(1)\ge1/2\), while \(1/Q\to0\). All subsequent packet substitutions are exact changes of legal columns in this full quadratic form.

## 3. An exact nearby-dilation identity

For fixed bounded periodic seeds \(\phi,\psi\), anchored at 0, set
\[
E_{\phi,n}=T_{n+1}\phi-T_n\phi,\qquad
\Delta\phi(j)=\phi(j)-\phi(j-1),\qquad L=n(n+1).
\]
Then
\[
\begin{aligned}
\langle E_{\phi,n},E_{\psi,n}\rangle
={}&\sum_{j=1}^{n}
\frac{[-n\Delta\phi(j)+\phi(j-1)]
      [-n\Delta\psi(j)+\psi(j-1)]}{jn(n+1)}\\
&+\sum_{j=1}^{n-1}\phi(j)\psi(j)
\left(\frac1{j(n+1)}-\frac1{(j+1)n}\right)
+R_n(\phi,\psi),
\end{aligned}
\tag{7}
\]
where the entire remaining tail is
\[
R_n(\phi,\psi)
=\sum_{k\ge L}w_kE_{\phi,n}(k)E_{\psi,n}(k).
\tag{8}
\]
In particular, this remainder is not silently discarded.

**Proof.** On \(jn\le k<j(n+1)\), for \(1\le j\le n\), the two floor quotients are \(j\) and \(j-1\). The packet value is
\(-n\Delta\phi(j)+\phi(j-1)\), and the interval has weight \(1/[jn(n+1)]\). On \(j(n+1)\le k<(j+1)n\), for \(1\le j<n\), both quotients are \(j\), the packet value is \(\phi(j)\), and the interval weight is the difference in (7). The packet is zero below \(n\). These intervals cover the coordinates below \(L\). The remaining coordinates give (8).

The retained tail admits the bound
\[
|R_n(\phi,\psi)|
\le\frac{(2n+1)^2}{n(n+1)}
\|\phi\|_\infty\|\psi\|_\infty
\le\frac92\|\phi\|_\infty\|\psi\|_\infty.
\tag{9}
\]
The middle sum in (7) is bounded in absolute value by
\(\|\phi\|_\infty\|\psi\|_\infty/n\). Expanding the first sum identifies its harmonic main term. Consequently,
\[
\lim_{n\to\infty}
\frac{\langle E_{\phi,n},E_{\psi,n}\rangle}{\log n}
=\operatorname{mean}_{\mathrm{period}}
   (\Delta\phi\,\Delta\psi).
\tag{10}
\]
For fixed seeds the difference from the mean times \(\log n\) is bounded. The bound need not be uniform over seeds that themselves depend on \(n\).

For residue seeds,
\[
J_a(j):=\Delta r_a(j)=1-a\,1_{a\mid j},
\]
and an exact average over a common period gives
\[
\operatorname{mean}(J_aJ_b)=\gcd(a,b)-1.
\tag{11}
\]
Thus local energy is governed by a concrete gcd Gram matrix. This conclusion was obtained from the full Pareto identity, rather than by assuming uniform CRT weights for the original norm.

## 4. An improved legal seed, with a sharp local coefficient

Consider
\[
\boxed{\phi=\frac34r_2+\frac12r_3-\frac14r_6},
\qquad
\theta=r_2-\phi.
\tag{12}
\]
This is legal because \(r_6=r_2+T_2r_3\). The values of \(\phi\) on the six residue classes are
\[
\begin{array}{c|rrrrrr}
k\bmod6&0&1&2&3&4&5\\ \hline
\phi(k)&0&1&1/2&0&-1/2&1/2\\
\theta(k)&0&0&-1/2&1&1/2&1/2
\end{array}
\]
Its jumps have the simple form
\[
\Delta\phi(j)=
\begin{cases}
1,&(j,6)=1,\\
-1/2,&(j,6)>1.
\end{cases}
\tag{13}
\]

For \((r_2,r_3,r_6)\), the matrix in (11) is
\[
G_{\mathrm{jump}}=
\begin{pmatrix}
1&0&1\\
0&2&2\\
1&2&5
\end{pmatrix}.
\]
For \(c=(3/4,1/2,-1/4)^\top\),
\[
G_{\mathrm{jump}}c=\tfrac12(1,1,1)^\top,\qquad
c^\top G_{\mathrm{jump}}c=\tfrac12.
\]
Also \(\operatorname{mean}(\Delta\phi\,\Delta\theta)=0\) and
\(\operatorname{mean}((\Delta\theta)^2)=1/2\). Therefore
\[
\lim_{n\to\infty}
\frac{\operatorname{Gram}(E_{\phi,n},E_{\theta,n})}{\log n}
=\frac12 I_2.
\tag{14}
\]
The best fixed mixture of only \(E_{r_2,n}\) and \(E_{r_3,n}\), with coefficient sum 1, has coefficient \(2/3\): minimize \(a^2+2b^2\) subject to \(a+b=1\). Formula (12) lowers that coefficient to \(1/2\).

The coefficient \(1/2\) is optimal among **all fixed finite residue seeds**
\[
\psi=\sum_{\substack{a=2^i3^j\\a>1}} c_a r_a,\qquad \psi(1)=1.
\tag{15}
\]
Such seeds are legal by telescoping along ratios 2 and 3. Their jumps equal 1 on the classes coprime to 6, which have density \(1/3\), and the jumps have period mean 0. Completing the square on the other classes gives the exact identity
\[
\operatorname{mean}((\Delta\psi)^2)
=\frac12+
\operatorname{mean}\!\left[
1_{(j,6)>1}\bigl(\Delta\psi(j)+\tfrac12\bigr)^2
\right].
\tag{16}
\]
The seed \(\phi\) realizes equality. This is a local optimality result for fixed smooth-index seeds, not an optimality theorem for arbitrary \(N\)-dependent global packet systems.

The harmonic main term for \(\phi\) is itself explicit:
\[
\sum_{j\le n}\frac{(\Delta\phi(j))^2}{j}
=H_n-\frac38H_{\lfloor n/2\rfloor}
-\frac14H_{\lfloor n/3\rfloor}
+\frac18H_{\lfloor n/6\rfloor}.
\tag{17}
\]
Equations (7), (8), and (17) together retain the full finite terms and tail.

The improved packet uses two scales of the original generators:
\[
\begin{aligned}
E_{r_6,n}&=E_{r_2,n}+E_{r_3,2n}+E_{r_3,2n+1},\\
E_{\phi,n}
&=\tfrac12 E_{r_2,n}+\tfrac12 E_{r_3,n}
-\tfrac14 E_{r_3,2n}-\tfrac14 E_{r_3,2n+1}.
\end{aligned}
\tag{18}
\]
Thus this improvement is an explicit admissible packet construction.

## 5. Retaining both channels

Using \(\phi\) does not require losing the original two-channel closure. In fact,
\[
2\phi-r_2=(I-\tfrac12T_2)r_3,\qquad
\|\tfrac12T_2\|=1/\sqrt2.
\]
For every positive integer \(J\),
\[
r_3=
\sum_{j=0}^{J-1}2^{-j}T_{2^j}(2\phi-r_2)
+2^{-J}T_{2^J}r_3,
\tag{19}
\]
with exact residual norm
\[
\|2^{-J}T_{2^J}r_3\|^2=2^{-J}\|r_3\|^2.
\tag{20}
\]
The residual is also zero on \(k<2^J\). It follows that the closed all-integer dilation spans of \(\{r_2,r_3\}\), \(\{r_2,\phi\}\), and \(\{\phi,\theta\}\) agree. This does not assert equality of their finite algebraic spans.

Keeping a second independent channel matters. A single fixed finite legal seed has an unconditional Mellin obstruction, proved in Section 9 below.

## 6. A concrete mean-preserving Schur recursion

All nearby differences have weighted mean zero. Starting solely from these differences would force every interpolant to have mean zero, an immediate obstruction: if \(F=1\) through \(N\) and \(\langle1,F\rangle=0\), then tail Cauchy–Schwarz gives
\[
\|F\|^2\ge \frac N{N+1}+\frac{N^2}{N+1}=N.
\tag{21}
\]
Use the finite legal baseline
\[
F_0=r_2/\log2,\qquad
\langle1,F_0\rangle=1,\qquad \|F_0\|^2=1/\log2.
\]

Set
\[
u_n=-E_{\phi,n}/n,\qquad d_n=-E_{\theta,n}/n.
\tag{22}
\]
These have mean zero. Moreover,
\[
u_n(k)=0\ (k<n),\quad u_n(n)=1,\quad
d_n(k)=0\ (k\le n),\quad d_n(2n)=-1/2.
\tag{23}
\]
The last identity ensures that the free direction never vanishes.

Suppose \(F_{n-1}\) has mean 1 and equals 1 through \(n-1\). Define
\[
\begin{aligned}
\delta_n&=1-F_{n-1}(n),\\
Z_n&=F_{n-1}+\delta_nu_n,\\
t_n&=-\frac{\langle Z_n,d_n\rangle}{\|d_n\|^2},\\
F_n&=Z_n+t_nd_n.
\end{aligned}
\tag{24}
\]
Every \(F_n\) is finite legal, has mean 1, and equals 1 through \(n\). The choice of \(t_n\) minimizes the **full** energy along this free direction. The exact energy update is
\[
\boxed{
\begin{aligned}
\|F_n\|^2={}&\|F_{n-1}\|^2
+2\delta_n\langle F_{n-1},u_n\rangle
+\delta_n^2\|u_n\|^2\\
&-\frac{\bigl(\langle F_{n-1},d_n\rangle
+\delta_n\langle u_n,d_n\rangle\bigr)^2}{\|d_n\|^2}.
\end{aligned}}
\tag{25}
\]
No independence assumption was made. The old-packet/new-packet terms and the within-packet cross term all remain.

The local correction costs satisfy
\[
\lim_{n\to\infty}
\frac{n^2}{\log n}\operatorname{Gram}(u_n,d_n)=\frac12 I_2.
\tag{26}
\]
This does not control \(\delta_n\), the old-packet correlations in (25), or the cumulative effect on later coordinates. Boundedness of this particular greedy recursion is unproved; it is a candidate to analyze, not a claimed solution.

## 7. Exact martingale coordinates and the remaining stability problem

There is a precise probabilistic coordinate system, stronger than an informal Brownian analogy. Define
\[
h_n(k)=
\begin{cases}
0,&k<n,\\
n,&k=n,\\
-1,&k>n.
\end{cases}
\tag{27}
\]
The functions \(h_n\) form an orthonormal basis of \(1^\perp\).

For example, with \(\Pr(K=k)=w_k\), let \(Y_n(K)\) equal 1 on \(K\le n\) and \(-n\) on \(K>n\), with \(Y_0=0\). For the filtration revealing the singletons \(K=1,\ldots,n\) and the remaining tail, \(Y_n\) is a martingale and \(h_n=Y_n-Y_{n-1}\). It is not a Wiener process: these increments are not independent Gaussian variables.

Directly, each \(h_n\) has mean 0 and norm 1. If \(i<n\), \(h_i=-1\) on the support of \(h_n\), giving orthogonality. For any mean-zero \(f\),
\[
\langle f,h_j\rangle
=\sum_{k<j}w_kf(k)+\frac{f(j)}j.
\tag{28}
\]
If all these coefficients vanish, induction gives \(f(j)=0\) for every \(j\); this proves completeness.

Expand the normalized repair:
\[
n u_n=h_n+\sum_{j>n}\beta_{jn}h_j,
\quad
\beta_{jn}
=n\left(\sum_{k=n}^{j-1}w_ku_n(k)+\frac{u_n(j)}j\right).
\tag{29}
\]
Every displayed coefficient is a finite rational expression for these rational-valued seeds. Define
\[
\beta_n=(\beta_{jn})_{j>n},\qquad
\gamma_n=(\langle d_n,h_j\rangle)_{j>n}.
\]
The vector \(\gamma_n\) is nonzero.

For a mean-one \(F_{n-1}\) with the required head, let
\[
x_j=\langle F_{n-1}-1,h_j\rangle.
\]
Then \(x_j=0\) for \(j<n\), \(\delta_n=-n x_n\), and (24) becomes exactly
\[
\boxed{
x_{\mathrm{new}}
=P_{\gamma_n^\perp}\bigl(x_{j>n}-x_n\beta_n\bigr).
}
\tag{30}
\]
Furthermore,
\[
\|F_n\|^2=1+\|x^{(n)}\|_{\ell^2}^2.
\tag{31}
\]
The initial vector is explicit:
\[
x_j^{(0)}
=\frac1{\log2}\left(
\sum_{k<j}w_k r_2(k)+\frac{r_2(j)}j
\right)-1.
\tag{32}
\]

Thus a concrete remaining theorem would bound the orbit of this initial vector under the explicitly specified causal maps in (30):
\[
\sup_N\|x^{(N)}\|_{\ell^2}<\infty.
\tag{33}
\]
This is a target-specific assertion. Requiring bounded products on every possible initial vector would be a stronger, presently unjustified replacement.

There is a useful warning against a naive contraction proof. For
\[
\mathcal A_n(a,y)=P_{\gamma_n^\perp}(y-a\beta_n),
\]
the exact operator norm is
\[
\begin{aligned}
\|\mathcal A_n\|^2
&=1+\|P_{\gamma_n^\perp}\beta_n\|^2\\
&=n^2\left(\|u_n\|^2
-\frac{|\langle u_n,d_n\rangle|^2}{\|d_n\|^2}\right).
\end{aligned}
\tag{34}
\]
Using (7) and the jump covariance in (14),
\[
\lim_{n\to\infty}\frac{\|\mathcal A_n\|^2}{\log n}=\frac12.
\tag{35}
\]
Individual maps therefore are not uniformly contractive. The possible saving must come from the actual orbit's arithmetic correlations, or from optimizing over larger collections of free directions. The orthonormal martingale coordinates identify the issue; they do not remove it.

## 8. Mixed arithmetic components cancel a linear amount of energy

The following calculation applies to every finite legal packet, independently of the proposed greedy recursion.

Represent a legal packet by its finite charge sequence:
\[
F=-\sum_{n\ge1}d_n r_n.
\tag{36}
\]
An edge \(g_{a,m}\) contributes the charge \(\delta_m-\delta_{am}\). Include \(n=1\), even though \(r_1=0\). For each rough core \(q\), with \((q,6)=1\), the component
\[
C_q=\{q2^i3^j:i,j\ge0\}
\]
has total charge zero. Therefore
\[
F(k)=\sum_{n\ge1}nd_n\lfloor k/n\rfloor,\qquad
F(k)-F(k-1)=\sum_{n\mid k}nd_n.
\tag{37}
\]
Möbius inversion makes the charge sequence unique, including \(d_1=F(1)\). If \(F=1\) through \(N\), it forces
\[
d_n=\frac{\mu(n)}n,\qquad 1\le n\le N.
\tag{38}
\]

Let \(F_q=-\sum_{n\in C_q}d_nr_n\). Component charge balance and (38) give the exact head formula
\[
F_q(k)=\mu(q)C(k/q)\quad(k\le N),
\tag{39}
\]
where
\[
C(x)=\lfloor x\rfloor-\lfloor x/2\rfloor
-\lfloor x/3\rfloor+\lfloor x/6\rfloor.
\]
The function \(C(x)\) counts positive integers at most \(x\) coprime to 6.

Define the sum of component diagonal head energies by
\[
D_N=\sum_{\substack{q\ge1\\(q,6)=1}}
\sum_{k\le N}w_k F_q(k)^2.
\]
Then
\[
\boxed{\lim_{N\to\infty}\frac{D_N}{N}=\frac6{5\pi^2}.}
\tag{40}
\]
Indeed \(C(x)=x/3+O(1)\). For each fixed \(q\), the inner average divided by \(N\) tends to \(\mu(q)^2/(9q^2)\). Since \(C(k/q)\le k/q\), these averages are bounded by \(1/q^2\), allowing dominated convergence over \(q\). Finally,
\[
\sum_{(q,6)=1}\frac{\mu(q)^2}{q^2}
=\frac{\zeta(2)/\zeta(4)}
{(1+1/4)(1+1/9)}
=\frac{54}{5\pi^2}.
\]

On the other hand, the total head energy is exactly \(N/(N+1)\). Hence
\[
\boxed{
2\sum_{q<q'}\langle F_q,F_{q'}\rangle_{\le N}
=\frac N{N+1}-D_N,
}
\tag{41}
\]
and the mixed sum divided by \(N\) tends to \(-6/(5\pi^2)\).

This establishes that linear-sized mixed cancellation is mandatory even on the already-correct head. Estimating each rough component by a positive cost and then summing loses exactly the phenomenon the argument needs. Arbitrary integer dilation indices are allowed throughout; adding new generator ratios beyond 2 and 3 would change this particular component decomposition.

## 9. Two restrictions on overly rigid constructions

### 9.1 Fixed prefix coefficients in the original generators

Suppose
\[
P_N=\sum_{m\le N}(u_mg_{2,m}+v_mg_{3,m})
\]
uses fixed coefficient streams and equals 1 through \(N\) for every \(N\). Charge inversion gives
\[
u_n+v_n-1_{2\mid n}u_{n/2}-1_{3\mid n}v_{n/3}
=\frac{\mu(n)}n.
\tag{42}
\]
Sum this over \(n=2^i3^j\) with \(i+j\le r\), where \(r\ge2\). Internal edges cancel; the right side equals
\(1-1/2-1/3+1/6=1/3\). Thus
\[
\sum_{i+j=r}(u_{2^i3^j}+v_{2^i3^j})=\frac13.
\]
For some \(n=2^i3^j\) on this boundary,
\[
|u_n+v_n|\ge\frac1{3(r+1)},\qquad n\ge2^r.
\]
On \(n\le k<2n\), the increment \(P_n-P_{n-1}\) equals \(n(u_n+v_n)\). Therefore
\[
\|P_n-P_{n-1}\|^2\ge\frac{2^r}{18(r+1)^2},
\qquad
\max(\|P_n\|^2,\|P_{n-1}\|^2)
\ge\frac{2^r}{72(r+1)^2}.
\tag{43}
\]
Such fixed-prefix truncations cannot stay bounded, even with both channels.

This result does not rule out all fixed coefficient expansions in nearby differences after a mean-one baseline. That is a different construction and must not be excluded by overextending (43).

There is a relevant literature precedent: [Báez-Duarte, “A divergent Vasyunin correction”](https://arxiv.org/pdf/math/0506318) analyzes a binary correction system built from \(\lfloor x/n\rfloor-2\lfloor x/(2n)\rfloor\), and proves failure of its \(L^1\) convergence. The broader two-channel calculation (42)–(43) is derived above, not attributed to that paper.

### 9.2 One fixed finite legal seed cannot be cyclic for the target

For \(\Re s>1/2\), define the continuous functional
\[
\mathcal L_s(f)=\int_1^\infty
f(\lfloor x\rfloor)x^{-s-1}\,dx.
\]
The step embedding is an isometry into \(L^2((1,\infty),dx/x^2)\), and
\[
|\mathcal L_s(f)|\le\frac{\|f\|}{\sqrt{2\Re s-1}},
\qquad \mathcal L_s(1)=1/s.
\tag{44}
\]
For legal generators, first integrate for \(\Re s>1\), then continue within the domain of these functionals:
\[
\mathcal L_s(g_{a,m})
=m^{1-s}(1-a^{1-s})\frac{\zeta(s)}s.
\tag{45}
\]
The apparent singularity at \(s=1\) is removable for each generator.

Every nonzero fixed finite legal seed \(\psi\) consequently has
\[
\mathcal L_s(\psi)=\frac{\zeta(s)}sQ(s),
\tag{46}
\]
where \(Q\) is a nonzero finite exponential polynomial and \(Q(1)=0\). Simultaneous recurrence of its finitely many phases supplies arbitrarily large \(T\) with \(Q(s+iT)\) arbitrarily close to \(Q(s)\), uniformly on any fixed compact set. Choose a small disk around 1 whose boundary contains no zero of \(Q\). Rouché's theorem then gives zeros of \(Q\) in vertically translated disks, with real part greater than \(1/2\) and nonzero imaginary part.

At any such zero \(s_0\), the zeta factor has no pole, so
\(\mathcal L_{s_0}(\psi)=0\). Since
\[
\mathcal L_s(T_m\psi)=m^{1-s}\mathcal L_s(\psi),
\]
the continuous functional \(\mathcal L_{s_0}\) annihilates every integer dilate of \(\psi\), while \(\mathcal L_{s_0}(1)=1/s_0\ne0\). Thus 1 is not in that single-seed closed dilation span.

There is an explicit interpolation lower bound as well. If \(\sigma=\Re s_0>1/2\), \(\mathcal L_{s_0}(F)=0\), and \(F=1\) through \(N\), splitting the integral at \(N+1\) and applying tail Cauchy–Schwarz yields
\[
\|F\|^2\ge
\frac N{N+1}
+\frac{(2\sigma-1)(N+1)^{2\sigma-1}}{|s_0|^2}
\left|1-(N+1)^{-s_0}\right|^2.
\tag{47}
\]
This diverges. The obstruction applies to a single fixed finite seed, not to an \(N\)-dependent seed family or to the retained two-channel system.

For Mellin and fractional-part autocorrelation background, see [Báez-Duarte, Balazard, Landreau and Saias, “Sur l’autocorrélation multiplicative de la fonction ‘partie fractionnaire’”](https://arxiv.org/pdf/math/0306251). The particular discrete packet identities in this note are proved directly above.

## 10. Limited exploratory calculation and the next arithmetic question

A small floating-point experiment evaluated the recursion (24), approximating every inner product by the sum over \(k\le1{,}200{,}000\). The reported quantities are the resulting partial squared norms, not certified full norms and not the exact infinite-inner-product recursion:

| Corrected head \(N\) | Partial squared norm |
|---:|---:|
| 1 | 1.18995 |
| 8 | 1.19673 |
| 16 | 1.23712 |
| 32 | 1.28158 |
| 64 | 1.34948 |
| 128 | 1.48957 |

At \(N=128\), changing the cutoff from 300,000 to 1,200,000 changed the reported value by about 0.00065. This is only a cutoff sensitivity check; it certifies neither the remaining infinite tail nor long-term behavior. The later upward trend provides no affirmative evidence of a uniform bound and proves no divergence.

The proved local improvement justifies using the pair \((\phi,\theta)\) as explicit columns in the full CRT optimization, with several scales and additional head-preserving directions optimized together. The single-direction greedy recursion is a clean mathematical candidate but has no established stability theorem.

Two precise research targets now stand out:

1. For the specified greedy construction, prove or disprove the target-specific orbit bound (33), retaining the exact transfer coefficients (29). The growth of the individual operator norms in (35) means that independent local norm bounds will not suffice.
2. For an explicitly chosen larger collection of legal directions, prove a uniform bound for the complete Schur complement (5). The packet identity (18) provides an admissible improved starting basis; (6) and (41) specify cancellations that an estimate must preserve.

Neither target is claimed to be easier than the original approximation problem. The advance is concrete: an optimal fixed-seed local correction, an exact two-channel substitution, a mean-preserving energy recursion, and a quantified reason that componentwise positive estimates fail. The remaining theorem is a global arithmetic stability or cancellation estimate, not another application of Pythagoras.

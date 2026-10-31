# Signed squarefree short-head responses: divisor coercivity, Schur compression, and averaged RH criteria

Date: 30 October 2026. Source: the user's request to continue
`SquarefreePrefixResponseResearch20261030.md` and test every proposed estimate
against `SquarefreePrefixResponseDiagnostics20261030.md`.

**Status.** The intermediate results below have self-contained paper proofs.
They have not been Lean-verified. Numerical checks are exploratory float64,
using complete-period formulas for the full Q moments. The uniform signed
short-head estimate remains **Open**. No proof of RH is claimed.

The main unconditional arithmetic estimate is a logarithmic-squared bound for
a suitably normalized inverse Gram matrix. Eliminating the directions that
vanish on the physical head improves its logarithmic parameter from the stage
size to the head size, uniformly over all later stages. This does not bound the
remaining evaluation/source pairing. A second result gives an exact signed
response identity retaining the projection-loss square. Finally, a spatial
mean-square, limiting-stage condition suffices for the existing RH consumer;
a uniform pointwise estimate at every finite stage is stronger than necessary.

## 1. Complete objects and conventions

Put Z = zeta(2), Q(m)=1/(Z m^2), and work in the real Hilbert space l2(Q).
Every sum without a finite range is over all positive physical sites. Set

\[
D_N=\{2\le d\le N+1:d\text{ is squarefree}\},\quad
g_d(m)=\frac{m\bmod d}{d},\quad V_N=\operatorname{span}\{g_d:d\in D_N\}.
\]

Write P_N for orthogonal projection onto V_N, F_N=P_N1,
r_N=1-F_N, epsilon_N=||r_N||_Q^2, and b_N=P_N B r_N, where
(Bf)(m)=f(m)/(m+1). These are the canonical unconstrained projections, not the
exact-head optimizers from the mixed-trial program. All composite squarefree
conductors are retained.

Let e_n(m)=1_{m=n}/Q(n), k_{N,n}=P_N e_n, and
K_N(n,m)=k_{N,n}(m). Thus ||k_{N,n}||_Q^2=K_N(n,n)<=Z n^2.
For 0<=H<n define the nonnegative, finite-support multiplier

\[
w_{H,n}(m)=\mathbf1_{m\le H}
\left(\frac1{m+1}-\frac1{n+1}\right),\qquad
S_{N,H}(n)=\langle w_{H,n}r_N,k_{N,n}\rangle_Q.
\tag{1}
\]

This S is the centered short-head response denoted T_corr in the source memo.
The case H=0 is identically zero. Orthogonality and complete-tail
Cauchy--Schwarz give the existing exact decomposition and estimate

\[
b_N(n)=S_{N,H}(n)+
\sum_{m>H}Q(m)r_N(m)K_N(n,m)
\left(\frac1{m+1}-\frac1{n+1}\right),
\tag{2}
\]
\[
|b_N(n)-S_{N,H}(n)|
\le\frac{\sqrt{K_N(n,n)}}{H+2}
\|\mathbf1_{m>H}r_N\|_Q
\le\sqrt Z\,\frac n{H+2}.
\tag{3}
\]

Here epsilon_N<=1. The centered tail is absolutely convergent. In particular,
ell(n)=6+log n and H(n)=floor(n/ell(n)) give an error at most sqrt(Z) ell(n).

For vectors v(m)=(g_d(m))_{d in D_N}, let

\[
G=\sum_{m\ge1}Q(m)v(m)v(m)^T,\quad
\mu=\sum_{m\ge1}Q(m)v(m),\quad
\alpha=G^{-1}\mu.
\]

The raw full Gram is positive definite. With
z_w=sum_{m<=H} Q(m)w(m)r_N(m)v(m), the exact response is

\[
S_{N,H}(n)=v(n)^TG^{-1}z_w.
\tag{4}
\]

No finite physical truncation is used to define G, mu, alpha, or the kernel.

## 2. A divisor-coercivity estimate for the full dictionary

For H>=1 put

\[
L_H=\sum_{k\le H}\frac{|\mu_{\mathrm{Mob}}(k)|}{k}
\le1+\log H.
\]

The Mobius function here is distinct from the moment vector mu above.

**Proposition 1 (finite divisor estimate).** Suppose a sequence on 0,...,H
has f(0)=0 and

\[
f(m)=s m-\sum_{2\le d\le H}c_d\lfloor m/d\rfloor,
\quad 1\le m\le H.
\]

Zeros may be prescribed at any subset of coefficient indices. Then

\[
\boxed{
|s|^2+\sum_{2\le d\le H}\frac{|c_d|^2}{d^2}
\le4Z L_H^2\sum_{m\le H}Q(m)|f(m)|^2.}
\tag{5}
\]

**Proof.** Write Delta f(k)=f(k)-f(k-1). Before taking any estimates, the exact
signed divisor relations are

\[
\Delta f(k)=s-\sum_{\substack{d\mid k\\d\ge2}}c_d,
\quad f(1)=s,
\quad c_d=-\sum_{k\mid d}\mu_{\mathrm{Mob}}(d/k)\Delta f(k)
\quad(d\ge2).
\tag{6}
\]

The last formula is finite Mobius inversion; the constant s disappears because
sum_{k|d} mu_Mob(d/k)=0 for d>1. Set c'_1=-s and c'_d=c_d for d>=2, and set
h(k)=Delta f(k)/k. Equation (6), including d=1, becomes

\[
\frac{c'_d}{d}=-\sum_{a\mid d}\frac{\mu_{\mathrm{Mob}}(a)}a h(d/a).
\tag{7}
\]

For each a, the map h -> 1_{a|d} h(d/a), restricted to d<=H, is an l2
contraction. The triangle inequality for this finite sum gives

\[
\left(\sum_{d\le H}\frac{|c'_d|^2}{d^2}\right)^{1/2}
\le L_H\left(\sum_{k\le H}\frac{|\Delta f(k)|^2}{k^2}\right)^{1/2}.
\]

For u_k=f(k)/k and u_0=0, h(k)=u_k-((k-1)/k)u_{k-1}. The weighted shift is
an l2 contraction on 1,...,H. Hence ||h||_2<=2||u||_2, and (5) follows from
||u||_2^2=Z||1_{m<=H}f||_Q^2. This estimate takes absolute values only at the
finite convolution-norm step; it makes no assertion of Mobius cancellation.

**Corollary 1 (full weighted inverse Gram).** Put M=N+1 and
D=diag(d)_{d in D_N}. For the nonempty dictionary,

\[
\boxed{
(DGD)^{-1}\preceq4Z L_M^2 I,
\qquad G^{-1}\preceq4Z L_M^2D^2.}
\tag{8}
\]

Indeed f=sum_d c_d g_d has s=f(1)=sum_d c_d/d and the form in Proposition 1
on the first M sites. Discard |s|^2 in (5) and retain the full nonnegative tail
of ||f||_Q^2. Substituting c_d=d a_d proves
a^T DGD a >= ||a||_2^2/(4Z L_M^2), and matrix inversion proves (8).
This is a bound in specified weighted coordinates, not a bound on the
unscaled norm of G^{-1}. It holds for the complete squarefree dictionary,
and the same proof works for any finite conductor subdictionary.

## 3. Exact head compression: the logarithm depends on H, not N

Fix H>=1 and choose d0 in D_N with d0>H. Such a conductor exists in the
intended moving-head range: 2H<=n<=N, and a prime in (H,2H] is available
(for H=1 use 2). Let I_H={d in D_N:d<=H}. Introduce legal functions

\[
\rho_0=d_0g_{d_0},\qquad
\rho_d=d g_d-d_0g_{d_0}\quad(d\in I_H),
\]
\[
\tau_e=g_e-\frac{d_0}{e}g_{d_0}
\quad(e\in D_N,\ e>H,\ e\ne d_0).
\tag{9}
\]

On 1<=m<=H, rho_0(m)=m, rho_d(m)=-d floor(m/d), and every tau_e(m)=0.
The collection (rho,tau) is an invertible change of the entire original
basis, including all large conductors. The rho restrictions are independent:
their coefficients are recovered by (6). Consequently

\[
W_{N,H}:=\operatorname{span}\{\tau_e\}
=\{f\in V_N:f(m)=0\ (1\le m\le H)\}.
\tag{10}
\]

Let R_W be orthogonal projection onto W_{N,H}, and put
psi_j=(I-R_W)rho_j. In the (rho,tau) basis write the complete Gram as

\[
\begin{pmatrix}A&C\\C^T&E\end{pmatrix},\qquad
\mathcal S_{N,H}=A-CE^{-1}C^T
=\big(\langle\psi_i,\psi_j\rangle_Q\big)_{ij}.
\tag{11}
\]

If W is zero-dimensional the CE^{-1}C^T term is zero. The head matrix is

\[
T_H=\sum_{m\le H}Q(m)\rho(m)\rho(m)^T.
\]

**Proposition 2 (uniform compressed inverse bound).** In precisely the
coordinates (9),

\[
\boxed{
\mathcal S_{N,H}\succeq T_H\succeq(4Z L_H^2)^{-1}I,
\qquad
\mathcal S_{N,H}^{-1}\preceq T_H^{-1}\preceq4Z L_H^2 I.}
\tag{12}
\]

**Proof.** The exact identity preceding the inequalities is

\[
\mathcal S_{N,H}=T_H+
\sum_{m>H}Q(m)\psi(m)\psi(m)^T.
\tag{13}
\]

This holds because psi=rho on the head. For a=(a_0,(a_d)),
a^T rho(m)=a_0 m-sum_d (d a_d)floor(m/d). Proposition 1 bounds ||a||_2^2
by 4Z L_H^2 a^T T_H a. Positive definiteness and order reversal under matrix
inversion finish the proof. All inequalities are uniform in N once the full
low dictionary and an anchor above H are present.

For a fixed H and fixed anchor, W_{N,H} grows with N. Thus
S_{N,H} decreases in Loewner order and its inverse increases, bounded above
by T_H^{-1}. This follows from the exact minimum-extension formula
a^T S_{N,H}a=inf_{t in W_{N,H}}||sum_j a_j rho_j-t||_Q^2.
It supplies fixed-head convergence without an RH assumption.

To retain the actual optimizer, define full moments

\[
\eta_j=\langle1,\psi_j\rangle_Q,
\quad a=\mathcal S_{N,H}^{-1}\eta,
\quad y(n)=\psi(n),
\quad q=\sum_{m\le H}Q(m)w(m)r_N(m)\rho(m).
\]

Orthogonal splitting V_N=W_{N,H} direct-sum span{psi_j} gives

\[
F_N=R_W1+\sum_j a_j\psi_j,
\quad r_N(m)=1-\rho(m)^Ta\quad(m\le H),
\]
\[
K_N(n,m)=y(n)^T\mathcal S_{N,H}^{-1}\rho(m)\quad(m\le H),
\]
\[
\boxed{S_{N,H}(n)=y(n)^T\mathcal S_{N,H}^{-1}q.}
\tag{14}
\]

In particular q=mu_{w,rho}-T_{w,rho} S^{-1} eta is an actual partial
normal-equation error. Its divisor entries, with
R_w(t,H)=sum_{m=t}^H Q(m)w(m)r_N(m), are exactly

\[
q_0=\sum_{m\le H}mQ(m)w(m)r_N(m),\qquad
q_d=-d\sum_{j\le H/d}R_w(jd,H).
\tag{15}
\]

The full normal equations say <r_N,psi_j>_Q=0, not q_j=0. Neither the
large-conductor part of eta nor the complete tail in (13) may be deleted.

The proved estimate (12) gives

\[
|S_{N,H}(n)|\le4ZL_H^2\,\|y(n)\|_2\|q\|_2,
\quad
|S_{N,H}(n)|^2\le
(y(n)^T\mathcal S^{-1}y(n))(q^T\mathcal S^{-1}q).
\tag{16}
\]

The second estimate follows from an exact orthogonal decomposition: for
y!=0, put c=(y^T S^{-1}q)/(y^T S^{-1}y). Then
q^T S^{-1}q=c^2 y^T S^{-1}y+(q-cy)^T S^{-1}(q-cy).
The discarded term is nonnegative. Also y^T S^{-1}y<=K_N(n,n)<=Z n^2.
Thus (12) removes a stage-dependent inverse-matrix difficulty but does not
remove the evaluation scale n. A common polylogarithmic bound for the
signed pairing (14), or adequate source/evaluation correlation, is still Open.
Equation (16) must not be advertised as the missing RH estimate.

## 4. A signed interval retaining the projection-loss square

Here abbreviate P=P_N, r=r_N, epsilon=||r||_Q^2>0, k=k_{N,n},
K=K_N(n,n), and w=w_{H,n}. Set

\[
E_1=\langle wr,r\rangle_Q,\quad
E_2=\|wr\|_Q^2,\quad
u=wr-\frac{E_1}{\epsilon}r,\quad
\eta_*=(I-P)u,\quad D_*^2=\|\eta_*\|_Q^2.
\]

**Proposition 3 (exact source variance and signed complement identity).**

\[
\boxed{\|Pwr\|_Q^2
=E_2-\frac{E_1^2}{\epsilon}-D_*^2
=z_w^TG^{-1}z_w=q^T\mathcal S^{-1}q.}
\tag{17}
\]

Let l=(I-P)e_n and l_0=l-(r(n)/epsilon)r. Then

\[
\boxed{S_{N,H}(n)=-\frac{r(n)E_1}{\epsilon}
-\langle l_0,\eta_*\rangle_Q,\qquad
\|l_0\|_Q^2=Zn^2-K-\frac{r(n)^2}{\epsilon}.}
\tag{18}
\]

Consequently the following two bounds hold simultaneously:

\[
|S_{N,H}(n)|^2\le K
\left(E_2-\frac{E_1^2}{\epsilon}-D_*^2\right),
\tag{19}
\]
\[
\boxed{
\left|S_{N,H}(n)+\frac{r(n)E_1}{\epsilon}\right|^2
\le\left(Zn^2-K-\frac{r(n)^2}{\epsilon}\right)D_*^2.}
\tag{20}
\]

**Proof.** Since Pr=0, Pu=Pwr and <u,r>=0. Pythagoras gives (17);
the inverse-Gram equalities are the normal equations. The vector Pwr is
orthogonal to W_{N,H} because wr is supported on the head, which gives the
last equality. Since n>H, <e_n,wr>=0. Decompose e_n=k+l and
wr=(E_1/epsilon)r+Pu+eta_*. The two projection subspaces are orthogonal,
and eta_* is orthogonal to r. This gives (18), including the norm of l_0.
Cauchy--Schwarz yields (19)--(20). Its omitted squares can be retained
explicitly: if L=||l_0||_Q^2>0, then
D_*^2=|<l_0,eta_*>|^2/L+
||eta_*-(<l_0,eta_*>/L)l_0||_Q^2. For L=0 the signed remainder is zero.

This interval is centered at a possibly negative number. It is compatible
with every lower multiplicative range having the same sign. No such sign
pattern is asserted universally. The nonnegative loss D_*^2 improves (19)
and controls (20); replacing it arbitrarily by zero would be invalid.

## 5. Moving-stage energy: exact two-stage comparison and its limitation

Fix H,n,w as above, and let M<=N. Put
Delta P=P_N-P_M, f=F_N-F_M, and Delta k=k_{N,n}-k_{M,n}.
Nested orthogonal projections give the complete identities

\[
\|f\|_Q^2=\epsilon_M-\epsilon_N,\quad
\|\Delta k\|_Q^2=K_N(n,n)-K_M(n,n),\quad r_N=r_M-f.
\]

The response difference has the exact signed form

\[
\boxed{S_{N,H}(n)-S_{M,H}(n)
=\langle wr_N,\Delta k\rangle_Q
-\langle wf,k_{M,n}\rangle_Q.}
\tag{21}
\]

The underlying vector identity is
P_Nwr_N-P_Mwr_M=Delta P wr_N-P_Mwf. Its terms are orthogonal, so the
squared norm is exactly ||Delta P wr_N||_Q^2+||P_Mwf||_Q^2.
In particular, with w_max=1/2-1/(n+1),

\[
|S_{N,H}(n)-S_{M,H}(n)|
\le w_{\max}\left[
\sqrt{\epsilon_N(K_N(n,n)-K_M(n,n))}
+\sqrt{K_M(n,n)(\epsilon_M-\epsilon_N)}\right].
\tag{22}
\]

The first, sharper version replaces w_max sqrt(epsilon_N) by ||wr_N||_Q
and w_max sqrt(epsilon_M-epsilon_N) by ||wf||_Q. Both evaluations are still
at the original physical site n. Residual energy decrease alone does not
control the kernel increment in (22). Substituting only K_N<=Z n^2 restores
a polynomial n scale, not a polylogarithm.

For each fixed H,n, the canonical projections converge strongly to projection
onto the closed union V. Thus r_N->r_infinity and k_{N,n}->k_infinity,n in Q,
and (21) also proves convergence of S_{N,H}(n). Likewise b_N->b_infinity
in Q, with b_infinity=P_V B r_infinity. This is unconditional and supplies
no uniform rate when n or H grows with N.

**Why general projection estimates cannot close the arithmetic gap.** This
is a counterexample to a proposed abstract inference, not to the squarefree
criterion. Let h_j=1_{m=j}/sqrt(Q(j)), and project onto the one-dimensional
space spanned by (h_1+h_n)/sqrt(2), for n>1. With r=(I-P)1 and b=PBr,
direct calculation gives, for every 1<=H<n,

\[
S_H(n)=b(n)=\frac{(n-1)^2}{8(n+1)}\sim\frac n8.
\tag{23}
\]

Indeed r(1)=(1-1/n)/2, K(n,1)=Zn/2, and the only nonzero centered
contribution is m=1. All full normal equations and orthogonal energy
identities hold, and ||r||<=1. Accordingly those facts alone cannot imply
a uniform polylogarithmic bound over arbitrary projection spaces. This
space is not V_N; the additional required input is arithmetic structure.

## 6. A weaker sufficient RH condition: limiting spatial mean squares

The source theorem
`QSquarefreeLogResidualTail.riemannHypothesis_of_polylog_moving_head_bound`
passes a uniform finite-stage bound to b_infinity. Inspecting its proof shows
that a common bound on the limiting response is what is consumed. The
following are paper-level extensions, not newly checked Lean declarations.

First, it suffices to have constants C>=0 and an integer A>=0, independent of n, such that

\[
\forall n\ge1:\quad
\liminf_{N\to\infty}|S_{N,H(n)}(n)|\le C\ell(n)^A.
\tag{24}
\]

The limit exists by Section 5. Equation (3) gives
|b_infinity(n)|<=(C+sqrt(Z))ell(n)^{max(A,1)}. Hence its weighted physical
tail is O(ell(M)^{2 max(A,1)}/M), contradicting the existing correction-tail
escape theorem if r_infinity is nonzero. This yields RH through the existing
residual/closure consumer. A finite-stage threshold may depend on n; no
uniform rate in that threshold is required.

There is a spatially averaged version that tolerates isolated large sites.
For M>=1 put H_M=floor(M/ell(M)) and I_M={M+1,...,2M}. Use this one cutoff
for every n in I_M, and denote S_{N,H_M}(n) by S_{N,M}^{block}(n).

**Proposition 4 (conditional block criterion).** Suppose C>=0 and an integer
A>=0 satisfy

\[
\boxed{\forall M\ge1:\quad
\liminf_{N\to\infty}\frac1M\sum_{n=M+1}^{2M}
|S_{N,M}^{\mathrm{block}}(n)|^2\le C^2\ell(M)^{2A}.}
\tag{25}
\]

Then the existing residual/closure results imply RH. It also suffices to
impose (25) only at dyadic M. The arithmetic hypothesis (25) is **Open**.

**Proof.** For a fixed block the finite sum converges with N. By (3),
|b_infinity(n)-S_infinity,M^{block}(n)|<=2sqrt(Z)ell(M). Put A'=max(A,1).
The elementary squared-sum inequality gives

\[
\frac1M\sum_{n\in I_M}|b_\infty(n)|^2
\le(2C^2+8Z)\ell(M)^{2A'}.
\]

Since Q(n)<=1/(Z M^2) on this block, its Q energy is bounded by
(2C^2+8Z)ell(M)^{2A'}/(Z M). Decompose m>M into the blocks I_{2^j M}.
Because ell(2^j M)=ell(M)+j log 2<=ell(M)(1+j), summing gives

\[
\|\mathbf1_{m>M}b_\infty\|_Q^2
\le\frac{2C^2+8Z}{Z}\,
\left(\sum_{j\ge0}2^{-j}(1+j)^{2A'}\right)
\frac{\ell(M)^{2A'}}{M}.
\tag{26}
\]

The geometric-polynomial series is finite. This contradicts
`correction_log_scaled_tail_tendsto` if r_infinity!=0, using a sufficiently
large fixed logarithmic exponent. For dyadic M only, perform the same
decomposition at dyadic starting M and use the cofinal correction-tail
criterion. Therefore r_infinity=0 and the repository's RH consumer applies.

The original uniform pointwise bound implies this averaged hypothesis via
(3). The converse pointwise control is not supplied: a block mean square
allows individual responses of size sqrt(M) times the block envelope.
This weakens the sufficient hypothesis, rather than discharging it.

There is an exact inverse-Gram expression for the arithmetic target (25).
For the common head H_M put

\[
z_j=\sum_{m\le H_M}Q(m)\beta_m^j r_N(m)v(m)\quad(j=0,1),
\quad
G_{I,j}=\sum_{n\in I_M}Q(n)\beta_n^j v(n)v(n)^T\quad(j=0,1,2),
\]

where beta_m=1/(m+1). Then

\[
\begin{aligned}
\sum_{n\in I_M}Q(n)|S_{N,M}^{block}(n)|^2
={}&z_1^TG^{-1}G_{I,0}G^{-1}z_1\\
&-2z_1^TG^{-1}G_{I,1}G^{-1}z_0\\
&+z_0^TG^{-1}G_{I,2}G^{-1}z_0.
\end{aligned}
\tag{27}
\]

The mixed term is retained with its sign. On I_M, Q(n) lies between
1/(4Z M^2) and 1/(Z M^2), so controlling (27) by
O(ell(M)^{2A}/M) is equivalent up to constants to the block target in (25).
The full matrix G is never replaced by G_{I,0}. Formula (14) permits the
same computation in the smaller exact Schur coordinates.

## 7. The N=240, n=221 diagnostic

The companion [diagnostic note](SquarefreeShortHeadSchurDiagnostics20261030.md) reproduces the source example using full
complete-period Q moments, all 149 squarefree conductors 2<=d<=241, and
ordinary Cholesky solves. It obtains

| Quantity | Exploratory value |
|---|---:|
| b_240(221) | -0.0489055412321 |
| Full lower response | -0.0491975407425 |
| Full upper response | 0.000291999510452 |
| H(221) | 19 |
| S_240,19(221) | -0.0426665815001 |
| b minus short response | -0.0062389597320 |
| Weighted divisor slope term | -0.00593172228845 |
| Weighted divisor floor term (subtracted) | 0.0367348592116 |
| Compressed dimension | 13 |
| ||S_240,19 inverse||_op | 4.15089316265 |
| Proved upper constant 4 Z L_19^2 | 53.8286309089 |
| ||(DGD) inverse||_op | 4.48767481798 |
| Proved full constant 4 Z L_241^2 | 126.724127809 |

For (17)--(20), r_240(221) is about 1.60322317,
E_2-E_1^2/epsilon is about 1.91983143e-5,
||Pwr||_Q^2 about 1.71548543e-5, and D_*^2 about 2.04345995e-6.
The centered signed interval (20) is approximately
[-0.38707719,0.31820642], with center -0.03443538. It contains the actual
short response and crosses zero, so it does not certify its sign.
The simpler response bound (19) is about 0.57097911, also far above the
actual magnitude. These numbers expose the remaining slack.

The original eight lower-range signs stay negative. Nothing in (5), (12),
(17)--(22), or (25) assumes cancellation between those ranges. The Schur
response agrees with the raw full-Gram response to about 1.5e-16; these
floating-point checks are not interval-certified error bounds.

## 8. Research consequence and next arithmetic obligation

Established on paper here: finite Mobius coefficient coercivity; the full
weighted inverse-Gram bound; the exact Schur reduction with an inverse bound
uniform in N and logarithmic in H; the source-variance and complementary
signed interval; exact two-stage comparison; and the conditional limiting
block criterion. Related abstract projection, head-prediction, and stage
variation infrastructure already exists in the repository; no novelty claim
is made for those general principles.

The most focused next target is (27), with the common logarithmic cutoff,
using (12) to control the normalized compressed inverse and (15) to expose
the actual signed divisor source. Averaging over the physical evaluation
block allows divisor correlations to be used without demanding that each
individual response be small. This is a proposed route, not a proved saving.

Still Open: a uniform polylogarithmic estimate for (14), or the weaker block
estimate (25)/(27). In particular there is no established uniform bound on
the product ||y(n)||_2||q||_2 in (16), no valid suppression of the complete
tail in (13), and no moving-stage argument that removes the evaluation
factor in (22). The normalized inverse-Gram estimate by itself does not prove
RH. No new Lean declaration or kernel verification is reported in this work.

Relevant source files: `SquarefreePrefixResponseResearch20261030.md`,
`SquarefreePrefixResponseDiagnostics20261030.md`,
`QSquarefreeLogResidualTail.lean`, `QSquarefreeHeadPrediction.lean`, and
`QSquarefreeResponsePrefixBudget.lean`. They support respectively the starting
identities, prior numerical example, conditional RH consumer, existing
head-extension interpretation, and existing stage-variation accounting.

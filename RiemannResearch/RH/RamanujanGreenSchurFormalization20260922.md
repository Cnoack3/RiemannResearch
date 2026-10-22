# Formalization status for the Ramanujan–Green–Schur calculation

Source: the user-provided calculation and ensuing discussion, 22 September 2026.
The source manuscript below records the complete mathematical calculation.
It is not itself a Lean proof. The formal coverage is recorded separately here.

## Checked finite identities

- `RH/IntegratedRamanujanMarkedArithmetic`: packet head `-mu(q)`, vanishing
  nonsquarefree head, prime-power floor formula, first value, full norm scaling,
  and common-prime-power Gram correlation scaling.
- `RH/ParetoPeriodicPacketGreen`: exact full-period Green representation,
  including its zero-boundary form on `1,...,L-1`. Progression weights retain
  every infinite-tail term.
- `LinearAlgebra/WeightedGreenInverse`: exact finite Green multiplication,
  its inverse flux difference, tridiagonal rows, and weighted Dirichlet identity.
- `Analysis/FiniteGramBasisInvariance`: actual inverse-Gram capacity invariance
  under equal finite observation spans.
- `RH/RamanujanFiniteSpanBridge`: exact finite residue/packet span equality,
  packet independence, and the original DPP `qN` as the packet inverse quadratic.
- `LinearAlgebra/RankTwoWoodbury`: matrix-level two-variable elimination from
  an actual rank-two perturbation and inverse equations, with the nonzero
  denominator explicit.
- `RH/IntegerDPPPacketRankTwo`: the explicit finite cotangent sum and
  double-divisor core, with proved symmetry. Its Gram identification is
  kept separate as described below.

## Conditional research reductions

`RH/IntegratedRamanujanRankTwo` and `RH/IntegerDPPPacketRankTwo` specialize
that elimination to actual arithmetic Gram matrices and to the existing `qN`.
Their conclusions are conditional on the following explicit hypotheses:

1. **Open provider:** the complete cotangent evaluation identifying the actual
   Gram as `pi*F + (Lambda*phi^T + phi*Lambda^T)/2` for the proposed cotangent `F`.
2. **Open provider:** an actual inverse `R` of that proposed core, with its
   required symmetry, for each finite stage `N >= 2`.
3. **Open provider:** nonvanishing of the displayed two-dimensional denominator
   for that arithmetic core. The manuscript's inertia/determinant proof is
   not yet a Lean provider.

The theorems do not assume their desired marked quadratic conclusion.
The inverse of the actual packet Gram is supplied by proved independence.
The unresolved inverse premise concerns the separate cotangent core `F`.

## Further source obligations

The radical reduction beyond the proved prime-power/common-dilation cases,
explicit cotangent and digamma evaluations, the algebraic-core inertia and
its determinant formula, and the complete Mellin product arguments below
are recorded as source arguments, not new checked results of this addition.
Existing project modules retain their separately checked CRT and mean results.
**Open:** `qN N -> 1`. No statement here proves that limit or RH.

---

# Source manuscript (informal)

# Ramanujan, periodic sums, Green matrices, CRT, orthogonality, and Schur reduction for q_N

Date: 2026-09-22.

## Main outcome

The transformations below preserve exactly the previously constructed full-Pareto orthonormal basis e_2,...,e_(N+1). They give:

1. Primitive Ramanujan generators with first-site vector -mu and constant-target vector Lambda.
2. Exact reductions of norms and cross-Gram entries by repeated prime factors.
3. A genuine Green representation with an explicitly tridiagonal inverse before compression.
4. A decomposition of the full Gram matrix into an algebraic cotangent matrix plus a term of rank at most two.
5. An exact two-by-two Schur formula for A_N=b_N^T G_N^{-1}b_N and q_N.

The remaining algebraic matrix retains interactions between conductors. No independent-prime product for q_N is assumed.

## 1. Conventions

Let
\[
w_n=\frac1{n(n+1)},\quad
g_d(n)=\frac{n\bmod d}{d},\quad r_d(n)=n\bmod d.
\]
Stage N consists of conductors d=2,...,N+1. Write
\[
G_N=(\langle g_d,g_e\rangle_H),\quad
B_N=(\langle r_d,r_e\rangle_H),\quad
b_N=(1/d)_{d=2}^{N+1},
\]
\[
A_N=b_N^TG_N^{-1}b_N,\qquad
L_N=\operatorname{lcm}(2,\ldots,N+1),\qquad
q_N=W_{L_N}(1)A_N.
\]
All inner products here use the complete infinite Pareto measure.
Functions used with floor dilations are extended by f(0)=0.

## 2. Ramanujan sums and a basis change preserving the existing e_d

Define
\[
c_d(n)=\sum_{a\mid\gcd(d,n)}a\mu(d/a).
\]
For d>=2, put
\[
\boxed{
h_d(n)=-\sum_{j=1}^n c_d(j)
=\sum_{a\mid d}\mu(d/a)r_a(n).
}
\]
The inverse divisor transform is
\[
r_d=\sum_{\substack{a\mid d\\a>1}}h_a.
\]
These follow from
\[
r_d(n)-r_d(n-1)=1-d\mathbf1_{d\mid n}
=-\sum_{\substack{a\mid d\\a>1}}c_a(n).
\]

Crucially,
\[
h_d=d\,g_d+\text{a combination of earlier generators}.
\]
Thus the orthogonal residual for h_d equals d times the residual for g_d.
Because d>0, their normalized Gram-Schmidt vectors agree exactly:
\[
\boxed{e_d^{\,h}=e_d^{\,g}.}
\]

Equivalently, let M_N have entries
\[
(M_N)_{d,a}=\mathbf1_{a\mid d}\mu(d/a),
\qquad d,a=2,\ldots,N+1.
\]
Then h=M_N r, and M_N is lower triangular with diagonal one.
If B_N=R_N R_N^T is its positive-diagonal Cholesky factorization,
\[
\Xi_N:=M_NB_NM_N^T=(M_NR_N)(M_NR_N)^T.
\]
The matrix M_NR_N is already lower triangular with positive diagonal, so
\[
(M_NR_N)^{-1}h=R_N^{-1}r.
\]
This directly reuses the existing orthonormal basis rather than replacing it.

The two relevant linear functionals simplify:
\[
\boxed{
h_d(1)=-\mu(d),\qquad
\langle\mathbf1,h_d\rangle_H=\Lambda(d),
}
\]
where
\[
\Lambda(d)=
\begin{cases}\log p,&d=p^a,\\0,&\text{otherwise}.\end{cases}
\]
Indeed, <1,r_a>=log a and the divisor convolution mu*log is Lambda.

Writing bold mu, phi, and Lambda for the corresponding vectors indexed by
2,...,N+1, one obtains
\[
\boxed{
A_N=\boldsymbol\mu^T\Xi_N^{-1}\boldsymbol\mu,\qquad
\|P_N\mathbf1\|_H^2=
\boldsymbol\Lambda^T\Xi_N^{-1}\boldsymbol\Lambda.
}
\]
These are distinct finite projection quantities.

## 3. CRT and exact repeated-prime-factor reductions

Ramanujan sums factor exactly:
\[
c_d(n)=\prod_{p^a\parallel d}c_{p^a}(n),
\]
\[
c_{p^a}(n)=
\begin{cases}
p^{a-1}(p-1),&p^a\mid n,\\
-p^{a-1},&p^{a-1}\mid n,\ p^a\nmid n,\\
0,&p^{a-1}\nmid n.
\end{cases}
\]
Let s=rad(d) and t=d/s. Then
\[
c_d(n)=t\,\mathbf1_{t\mid n}c_s(n/t),
\qquad
\boxed{h_d(n)=t\,h_s(\lfloor n/t\rfloor).}
\]
For D_t f(n)=f(floor(n/t)),
\[
\sum_{n=tk}^{t(k+1)-1}w_n
=\frac1{tk}-\frac1{t(k+1)}
=\frac1t w_k\quad(k\ge1).
\]
The initial block contributes zero because f(0)=0. Therefore
\[
\boxed{\langle D_tf,D_tg\rangle_H=\frac1t\langle f,g\rangle_H.}
\]
Consequently,
\[
\boxed{
\Xi_{dd}=\frac d{\operatorname{rad}(d)}
\Xi_{\operatorname{rad}(d),\operatorname{rad}(d)}.
}
\]
More generally, with
\[
u=\gcd\left(\frac d{\operatorname{rad}(d)},
           \frac e{\operatorname{rad}(e)}\right),
\]
\[
\boxed{\Xi_{de}=u\,\Xi_{d/u,e/u}.}
\]

For prime powers,
\[
h_{p^a}(n)=p^{a-1}
\bigl(\lfloor n/p^{a-1}\rfloor\bmod p\bigr),
\]
\[
\boxed{\|h_{p^a}\|_H^2=p^{a-1}\|h_p\|_H^2.}
\]
Some explicit exact values are
\[
\|h_{2^a}\|_H^2=2^{a-1}\log2,
\]
\[
\|h_{3^b}\|_H^2=
3^{b-1}\left(2\log3-\frac{\pi}{3\sqrt3}\right),
\]
\[
\boxed{
\|h_{2^a3^b}\|_H^2
=2^{a-1}3^{b-1}\frac{\pi}{\sqrt3}
\quad(a,b\ge1).
}
\]
The last identity uses h_6=r_6-r_3-r_2 and the exact value
\[
\|h_6\|_H^2=\frac{\pi}{\sqrt3}.
\]

## 4. Periodic summation and the full Green matrix

For a common period L, use the full-tail weights
\[
W_L(r)=\sum_{k=0}^\infty\frac1{(r+kL)(r+kL+1)}
=\frac{\psi((r+1)/L)-\psi(r/L)}L.
\]
Since h_d(L)=0 for d|L,
\[
\Xi_{de}=\sum_{r=1}^{L-1}W_L(r)h_d(r)h_e(r).
\]
Set
\[
C_{k,d}=c_d(k),\qquad 1\le k<L,
\]
and
\[
\boxed{
K_L(k,j)=\sum_{r=\max(k,j)}^{L-1}W_L(r)
=\frac{\psi(1)-\psi(\max(k,j)/L)}L.
}
\]
Then the exact Green factorization is
\[
\boxed{\Xi_N=C^T K_L C.}
\]

Let P be the lower triangular matrix P_(r,k)=1_(k<=r), with indices1,...,L-1.
Then K_L=P^T diag(W_L(1),...,W_L(L-1))P. Its inverse is tridiagonal:
\[
(K_L^{-1})_{11}=\frac1{W_L(1)},
\]
\[
(K_L^{-1})_{kk}=
\frac1{W_L(k-1)}+\frac1{W_L(k)}\quad(k\ge2),
\]
\[
(K_L^{-1})_{k,k+1}=(K_L^{-1})_{k+1,k}
=-\frac1{W_L(k)}.
\]
This is a true finite Green matrix retaining the entire infinite Pareto tail.
All summations in its derivation are finite after grouping into one period;
there is no unlicensed rearrangement of an infinite double sum.

## 5. What orthogonality and CRT actually diagonalize

On a full period, Ramanujan sums satisfy
\[
\frac1L\sum_{n=1}^L c_d(n)c_e(n)=\varphi(d)\mathbf1_{d=e}.
\]
Their integrated modes satisfy
\[
\boxed{
\frac1L\sum_{n=1}^L h_d(n)h_e(n)
=\frac{\varphi(d)\varphi(e)}4+
\mathbf1_{d=e}\frac{J_2(d)}{12},
}
\]
where
\[
J_2(d)=d^2\prod_{p\mid d}(1-p^{-2}).
\]
To see this, the centered h_d have disjoint primitive-frequency supports;
their squared Fourier coefficients sum to
\[
\frac14\sum_{\substack{1\le a<d\\(a,d)=1}}
\csc^2(\pi a/d)=\frac{J_2(d)}{12}.
\]
Thus the uniform reference Gram is diagonal plus rank one, with explicit
multiplicative diagonal entries.

The actual Pareto Gram equals
\[
\Xi_N=\operatorname{diag}(J_2(d)/12)
+\frac14\boldsymbol\varphi\boldsymbol\varphi^T+\mathcal E_N,
\]
\[
(\mathcal E_N)_{de}
=\sum_{r=1}^L\left(W_L(r)-\frac1L\right)h_d(r)h_e(r).
\]
This correction is retained throughout. For example,
\[
\left\langle h_2-\frac12,h_3-1\right\rangle_H
=\frac12-\frac{\pi}{3\sqrt3}\ne0,
\]
although the corresponding uniform-period inner product is zero.

## 6. Explicit cotangent entries and the rank-two logarithmic term

Define the finite algebraic cotangent sums
\[
V(a,b)=\sum_{r=1}^{b-1}\left\{\frac{ar}{b}\right\}
\cot\frac{\pi r}{b},\qquad V(a,1)=0.
\]
The full scaled residue Gram is
\[
B_{ab}=
\frac{(b-1)\log a+(a-1)\log b}{2}
+\frac\pi2[V(1,a)+V(1,b)-V(a,b)-V(b,a)].
\]
Apply the divisor transform on both indices. The terms depending on only
one index cancel because sum_(a|d)mu(d/a)=0 for d>1. The logarithmic terms
use sum mu(d/a)(a-1)=phi(d) and sum mu(d/a)log a=Lambda(d).

Define the symmetric algebraic matrix F_N by
\[
\boxed{
(F_N)_{de}=
-\frac12\sum_{\substack{a\mid d\\b\mid e}}
\mu(d/a)\mu(e/b)[V(a,b)+V(b,a)].
}
\]
Then
\[
\boxed{
\Xi_N=\pi F_N+
\frac12\left(
\boldsymbol\Lambda\boldsymbol\varphi^T+
\boldsymbol\varphi\boldsymbol\Lambda^T
\right).
}
\]
Every entry of F_N is algebraic, since cotangents of rational multiples of
pi are algebraic. The entire logarithmic dependence has rank at most two.

The identity also shows that every determinant and cofactor of Xi_N is a
polynomial of total degree at most two in the prime logarithms, with
coefficients in the field generated by pi and these explicit algebraic
cotangent values.

## 7. The algebraic matrix is invertible: no conditional inverse

For every x with Lambda^T x=0,
\[
\pi x^TF_Nx=x^T\Xi_Nx>0\quad(x\ne0).
\]
Therefore F_N is positive definite on a hyperplane and has at most one
nonpositive eigenvalue.

For N>=2, its leading block is
\[
\begin{pmatrix}
0&-1/(3\sqrt3)\\
-1/(3\sqrt3)&-1/(3\sqrt3)
\end{pmatrix},
\]
which has negative determinant and hence a negative direction.
It follows that F_N has exactly one negative and N-1 positive eigenvalues.
In particular,
\[
\boxed{\det F_N<0,\qquad F_N^{-1}\text{ exists for every }N\ge2.}
\]
For N=1, F_1=0, and the initial exact value remains A_1=1/log2, q_1=1.

## 8. Exact two-by-two Schur formula for A_N and q_N

For x,y in {mu,phi,Lambda}, define
\[
\rho_{xy}=x^TF_N^{-1}y.
\]
These scalars are explicit:
\[
\rho_{xy}=
\frac{\sum_{d,e=2}^{N+1}
x_d\,\operatorname{adj}(F_N)_{de}\,y_e}{\det F_N}.
\]
The rho values with only mu and phi are algebraic. Those with one Lambda
are linear combinations of prime logarithms; rho_(Lambda,Lambda) is
quadratic in those logarithms.

Set
\[
\mathcal D_N=
\rho_{\varphi\varphi}\rho_{\Lambda\Lambda}
-(\rho_{\varphi\Lambda}+2\pi)^2,
\]
\[
\mathcal Q_N=
\rho_{\Lambda\Lambda}\rho_{\mu\varphi}^2
-2(\rho_{\varphi\Lambda}+2\pi)
 \rho_{\mu\varphi}\rho_{\mu\Lambda}
+\rho_{\varphi\varphi}\rho_{\mu\Lambda}^2.
\]
Then, for every N>=2,
\[
\boxed{
A_N=\frac1\pi\left(
\rho_{\mu\mu}-\frac{\mathcal Q_N}{\mathcal D_N}
\right),
}
\]
\[
\boxed{
q_N=\frac{W_{L_N}(1)}{\pi}\left(
\rho_{\mu\mu}-\frac{\mathcal Q_N}{\mathcal D_N}
\right).
}
\]

Proof: write U=[phi,Lambda] and T=[[0,1/2],[1/2,0]], so
Xi=pi F+UTU^T. Woodbury reduction gives the two-by-two matrix
\[
T^{-1}+U^T(\pi F)^{-1}U
=\frac1\pi
\begin{pmatrix}
\rho_{\varphi\varphi}&\rho_{\varphi\Lambda}+2\pi\\
\rho_{\varphi\Lambda}+2\pi&\rho_{\Lambda\Lambda}
\end{pmatrix}.
\]
Its explicit inverse yields the displayed scalar formula.

There is no zero-denominator issue:
\[
\boxed{
\det\Xi_N=-\frac{\pi^{N-2}}4\det(F_N)\mathcal D_N.
}
\]
Since det Xi_N>0 and det F_N<0, one has D_N>0.

This formula reduces inversion of a matrix containing transcendental
logarithms to inversion of an explicitly algebraic cotangent matrix and
a two-by-two inverse. It does not assert a product of independent factors
for the different primes.

## 9. Schur reduction of squareful modes and the existing recurrence

Partition conductors into squarefree Q and nonsquarefree Z. Because mu_Z=0,
\[
\boxed{
A_N=
\mu_Q^T
\left(\Xi_{QQ}-\Xi_{QZ}\Xi_{ZZ}^{-1}\Xi_{ZQ}\right)^{-1}\mu_Q.
}
\]
For the constant target, an analogous Schur reduction retains prime-power
indices, since Lambda vanishes elsewhere.

For a new conductor m=N+2, put
\[
\xi=(\Xi_{d,m})_{d=2}^{N+1},\qquad \kappa=\Xi_{m,m}.
\]
The exact original increment is
\[
\boxed{
\frac{\eta_N^2}{\sigma_N}
=
\frac{[\mu(m)-\xi^T\Xi_N^{-1}\boldsymbol\mu]^2}
{\kappa-\xi^T\Xi_N^{-1}\xi}
=|e_m(1)|^2.
}
\]
The denominator is m^2 sigma_N. The unsquared numerator is -m eta_N.
A zero value mu(m)=0 does not remove the mixed term.

For example, with a=log2, b=log3, c=pi/sqrt3, define
\[
u=a+b/2-c/3,\quad v=2b-c/3,
\quad s=3a/2-\pi/4,\quad t=a+b+c/3-\pi/2.
\]
Then
\[
\Xi_{\{2,3,4\}}=
\begin{pmatrix}a&u&s\\u&v&t\\s&t&2a\end{pmatrix},
\quad
(h_2(1),h_3(1),h_4(1))=(1,1,0).
\]
Writing Delta=av-u^2,
\[
\frac{\eta_2^2}{\sigma_2}
=
\frac{[s(v-u)+t(a-u)]^2}
{\Delta[2a\Delta-vs^2+2ust-at^2]}.
\]
Thus the base-two digit mode h_4 improves the first-site projection through
its full-Pareto correlations with earlier modes.

## 10. Mellin products at the generator level

As an additional exact consequence,
\[
\widehat h_d(s)
=\int_1^\infty h_d(\lfloor x\rfloor)x^{-s-1}\,dx
=-\frac{\zeta(s)}s J_{1-s}(d),
\]
\[
\boxed{
\widehat h_d(s)
=-\frac{\zeta(s)}s
\left(\frac d{\operatorname{rad}(d)}\right)^{1-s}
\prod_{p\mid d}(p^{1-s}-1).
}
\]
Initially the integral is defined for Re(s)>0, with the removable value at
s=1. At s=1, the pole cancellation gives Lambda(d). When d has at least two
distinct prime factors, that value is zero. These are genuine multiplicative
formulas for the transformed generators, not an Euler product for A_N.

## 11. Verification and scope

The separate numerical verification script from the source discussion uses Arb real balls at 320 bits; it is not a Lean proof or part of this module build.

- For N=2,...,20, the primitive Gram from the divisor transform agrees with
  the algebraic-plus-rank-two decomposition.
- The two-by-two Schur formula agrees with direct full-Gram evaluation.
- The determinant identity and positivity of D_N are checked.
- With L=60, the finite Green formula Xi=C^T K C is checked against the
  original full-tail Gram matrix.
- The explicit tridiagonal inverse is checked by multiplication with K.
- The uniform-period orthogonality formula is checked for d,e=2,...,6.
- The exact norm ||h_6||^2=pi/sqrt3 is checked.

These numerical checks are separate from Lean verification. The manuscript
provides informal arguments for the all-N identities; only the coverage
listed at the top of this document is claimed as formalized. The resulting q values agree
with the prior certified calculations, including
q_2=0.77283480254059759972... and q_3=0.83084822945111103003....

The unchanged orthonormal basis still gives
\[
A_N=\sum_{d=2}^{N+1}|e_d(1)|^2,\qquad q_N=W_{L_N}(1)A_N.
\]
No step above replaces the Pareto weight by uniform CRT weight or assumes
that the infinite coefficient sum equals its RH endpoint. The remaining
asymptotic task is to control the displayed coupled Schur quantities as
N tends to infinity.

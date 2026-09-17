# Conditional iid, Cesàro smoothing, and the remaining RH criterion

Date: 2026-09-17.

Status: mathematical theorem statements and proofs, written without using Lean. No new kernel-verification claim is made. This completes the analytic and finite-algebra arguments in the supplied `Conditional_IID_Cesaro_Nyman_RH_Handoff_2026-09-16.md`, with the classical dependencies identified below. It does not construct an RH-strength bounded-energy family.

The main additional reduction is an exact variational characterization. Define

\[
E_Y=\inf\{\|\mathsf CF\|_J^2:F\in V,\ F(n)=1\ (1\le n\le Y)\}.
\]

We prove

\[
\frac{Y}{Y+2}\le E_Y\le\frac{Y(2Y+1)}{Y+2}<2Y,
\]

and, using the classical weighted Nyman–Beurling–Báez-Duarte theorem,

\[
\boxed{\mathrm{RH}\iff\sup_{Y\ge1}E_Y<\infty
\iff E_Y=\frac{Y}{Y+2}\text{ for every }Y.}
\]

The upper bound here is unconditional; the boundedness and exact-infimum assertions are equivalences with RH. Section 11 expresses every finite-generator minimum through the full signed Gram matrix and an exact Schur complement. An infimum over legal functions need not be attained by a legal function.

## 1. Definitions and classical dependencies

All arithmetic indices are positive integers. Row indices are also taken positive. Set

\[
w_n=\frac1{n(n+1)},\qquad q_t=\frac2{(t+1)(t+2)},
\]

\[
H=\ell^2(w),\qquad J=\ell^2(q),\qquad
(\mathsf CF)(t)=\frac1t\sum_{n=1}^tF(n).
\]

The spaces are real unless explicitly complexified. Coordinate values are unambiguous because every weight is positive. Let

\[
g_d(n)=\{n/d\},\quad d\ge2,\qquad
V=\operatorname{span}_{\mathbb R}\{g_d:d\ge2\}.
\]

Every member of this algebraic span has finite generator support, is bounded and periodic, and belongs to H. Coefficients are deterministic and do not depend on T or on the evaluation coordinate.

We use the established theorem

\[
\mathrm{RH}\iff1\in\overline V^H\iff\overline V^H=H.
\tag{NB}
\]

This exact weighted-sequence formulation is [Bagchi, Theorem 1](https://arxiv.org/html/math/0607733v1). The real version follows from the complex version by taking real parts. This deep classical theorem is an explicit input, not reproved here and not asserted to be available in the Lean repository.

We also use the classical analytic continuation of zeta and its reflection symmetry, as recorded in [DLMF §25.4](https://dlmf.nist.gov/25.4). The optional sieve asymptotic in Section 9 uses the prime-reciprocal estimate [DLMF 27.11.8](https://dlmf.nist.gov/27.11#E8). All further deductions below are proved explicitly. They are not claims of priority over the literature.

The basic telescoping identities are

\[
\sum_{n\ge1}w_n=\sum_{t\ge1}q_t=1,
\quad
\frac{q_t}{t}=w_t-w_{t+1},
\quad
\sum_{t\ge n}\frac{q_t}{t}=w_n,
\tag{1.1}
\]

\[
Q_Y:=\sum_{t=1}^Yq_t=\frac{Y}{Y+2},\qquad
\sum_{t>Y}q_t=\frac2{Y+2}.
\tag{1.2}
\]

For a source sequence f, its cumulative witness is \(Sf(n)=\sum_{m\le n}f(m)\). Finite interchange gives

\[
\mathsf CSf(t)=\frac1t\sum_{m=1}^t(t-m+1)f(m).
\]

Thus the conditional-mean source energy is \(\|\mathsf CSf\|_J^2\), not \(\|\mathsf Cf\|_J^2\).

## 2. The actual infinite conditional-iid model

Let \(U_t=t^{-1}\sum_{n=1}^t\delta_n\). On the product measurable space

\[
\Omega=\mathbb N_{>0}\times(\mathbb N_{>0})^{\mathbb N_{>0}}
\]

define

\[
P_t=\delta_t\otimes U_t^{\otimes\mathbb N_{>0}},\qquad
P(A)=\sum_{t\ge1}q_tP_t(A).
\tag{2.1}
\]

The countable product measure exists by the product-measure theorem. Nonnegative interchange proves countable additivity of P, and (1.1) proves P(Ω)=1. This constructs a single measure supporting the whole infinite sequence.

Write T for the first coordinate, K_i for row coordinate i, and \(\mathcal G=\sigma(T)\). For finite I and arbitrary subsets B_i of the positive integers,

\[
P(T=t,\ K_i\in B_i\ \forall i\in I)
=q_t\prod_{i\in I}U_t(B_i).
\tag{2.2}
\]

Only the t-th component contributes to this event, and its row law is a product. Since q_t>0, division by q_t gives the conditional product law on every latent atom.

To pass from this statement to actual conditional expectations, let X be integrable and put

\[
\psi_X(t)=q_t^{-1}\int_{\{T=t\}}X\,dP.
\]

Then \(\sum_tq_t|\psi_X(t)|\le\int|X|dP\). Every event of \(\sigma(T)\) is a union of latent atoms, so absolute summability permits summing their integral identities. Consequently

\[
E[X\mid\mathcal G]=\psi_X(T)\quad P\text{-a.s.}
\tag{2.3}
\]

Apply (2.3) to the indicators in (2.2). It gives

\[
E\left[\prod_{i\in I}\mathbf1_{B_i}(K_i)\mid\mathcal G\right]
=\prod_{i\in I}E[\mathbf1_{B_i}(K_i)\mid\mathcal G],
\]

and \(E[\mathbf1_B(K_i)\mid\mathcal G]=U_T(B)\), independently of i. These are conditional independence and identical conditional laws for the actual constructed random variables.

The marginal is, by (1.1),

\[
P(K_i=n)=\sum_{t\ge n}q_t/t=w_n.
\tag{2.4}
\]

Every finite permutation of row coordinates preserves each P_t on cylinders, hence on the generated sigma algebra, and therefore preserves P. Thus the sequence is exchangeable.

Under P_t all K_i≤t, and

\[
P_t(K_1<t,\ldots,K_r<t)=(1-1/t)^r\longrightarrow0.
\]

Continuity from above proves that some row equals t almost surely. Afterwards the running maximum equals t. Summing these probability-one statements over the countable mixture proves

\[
\max_{i\le r}K_i=T\quad\text{eventually, }P\text{-a.s.}
\tag{2.5}
\]

For a stronger common-event statement, under P_t apply the strong law to the finitely many indicators \(\mathbf1_{K_i=n}\), 1≤n≤t. On their common probability-one event, the empirical frequencies tend to 1/t. Taking the countable mixture yields one probability-one event on which, for every fixed arithmetic function F,

\[
\frac1r\sum_{i=1}^rF(K_i)\longrightarrow\mathsf CF(T).
\tag{2.6}
\]

This simultaneous assertion is possible because each realization has finite support {1,…,T}. It does not imply convergence for an arbitrarily changing triangular array F_r without quantitative control.

### Prime-exponent rows

Set \(N_i=2K_i\) and \(A_i=(v_p(N_i))_{p\text{ prime}}\). The map from an integer to its valuation vector is measurable: each coordinate is a map on a countable discrete space. Unique factorization gives finite support and a nonzero row, since N_i≥2. Taking preimages in the conditional product law proves that the rows A_i are conditionally iid given T.

Almost surely N_i≤2T for every i, so all active prime columns lie in the finite set of primes at most 2T. No within-row prime independence is asserted. In particular, for positive a,b,d,

\[
P(d\mid K_i\mid T=t)=\frac{\lfloor t/d\rfloor}{t},
\quad
P(a\mid K_i,\ b\mid K_i\mid T=t)
=\frac{\lfloor t/\operatorname{lcm}(a,b)\rfloor}{t}.
\tag{2.7}
\]

These follow by counting multiples. For distinct rows, conditional probabilities multiply by (2.2).

## 3. Integrability and exact moment identities

Let F,G∈H be real and c∈ℝ. By (2.4),

\[
E|F(K_i)|^2=\|F\|_H^2<\infty.
\]

Define

\[
M_F(t)=\mathsf CF(t),\qquad
V_F(t)=\frac1t\sum_{n\le t}(F(n)-M_F(t))^2.
\]

Jensen followed by nonnegative interchange and (1.1) gives

\[
\sum_tq_t|M_F(t)|^2
\le\sum_t\frac{q_t}{t}\sum_{n\le t}|F(n)|^2
=\|F\|_H^2.
\tag{3.1}
\]

Finite variance decomposition on each atom gives

\[
\sum_tq_tV_F(t)=\|F\|_H^2-\|\mathsf CF\|_J^2<\infty.
\tag{3.2}
\]

Hence all conditional means, squares and variances used below have their required integrability. Also

\[
E|F(K_i)G(K_j)|\le\|F\|_H\|G\|_H,
\quad
\sum_tq_t|M_F(t)M_G(t)|\le\|F\|_H\|G\|_H.
\]

Using (2.3) and the finite uniform law on each atom proves

\[
E[F(K_i)\mid\mathcal G]=M_F(T),
\]

\[
E[F(K_i)^2\mid\mathcal G]=\frac1T\sum_{n\le T}F(n)^2,
\quad
\operatorname{Var}(F(K_i)\mid\mathcal G)=V_F(T),
\tag{3.3}
\]

and, for i≠j,

\[
E[F(K_i)G(K_j)\mid\mathcal G]=M_F(T)M_G(T).
\tag{3.4}
\]

For \(\overline F_r=r^{-1}\sum_{i=1}^rF(K_i)\), expand the square conditionally. The r diagonal centered terms contribute V_F(T); all distinct-row centered products vanish by (3.4). Thus

\[
E[(\overline F_r-c)^2\mid\mathcal G]
=V_F(T)/r+(M_F(T)-c)^2,
\tag{3.5}
\]

\[
\boxed{E(\overline F_r-c)^2
=\frac1r\|F-c\|_H^2+\left(1-\frac1r\right)\|\mathsf C(F-c)\|_J^2.}
\tag{3.6}
\]

In particular \(E|\overline F_r-M_F(T)|^2=r^{-1}EV_F(T)\to0\). For fixed r,

\[
\frac1r\|F-c\|_H^2\le E(\overline F_r-c)^2\le\|F-c\|_H^2.
\tag{3.7}
\]

The conditional two-replica squared difference has expectation 2V_F(T), so

\[
\|F-c\|_H^2=\|\mathsf CF-c\|_J^2+\tfrac12E(F(K_1)-F(K_2))^2.
\tag{3.8}
\]

Expanding the corresponding product, or polarizing, gives

\[
\langle F,G\rangle_H=\langle\mathsf CF,\mathsf CG\rangle_J
+\tfrac12E[(F(K_1)-F(K_2))(G(K_1)-G(K_2))].
\tag{3.9}
\]

These are signed identities. For complex functions, conjugate the second factor in inner products and replace squares of magnitudes accordingly.

## 4. The operator, its adjoint, and the exact row kernel

Equation (3.1) makes C a continuous linear contraction H→J, and C1=1. Put \(0\cdot\mathsf CF(0)=0\). Direct subtraction of partial sums gives

\[
F(n)=n\mathsf CF(n)-(n-1)\mathsf CF(n-1).
\tag{4.1}
\]

Thus C is injective. For \(e_N=\delta_N-\delta_{N+1}\),

\[
\mathsf Ce_N=\delta_N/N,\quad
\|e_N\|_H^2=\frac2{N(N+2)},\quad
\|\mathsf Ce_N\|_J^2=\frac2{N^2(N+1)(N+2)}.
\tag{4.2}
\]

Their squared-norm ratio is \(1/[N(N+1)]\to0\); hence C has no positive uniform lower norm bound. Its range contains every finite-support sequence because \(\mathsf C(Ne_N)=\delta_N\), so its range is dense. If that range were closed, the bounded inverse theorem applied to C onto its range would contradict (4.2). Therefore the range is not closed.

Bayes' formula on the positive-probability atom K_1=n gives

\[
P(T=t\mid K_1=n)=\frac{q_t}{tw_n}\mathbf1_{t\ge n}.
\tag{4.3}
\]

Consequently

\[
(\mathsf C^*G)(n)=w_n^{-1}\sum_{t\ge n}\frac{q_t}{t}G(t).
\tag{4.4}
\]

The tail converges absolutely for G∈J by Cauchy–Schwarz against \(\sum_{t\ge n}q_t/t^2<\infty\). Jensen for (4.3) proves \(\|C^*G\|_H\le\|G\|_J\). Absolute interchange is justified by

\[
\sum_tq_t|G(t)|\mathsf C|F|(t)\le\|G\|_J\|F\|_H.
\]

It proves the adjoint identity, and (1.1) gives C*1=1. Consecutive tails satisfy

\[
w_nC^*G(n)-w_{n+1}C^*G(n+1)=q_nG(n)/n,
\]

so C* is injective too.

For real F,G∈H, the full row kernel is

\[
E[F(K_1)G(K_2)]
=\sum_{a,b\ge1}F(a)G(b)K(\max(a,b))
=\langle CF,CG\rangle_J,
\tag{4.5}
\]

where

\[
K(m)=\sum_{t\ge m}\frac{q_t}{t^2}
=\sum_{t\ge m}\frac1{t^2}-\frac3{2m}+\frac1{2(m+1)}.
\tag{4.6}
\]

Indeed

\[
\frac{2}{t^2(t+1)(t+2)}
=\frac1{t^2}-\frac3{2t}+\frac2{t+1}-\frac1{2(t+2)},
\]

and the last three terms telescope. Even for general H functions, the double series in (4.5) is absolutely convergent: its absolute-value series equals
\(\langle C|F|,C|G|\rangle_J\le\|F\|_H\|G\|_H\).
This is justification for interchange, not replacement of signed correlations in (4.5).

The transition probabilities

\[
P(n,m)=K(\max(n,m))/w_n
\]

sum to one in m and satisfy \(w_nP(n,m)=w_mP(m,n)\). They describe K→T→a new conditional row; their operator is C*C. Positivity as a quadratic form follows from \(\langle F,C^*CF\rangle_H=\|CF\|_J^2\).

## 5. Complete Mellin estimates with the boundary retained

For s∈ℂ write σ=Re(s), and define positive-base powers by \(x^{-s}=e^{-s\log x}\). Set

\[
a_s(n)=n^{-s}-(n+1)^{-s},\qquad
b_s(n)=n(a_s(n)-a_s(n+1)).
\]

For σ>0, the fundamental theorem of calculus, applied once and twice, gives

\[
a_s(n)=s\int_0^1(n+u)^{-s-1}\,du,
\]

\[
b_s(n)=s(s+1)n\int_0^1\int_0^1(n+u+v)^{-s-2}\,du\,dv.
\tag{5.1}
\]

Since the real parts of both decay exponents are positive,

\[
|a_s(n)|\le|s|n^{-\sigma-1},\qquad
|b_s(n)|\le|s(s+1)|n^{-\sigma-1}.
\tag{5.2}
\]

For σ>1/2, use \(1/w_n\le2n^2\), \(1/q_n\le3n^2\) to obtain

\[
\sum_n\frac{|a_s(n)|^2}{w_n}\le2|s|^2\zeta(2\sigma)<\infty,
\]

\[
D_s:=\sum_n\frac{|b_s(n)|^2}{q_n}
\le3|s(s+1)|^2\zeta(2\sigma)<\infty.
\tag{5.3}
\]

For integer Y≥1, comparison of a decreasing power with its integral yields

\[
\tau_s(Y):=\sum_{n>Y}\frac{|b_s(n)|^2}{q_n}
\le\frac{3|s(s+1)|^2}{2\sigma-1}Y^{1-2\sigma}.
\tag{5.4}
\]

Weighted Cauchy–Schwarz shows absolute convergence of

\[
L_s(F)=\sum_na_s(n)F(n),\quad F\in H_{\mathbb C},
\qquad
\Lambda_s(M)=\sum_nb_s(n)M(n),\quad M\in J_{\mathbb C}.
\]

They are continuous complex-linear functionals, with \(\|\Lambda_s\|=\sqrt{D_s}\). Equality in this norm assertion follows by using the representing vector with coordinates \(\overline{b_s(n)}/q_n\).

Substituting (4.1) and shifting a finite sum proves, with no convergence assumptions,

\[
\sum_{n=1}^Ra_s(n)F(n)
=\sum_{n=1}^Rb_s(n)CF(n)+Ra_s(R+1)CF(R).
\tag{5.5}
\]

Here is a direct boundary estimate for every F∈H, stronger than merely treating bounded F. Since

\[
\sum_{n=1}^R1/w_n=R(R+1)(R+2)/3,
\]

Cauchy–Schwarz gives

\[
|Ra_s(R+1)CF(R)|
\le |s|\|F\|_H(R+1)^{-\sigma-1}
\sqrt{R(R+1)(R+2)/3}\longrightarrow0
\tag{5.6}
\]

when σ>1/2. Taking limits in the absolutely convergent series proves

\[
\boxed{\Lambda_s(CF)=L_s(F),\quad F\in H_{\mathbb C}.}
\tag{5.7}
\]

For a bounded F the boundary also tends to zero whenever σ>0, using \(|CF(R)|\le\|F\|_\infty\).

Finite telescoping yields

\[
B_s(Y):=\sum_{n=1}^Yb_s(n)
=1-(Y+1)^{-s}-Ya_s(Y+1).
\tag{5.8}
\]

Therefore

\[
|1-B_s(Y)|\le(1+|s|)(Y+1)^{-\sigma},\qquad
\Lambda_s(1)=1.
\tag{5.9}
\]

In particular D_s≥1, by Cauchy–Schwarz and \(\|1\|_J=1\).

### Legal-generator normalization and analytic continuation

For n≥1, with g_d(0)=0,

\[
g_d(n)-g_d(n-1)=d^{-1}-\mathbf1_{d\mid n}.
\]

When σ>1, finite summation by parts and a vanishing bounded boundary give

\[
L_s(g_d)=\sum_{n\ge1}n^{-s}
(d^{-1}-\mathbf1_{d\mid n})
=(d^{-1}-d^{-s})\zeta(s).
\tag{5.10}
\]

To justify extension, on any compact subset of σ>0 the left series converges uniformly: if σ≥δ>0 and |s|≤A, its summands are bounded by \(A n^{-1-\delta}\). Thus its sum is holomorphic there. The right-hand side is holomorphic after removing its apparent pole at s=1; its value there is \((\log d)/d\). The identity theorem proves (5.10) on σ>0, with that removable interpretation at 1. For σ>1/2, (5.7) therefore gives

\[
\boxed{\Lambda_s(Cg_d)=(d^{-1}-d^{-s})\zeta(s).}
\tag{5.11}
\]

This calculation fixes the normalization directly; no factor 1/s is omitted.

## 6. The smoothed and sample-mean criteria

Let \(W=\overline{C(V)}^{J}\). If ζ(s)=0, σ>1/2 and s≠1, (5.11) implies \(\Lambda_s\vert_W=0\), but \(\Lambda_s(1)=1\). Hence 1∈W excludes every such zero. Reflection of nontrivial zeros then gives RH. Conversely, (NB), continuity of C and C1=1 give RH⇒1∈W. Thus

\[
\boxed{\mathrm{RH}\iff1\in W.}
\tag{6.1}
\]

The reverse implication from RH uses the cited classical theorem; the sufficient implication is proved by the explicit annihilator above.

At a hypothetical zero as above, for every legal F,

\[
1=|\Lambda_s(1-CF)|\le\sqrt{D_s}\|1-CF\|_J,
\]

so

\[
\|1-CF\|_J^2\ge D_s^{-1}
\ge[3|s(s+1)|^2\zeta(2\sigma)]^{-1}.
\tag{6.2}
\]

For a sequence F_j∈V put \(v_j=EV_{F_j}(T)<\infty\). Formula (3.5), integrated, says

\[
E|\overline{F_j}_{r_j}-1|^2=v_j/r_j+\|CF_j-1\|_J^2.
\tag{6.3}
\]

Both terms are nonnegative. Thus sample-mean approximation implies conditional-mean approximation. Conversely, if CF_j→1, choose

\[
r_j=\max\{j,\lceil jv_j\rceil\},\qquad j\ge1.
\]

Then r_j≥1, r_j→∞ and v_j/r_j≤1/j. Equation (6.3) gives sample-mean approximation on the same fixed probability space. Combining this with (6.1) proves the full conditional-iid criterion.

For the independent-row contrast one can choose an explicit legal function: g_2≥0 and \(Eg_2(K)\ge w_1g_2(1)=1/4>0\). Normalize g_2 by its expectation. Independent copies then have mean-square sample-average error equal to their variance divided by r, tending to zero. In the conditional-iid model the persistent term is instead \(\|CF-1\|_J^2\).

## 7. Exact heads and polynomial zero obstructions

If F(n)=1 for 1≤n≤Y, then CF(t)=1 for 1≤t≤Y. Conversely, those mean equalities imply the head equalities by (4.1). At a hypothetical zero from Section 6, absolute convergence and annihilation give the exact tail equation

\[
\sum_{t>Y}b_s(t)CF(t)=-B_s(Y).
\tag{7.1}
\]

The dual tail τ_s(Y) is positive: otherwise b_s(n)=0 eventually, hence a_s(n) is eventually constant; it tends to zero, so it is eventually zero. Then n^{-s} is eventually constant and tends to zero, contradicting n^{-s}≠0.

Cauchy–Schwarz applied only to the tail in (7.1) proves the strengthened bound

\[
\boxed{\|CF\|_J^2\ge Q_Y+\frac{|B_s(Y)|^2}{\tau_s(Y)}.}
\tag{7.2}
\]

Choose Y_s so \((1+|s|)(Y+1)^{-\sigma}\le1/2\) for Y≥Y_s. Using (5.4) gives

\[
\boxed{\|CF\|_J^2\ge Q_Y+
\frac{2\sigma-1}{12|s(s+1)|^2}Y^{2\sigma-1},\qquad Y\ge Y_s.}
\tag{7.3}
\]

This contains the handoff's lower bound and also retains the compulsory head energy.

Consequently, suppose Y_j→∞ and F_j∈V is exact on [1,Y_j]. If for every ε>0 there is C_ε>0 such that

\[
\|CF_j\|_J^2\le C_\epsilon Y_j^\epsilon
\quad\text{eventually,}
\tag{7.4}
\]

then RH holds. Indeed, a zero with p=2σ−1>0 contradicts (7.3) after choosing ε=p/2 and dividing by Y_j^{p/2}. More generally a bound O(Y_j^θ), θ≥0, excludes zeros with \(\sigma>(1+\theta)/2\).

### Bounded heads: a direct weak-convergence proof

There is a separate functional-analytic proof when \(\sup_j\|CF_j\|_J\le B\). Set M_j=CF_j. For any Z∈J and any fixed L, once Y_j≥L the first L coordinates of M_j−1 vanish. Hence

\[
|\langle M_j-1,Z\rangle_J|
\le(B+1)\|Z\mathbf1_{t>L}\|_J.
\]

First let j tend to infinity, then L tend to infinity. It follows that M_j converges weakly to 1. The norm-closed linear subspace W is weakly closed, so 1∈W and (6.1) gives RH. This proof does not invert C. For subpolynomial but unbounded energy, this boundedness argument is unavailable; the power-decaying Mellin dual tail supplies the needed arithmetic information.

## 8. Exact generator means

Let d≥2, t≥1, and write t=kd+r with 0≤r<d. A complete period of g_d over indices 1,…,d has sum (d−1)/2. The last r terms sum to r(r+1)/(2d). Therefore

\[
\boxed{Cg_d(t)=\frac1t\left[\frac{k(d-1)}2+
\frac{r(r+1)}{2d}\right].}
\tag{8.1}
\]

This also proves the uniform estimate

\[
0\le Cg_d(t)\le\frac12:
\]

indeed \(k(d-1)+r(r+1)/d\le kd+r=t\), since \(r(r+1-d)\le0\). All smoothed generator Gram entries are consequently finite.

## 9. Complete sieve and floor-repair obstructions

Let y≥2 be an integer, \(Q_y=\prod_{p\le y}p\), \(a_y(n)=\mathbf1_{\gcd(n,Q_y)=1}\), \(R_y(n)=\sum_{m\le n}a_y(m)\), and \(\alpha_y=\prod_{p\le y}(1-1/p)\).

Inclusion–exclusion gives

\[
R_y(n)=\sum_{d\mid Q_y}\mu(d)\lfloor n/d\rfloor,
\quad\alpha_y=\sum_{d\mid Q_y}\mu(d)/d,
\]

\[
F_y^0(n)=R_y(n)-\alpha_yn
=-\sum_{d\mid Q_y}\mu(d)g_d(n)\in V,
\tag{9.1}
\]

where g_1=0. For finite coefficients t_d with d>y and \(\sum_dt_d/d=-\alpha_y\),

\[
F_y(n)=R_y(n)+\sum_dt_d\lfloor n/d\rfloor
=F_y^0(n)-\sum_dt_dg_d(n)\in V.
\tag{9.2}
\]

If 1≤n≤y, every n≥2 has a prime factor at most y, so R_y(n)=1. Every added floor is zero there. Thus F_y has the required exact head.

For the uncorrected function, summing its head values gives

\[
CF_y^0(t)=1-\alpha_y(t+1)/2\quad(1\le t\le y).
\]

Therefore its finite head contribution alone is

\[
\sum_{t=1}^yq_t|CF_y^0(t)-1|^2
=\frac{\alpha_y^2}{2}\sum_{t=1}^y\frac{t+1}{t+2}
\ge\frac{\alpha_y^2y}{3}.
\tag{9.3}
\]

All omitted summands are nonnegative. Since F_y^0 is bounded, its full energy is finite, and (9.3) is also a valid lower bound for its J error norm.

### One-divisor repair, including the floor specialization

Let D be a positive integer, 8≤β≤D, and L=⌊β/4⌋. Suppose

\[
R(n)=1\quad(1\le n<D),\qquad
R(D+j)\le j+2\quad(0\le j\le L).
\]

Put \(\widetilde F(n)=R(n)-\beta\lfloor n/D\rfloor\). Because D≥8 and L≤β/4≤D/4<D, for every 0≤j≤L we have

\[
\left\lfloor\frac{D+j}{D}\right\rfloor=1,
\qquad
\widetilde F(D+j)\le j+2-\beta\le-\beta/2.
\tag{9.4}
\]

The last inequality uses j≤β/4 and β≥8. Before D, the error \(\widetilde F-1\) is zero. Thus

\[
C\widetilde F(D+j)-1
\le-\frac{(j+1)\beta}{2(D+j)}
\le-\frac{(j+1)\beta}{4D}.
\tag{9.5}
\]

For t=D+j, t+2≤D+D/4+2≤3D/2, since D≥8. In particular

\[
q_{D+j}=\frac2{(t+1)(t+2)}\ge\frac1{3D^2}.
\tag{9.6}
\]

Also \(L+1\ge\beta/4\), and

\[
\sum_{j=0}^L(j+1)^2\ge\int_0^{L+1}x^2dx=(L+1)^3/3.
\]

Squaring the negative bound (9.5), multiplying by (9.6), and summing proves the complete finite theorem

\[
\boxed{
\sum_{j=0}^Lq_{D+j}|C\widetilde F(D+j)-1|^2
\ge\frac{\beta^5}{9216D^4}.}
\tag{9.7}
\]

The finite statement needs no infinite summability. The same inequality holds for the full extended nonnegative series. If \(C\widetilde F\in J\), it is a lower bound for the ordinary squared J norm. We never assign a finite Hilbert norm to a divergent series.

For the sieve specialization take D=y+1 and β=α_yD. The condition R_y(D+j)≤j+2 follows from R_y(D−1)=1 and the fact that every increment is either zero or one. Moreover β≤D, and β≥8 eventually by the asymptotic below. The repaired function is legal by (9.2), hence bounded, so its energy is genuinely finite. Equation (9.7) becomes

\[
\|C\widetilde F-1\|_J^2\ge\alpha_y^5(y+1)/9216.
\tag{9.8}
\]

### The asymptotic input and its precise consequence

The published estimate \(\sum_{p\le y}p^{-1}=\log\log y+A+O(1/\log y)\) is [DLMF 27.11.8](https://dlmf.nist.gov/27.11#E8). Since \(\log(1-u)=-u+O(u^2)\) for 0≤u≤1/2 and \(\sum_pp^{-2}<\infty\),

\[
\log\alpha_y=-\log\log y+O(1),\qquad
\alpha_y\asymp1/\log y.
\]

Thus the lower bounds (9.3) and (9.8) diverge at least as constant multiples of \(y/(\log y)^2\) and \(y/(\log y)^5\), respectively. Their divergence also forces the corresponding uncentered norms to diverge, since \(\|CF\|_J\ge\|CF-1\|_J-1\). No RH assumption enters this specialization.

## 10. Exact finite interpolation and an unconditional energy bound

### 10.1 Every finite head can be prescribed legally

Fix Y≥1 and target values u_1,…,u_Y, with u_0=0. Let A=u_1. Define coefficients recursively for 2≤n≤Y by

\[
c_n=A-(u_n-u_{n-1})-
\sum_{\substack{d\mid n\\2\le d<n}}c_d,
\]

and then set

\[
c_{Y+1}=(Y+1)\left(A-\sum_{d=2}^Yc_d/d\right),
\qquad F=\sum_{d=2}^{Y+1}c_dg_d.
\tag{10.1}
\]

The normalization gives \(\sum c_d/d=A\). The generator difference formula implies ΔF(1)=u_1 and, for 2≤n≤Y,

\[
\Delta F(n)=A-\sum_{\substack{d\mid n\\d\ge2}}c_d
=u_n-u_{n-1}.
\]

Since F(0)=0, summation proves F(n)=u_n for n≤Y. This is a linear right inverse to finite head restriction.

A prescribed mean head h_1,…,h_Y is obtained by taking
\(u_n=nh_n-(n-1)h_{n-1}\), h_0=0. Denote the resulting map to CF by \(\mathcal R_Y:\mathbb R^Y\to C(V)\). It is linear and bounded, because its domain is finite dimensional and its output uses finitely many fixed J vectors. Its norm may depend arbitrarily badly on Y; no uniform estimate is being inferred.

### 10.2 A canonical exact-one head

Let \(m_Y=\sum_{d=1}^Y\mu(d)/d\), and define

\[
F_Y=-\sum_{d=2}^Y\mu(d)g_d+(Y+1)m_Yg_{Y+1}.
\tag{10.2}
\]

The coefficient normalization is 1. For 2≤n≤Y, the divisor identity \(\sum_{d\mid n}\mu(d)=0\) makes ΔF_Y(n)=0, whereas ΔF_Y(1)=1. Thus F_Y is exact on [1,Y].

We need a uniform elementary bound on m_Y. Counting divisors gives

\[
1=\sum_{d\le Y}\mu(d)\lfloor Y/d\rfloor,
\qquad
Ym_Y=1+\sum_{d\le Y}\mu(d)\{Y/d\}.
\]

The d=1 fractional part is zero, |μ(d)|≤1, and every fractional part is at most 1. Hence \(|Ym_Y|\le1+(Y-1)=Y\), so |m_Y|≤1. The total absolute coefficient sum in (10.2) is at most 2Y. Using (8.1),

\[
|CF_Y(t)|\le Y\quad\text{for every }t,
\qquad CF_Y(t)=1\quad(t\le Y).
\]

Consequently

\[
\boxed{\|CF_Y\|_J^2\le Q_Y+Y^2\sum_{t>Y}q_t
=\frac{Y(2Y+1)}{Y+2}<2Y.}
\tag{10.3}
\]

This constructs a legal exact head and an unconditional linear energy bound. It supplies no subpolynomial bound.

### 10.3 Constrained density and the exact variational criterion

Let \(W=\overline{C(V)}^J\). For any M∈W with M(t)=1 for t≤Y, choose M_k∈C(V) converging to M. Evaluation at each t is continuous, with norm q_t^{-1/2}. Therefore

\[
\widehat M_k=M_k+\mathcal R_Y((1-M_k(t))_{1\le t\le Y})
\]

converges to M and has exact mean head 1. By (4.1) it comes from a legal witness with exact ordinary head 1. Hence

\[
E_Y=\min\{\|M\|_J^2:M\in W,\ M(t)=1\ (t\le Y)\}.
\tag{10.4}
\]

The right minimum exists by projection onto a nonempty closed affine subset of a Hilbert space; nonemptiness follows from (10.2). Equality of the infimum and minimum follows from the constrained approximation just proved. The minimizer in W need not lie in C(V).

The constraints are nested, so E_Y is nondecreasing. Every feasible vector has head energy Q_Y, giving the lower bound E_Y≥Q_Y. Together with (10.3),

\[
Q_Y\le E_Y\le Y(2Y+1)/(Y+2)<2Y.
\tag{10.5}
\]

If sup_Y E_Y<∞, choose legal F_Y with energy at most E_Y+1. The bounded-head argument of Section 7 gives 1∈W and RH.

Conversely, under RH, (NB) gives \(\overline V^H=H\). Continuity of C implies \(C(H)\subseteq W\), and Section 4 proves C(H) dense in J. Hence W=J. In (10.4) the minimum is then attained by \(M=\mathbf1_{t\le Y}\), with value Q_Y. We have proved

\[
\boxed{
\mathrm{RH}\iff \sup_YE_Y<\infty
\iff E_Y=Q_Y\text{ for every }Y.}
\tag{10.6}
\]

The equality E_Y=Q_Y concerns an infimum over legal functions. It cannot be attained by a legal F: equality forces CF(t)=0 for t>Y, so (4.1) forces F to be the nonzero finite-support sequence with values 1 on [1,Y], −Y at Y+1, and 0 thereafter. A periodic sequence of finite support is zero, whereas every legal F is periodic.

Under RH, for any prescribed positive tolerances ε_Y one may therefore choose a legal exact head with \(\|CF_Y\|_J^2\le Q_Y+\epsilon_Y\). One may also obtain exact heads satisfying CF_Y→1 by applying the finite-head correction to successively sufficiently accurate approximations of 1. These are consequences of RH, not unconditional constructions with a useful energy estimate.

There is an explicit conversion from near-minimum energy to approximation error. For every exact head M=CF,

\[
\|M-1\|_J^2
\le\left(\sqrt{\|M\|_J^2-Q_Y}+\sqrt{1-Q_Y}\right)^2,
\tag{10.7}
\]

by applying the triangle inequality to the two tails. Under RH we can choose \(\|CF_Y\|_J^2<1\), since its infimum Q_Y is strictly less than 1. These witnesses satisfy

\[
\|CF_Y-1\|_J^2\le\frac8{Y+2}.
\tag{10.8}
\]

Choosing r_Y≥max{Y,⌈Y EV_{F_Y}(T)⌉} then gives sample-mean error at most \(1/Y+8/(Y+2)\) by (6.3). This is an existence-and-rate consequence of RH; there is still no unconditional construction meeting the energy threshold or controlling the required r_Y.

Monotonicity shows that bounded E_Y along any cofinal sequence is equivalent to uniform boundedness. More generally, (7.3) shows that a cofinal subpolynomial upper bound on E_Y implies RH, by choosing near-minimizing legal witnesses. Under RH the exact formula in (10.6) supplies such a bound. This completes both mathematical directions of the exact-head criteria, with (NB) as the explicit classical input.

## 11. The exact finite signed Gram and Schur-complement problem

Fix integers D≥Y+1. Use the generators g_2,…,g_D and write \(m_d=Cg_d\). Let m=D−1 and define

\[
A_{td}=m_d(t)\quad(1\le t\le Y,\ 2\le d\le D),
\]

\[
G_{de}=\sum_{t\ge1}q_tm_d(t)m_e(t),\qquad
T_{de}=\sum_{t>Y}q_tm_d(t)m_e(t).
\tag{11.1}
\]

All entries are absolutely convergent because 0≤m_d≤1/2. Every entry uses the actual shared-latent means; no independence approximation occurs. In particular

\[
G=A^{\mathsf T}\operatorname{diag}(q_1,\ldots,q_Y)A+T.
\tag{11.2}
\]

The finite interpolation theorem with Y=D−1 proves that g_2,…,g_D are linearly independent. Injectivity of C makes G positive definite. The same interpolation theorem with the given Y proves A has full row rank.

T is positive definite too. If c^TTc=0, then CF(t)=0 for all t>Y, where \(F=\sum c_dg_d\). Formula (4.1) makes F zero for all n>Y+1. Periodicity forces F=0 everywhere, and independence forces c=0.

Define the finite minimum

\[
E_{Y,D}=\min_{Ac=\mathbf1_Y}c^{\mathsf T}Gc.
\]

The minimizer exists and is unique. Lagrange multipliers, or completing the quadratic square, give

\[
c_*=G^{-1}A^{\mathsf T}(AG^{-1}A^{\mathsf T})^{-1}\mathbf1_Y,
\]

\[
\boxed{E_{Y,D}=\mathbf1_Y^{\mathsf T}
(AG^{-1}A^{\mathsf T})^{-1}\mathbf1_Y.}
\tag{11.3}
\]

For example, if Ac=1 and z=c−c_*, then Az=0, and
\(z^TGc_*=z^TA^T\lambda=0\). Hence
\(c^TGc=c_*^TGc_*+z^TGz\), proving the minimum without dropping a mixed term.

On the constraint Ac=1, (11.2) gives c^TGc=Q_Y+c^TTc. Repeating the same argument with T proves the useful tail form

\[
\boxed{E_{Y,D}=Q_Y+\mathbf1_Y^{\mathsf T}
(AT^{-1}A^{\mathsf T})^{-1}\mathbf1_Y>Q_Y.}
\tag{11.4}
\]

Because every legal function uses finitely many generators,

\[
E_Y=\inf_{D\ge Y+1}E_{Y,D}=\lim_{D\to\infty}E_{Y,D}.
\tag{11.5}
\]

The limit exists by monotonicity in D. The strict finite inequality in (11.4) is compatible with the RH-conditional infimum Q_Y.

### Corrections and the complete Schur complement

Choose any feasible c_0, for instance (10.2) padded with zeros. Let the columns of N form a basis of ker A. Every legal correction preserving the head is c=c_0+Nz. Put

\[
S=N^{\mathsf T}TN,\qquad h=N^{\mathsf T}Tc_0.
\]

When ker A is nonzero, S is positive definite, and direct expansion gives

\[
c^{\mathsf T}Tc=c_0^{\mathsf T}Tc_0+2z^{\mathsf T}h+z^{\mathsf T}Sz.
\]

Completing the square, with z_*=-S^{-1}h, yields

\[
\boxed{E_{Y,D}=Q_Y+c_0^{\mathsf T}Tc_0-h^{\mathsf T}S^{-1}h.}
\tag{11.6}
\]

If ker A={0}, the last term is zero and no inverse of an empty matrix is needed. A redundant correction list would instead require a pseudoinverse and its range condition; choosing a basis avoids that additional obligation.

Equation (11.6) retains every signed covariance and cross term. Although the generator Gram entries are nonnegative, entries of S and h after signed corrections can have either sign.

The outstanding arithmetic estimate can now be stated with all quantifiers:

\[
\boxed{\exists K<\infty\ \forall Y\ge1\ \exists D\ge Y+1:
c_0^{\mathsf T}Tc_0-h^{\mathsf T}S^{-1}h\le K.}
\tag{11.7}
\]

This is equivalent to sup_Y E_Y<∞ and therefore to RH. Equivalently, the coupled directions must recover at least \(c_0^TTc_0-K\) of the initial tail energy through their actual correlations. Positive definiteness alone supplies no such estimate. A cofinal subpolynomial bound for the same remainder would also imply RH by Section 7.

No bound on how large D must be, on the coefficient sizes, or on a fixed conductor budget is established by these equivalences.

## 12. Signed replica geometry and randomized coefficients

For real directions w_1,…,w_m∈H define

\[
G^H_{ij}=\langle w_i,w_j\rangle_H,\quad
G^{\rm cm}_{ij}=\langle Cw_i,Cw_j\rangle_J,
\]

\[
G^{\rm within}_{ij}=\tfrac12E[(w_i(K_1)-w_i(K_2))
(w_j(K_1)-w_j(K_2))].
\]

Equation (3.9) proves \(G^H=G^{\rm cm}+G^{\rm within}\). Each component is positive semidefinite: its quadratic form is respectively a squared J norm or half the expected square of a replica difference. Its individual off-diagonal entries need not be nonnegative. Applying (3.9) with a residual e and each w_i also decomposes the actual residual-correlation vector.

For deterministic coefficients c, with h_i=⟨Ce,Cw_i⟩_J,

\[
\left\|C\left(e-\sum_ic_iw_i\right)\right\|_J^2
=\|Ce\|_J^2-2c^{\mathsf T}h+c^{\mathsf T}G^{\rm cm}c.
\tag{12.1}
\]

Let A be any random vector in ℝ^m with E|A|²<∞, on a separate probability space, and let B:ℝ^m→H be the finite linear map with columns w_i. Set a=EA and Z=B(A−a). Then Z is square integrable, EZ=0, and expansion followed by integration gives

\[
E\|e-BA\|_H^2=\|e-Ba\|_H^2+E\|B(A-a)\|_H^2.
\tag{12.2}
\]

The cross term is integrable by Cauchy–Schwarz and has expectation zero. Applying the same proof to CB gives the corresponding identity in J. Linear constraints imposed almost surely on A are inherited by a. Thus randomizing coefficients in one fixed finite correction space cannot improve expected squared loss below its deterministic minimum.

## 13. What is complete and what remains

The probability construction, conditional laws, integrability, moment identities, operator identities, Mellin dual estimates and normalization, smoothed/sample-mean equivalences, exact-head implications, finite interpolation, floor specialization, sieve obstructions, and signed finite minimization formulas have mathematical proofs above. The reverse classical RH implication uses (NB) as an identified theorem. The sieve growth conclusions use the identified prime-reciprocal estimate.

Two levels must remain distinct:

1. **Mathematical formalization:** the preceding definitions, hypotheses and proofs supply the missing ordinary-mathematics steps and sharpen the variational target.
2. **Machine verification:** none of this new completion was run through Lean. The earlier repository coverage audit remains incomplete; filenames alone do not certify which proofs are already there.

The unresolved research assertion is (11.7), or its cofinal subpolynomial replacement. The explicit construction in Section 10 gives only an O(Y) energy bound. A proof of the required uniform or subpolynomial signed remainder would imply RH; it is not supplied here.

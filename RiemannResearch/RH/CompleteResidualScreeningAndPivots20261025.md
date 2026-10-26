# Complete residual screening and exact squarefree evaluation pivots

25 October 2026. Continuation of the user-provided ordered-basis / signed-head-prediction handoff, baseline `3eaebc6790607d36c684a41a460e8debfb1ff34f`.

**RH is not proved. The actual uniform arithmetic provider remains Open.**

This report separates the Lean development below from the ordinary mathematical investigations in its later sections. The final checkpoint record is supplied in the accompanying conversation; a successful ephemeral snippet alone is not publication validation.

## Lean development

Use the incoming notation: physical measure Q(n)=1/(zeta(2)n^2), actual squarefree stages V_N with conductors through N+1, residual r_N=1-P_N1, error epsilon_N=||r_N||², and correction b_N=P_N B r_N, where Bf(n)=f(n)/(n+1). Complete infinite Hilbert norms are retained throughout.

### Complete gain and its omitted tail

`RH/QResidualScreeningSeries.lean` proves summability of

$$\delta_k\,\frac{\langle T_kBr,T_kr\rangle^2}{\|T_kr\|^2},\qquad
\delta_0=4,\quad\delta_k=2k+3\ (k>0).$$

Zero denominators use totalized division and contribute zero. The module defines the complete sum Gamma_infinity and proves

$$0\le\Gamma_\infty(r)-\Gamma_M(r)\le\|T_Mr\|^2.$$

Central declarations are `weightedResidualLayerGain_summable`, `completeResidualGain_eq_finite_add_tail`, `completeResidualGain_sub_finite_nonneg`, and `completeResidualGain_sub_finite_le_tail`. No arithmetic decay rate or RH hypothesis is used.

### Exact finite remainder and layer slack

The same module proves, for M>0, the coordinate formula

$$R_M(r)=\sum_{j\ge M}\left(1-\frac{(M+1)^2}{(j+2)^2}\right)|r_j^{\rm Lean}|^2.$$

For zero-based onsets s_i<M (in particular M>=N+1 for the actual stage), it proves the full identity

$$W+\Gamma_M+\sum_{k<M}\delta_k E_k+R_M=\|r\|^2,$$

where s_i denotes the zero-based onset, its physical onset is s_i+1, and

$$E_k=\|T_kBr\|^2-\frac{\langle T_kBr,T_kr\rangle^2}{\|T_kr\|^2}
-\sum_{i:\,k\le s_i}\langle Br,u_i\rangle^2.$$

`reciprocalLayerRemainder_eq_tsum` gives the coordinate formula; `residual_screening_full_identity` gives the equality; `residualLayerSlack_nonneg` supplies nonnegativity under the stated orthogonality, onset, norm, and residual-orthogonality hypotheses. The equality itself is algebraic and does not silently assume these hypotheses.

### Actual-stage assembly and cutoff selection

`RH/QSquarefreeEvaluationBasis.lean` specializes these identities to the actual ordered evaluation basis. Its new declarations include:

- `movingCorrection_screening_full_identity` and `movingCorrection_layerSlack_nonneg`;
- `completeScreeningGain`, `residualScreeningGain_tendsto`;
- `movingCorrection_weighted_coefficients_complete_screened`;
- `movingCorrection_sq_le_complete_screened_diagonal`;
- `exists_screening_cutoff`.

In particular,

$$|b_N(n)|^2\le W_ND_N(n)
\le(\varepsilon_N-\Gamma_{N,\infty})D_N(n).$$

For every N,n,L and eta>0, `exists_screening_cutoff` gives an M>=max(N+1,L) such that

$$ (\varepsilon_N-\Gamma_{N,M})D_N(n)
\le (\varepsilon_N-\Gamma_{N,\infty})D_N(n)+\eta.$$

Thus cutoff selection is settled once a common bound for the complete product is available. Taking eta=1 enlarges a squared bound C² to at most C²+1, or to (C+1)² when C>=0. This is not a provider of that common bound.

### Exact arithmetic pivot classification

`RH/QSquarefreeHeadBoundary.lean` proves that, for N>0, the first N physical values already determine a stage-N vector (`stage_eq_zero_of_head_zero`), sharpening the previous N+1-site injectivity argument. It also provides `stage_le_of_active_cutoff`.

`RH/QSquarefreeResponseBasis.lean` proves existence of a largest active conductor at every nonempty stage and the exact classification `orderedVector_ne_zero_iff`. If D is the largest squarefree conductor at most N+1, then

$$u_{N,i}\ne0\quad\Longleftrightarrow\quad
\operatorname{Squarefree}(i+1)\ \text{and}\ i+1<D.$$

This includes physical site 1. The zero stage is treated separately. Interior witnesses are m*g_m-D*g_D, with onset m and value -m there. The finite boundary charge forces the last possible pivot to vanish. No numerical rank computation or invertible masked Gram matrix is assumed.

The classification supplies exact support restrictions for all basis sums. It does not bound the physical sizes of the surviving vectors.

## Remaining research obligations

The primary target is still an unconditional common C>=0 with

$$\forall N,n,\quad1\le n\le N\Longrightarrow
(\varepsilon_N-\Gamma_{N,\infty})D_N(n)\le C^2.$$

The sharper actual-coefficient target W_N D_N(n)<=C² and the direct actual signed-response bound remain open. A1 and A3 therefore remain unresolved; A2's complete-gain and cutoff components are implemented, and A4's exact classification is established without claiming its missing quantitative consequence. The inherited KPS/KF, odd-radical, scaled-tail, and measure-change providers retain their earlier open status. No unconditional declaration of type `RiemannHypothesis` was obtained.

For H comparable with n, ordinary evaluation-vector Bessel bounds already control the high-onset diagonal block by zeta(2)*n²/(H+2)². The unresolved part is transport of the low-onset coordinates to larger physical sites, jointly with the actual signed coefficients. The exact arbitrary-data amplification example below prevents replacing this problem by an assumed row-sum contraction.

The later variance identities and strict finite-stage surviving-budget bound are ordinary proofs recorded for future work; they are not separately formalized by this publication. In particular, the complete-gain tail bound must not be misreported as a bound on the surviving budget.

## Ordinary mathematical investigation


# Arithmetic review of signed head prediction and complete residual screening

Date: 25 October 2026.

**Status:** Ordinary mathematical arguments, with one independently checked exact rational computation. The arguments in this section were not separately formalized in this continuation. A rational Python check is not a Lean certificate. The uniform actual-response bound remains open, and RH is not proved.

Throughout, physical sites are positive integers, \(Z=\zeta(2)\), \(Q(n)=1/(Zn^2)\), \(g_d(n)=(n\bmod d)/d\), and \(Bf(n)=f(n)/(n+1)\). All Hilbert norms and inner products use the complete infinite measure Q.

## 1. Exact obstruction to arbitrary-data sup-norm contraction

The handoff reports a numerical prediction-row norm greater than one at \(N=4,H=2,n=4\). The following gives an exact proof for this actual squarefree stage. It does **not** give a counterexample to the requested bound on the actual correction \(b_N\).

### 1.1 The head extension and its Gram equations

At \(N=4\), the active conductors are 2, 3, and 5. Write

\[
a=g_2,\qquad b=g_3,\qquad c=g_5,\qquad v=3b-5c.
\]

For \(f=ua+wb+zc\),

\[
f(1)=u/2+w/3+z/5,\qquad f(2)=2w/3+2z/5.
\]

Consequently, \(f(1)=f(2)=0\) if and only if \(u=0\) and \(w=-3z/5\). Thus the actual tail-stage subspace is

\[
\mathcal C_{4,2}=\operatorname{span}\{v\}.
\]

In particular, \(v(1)=v(2)=0\), \(v(3)=-3\), and \(v(4)=-3\), so \(V:=\|v\|_Q^2>0\).

Given arbitrary real head data \((x,y)\), set

\[
F_{x,y}=(2x-y)a+\frac{3y}{2}b,
\qquad
h_{x,y}=F_{x,y}-\frac{\langle F_{x,y},v\rangle_Q}{V}v.
\]

Then \(h_{x,y}\) belongs to the actual stage, has head values \(h_{x,y}(1)=x\), \(h_{x,y}(2)=y\), and satisfies \(\langle h_{x,y},v\rangle_Q=0\). Every stage extension of the same head differs by a multiple of v. Pythagoras therefore proves that \(h_{x,y}\) is the unique minimum-norm complete legal extension of that head.

Put \(A=\langle a,v\rangle_Q\) and \(B_0=\langle b,v\rangle_Q\), where the subscript distinguishes this scalar from the multiplication operator B. Since \(F_{x,y}(4)=y/2\), direct evaluation gives

\[
h_{x,y}(4)=\beta_1x+\beta_2y,
\qquad
\beta_1=\frac{6A}{V},
\qquad
\beta_2=\frac12-\frac{3A}{V}+\frac{9B_0}{2V}.
\]

These are the coefficients of the actual head-prediction operator. To make the connection with the normal equations explicit, let \(k_j=P_4e_j\) and \(L=\operatorname{span}\{k_1,k_2\}\). The above minimum-norm extension is \(P_Lf\) for any stage f with head \((x,y)\). Hence

\[
P_Le_4=\beta_1k_1+\beta_2k_2,
\qquad
\sum_{m=1}^2\langle k_j,k_m\rangle_Q\beta_m
=\langle k_j,k_4\rangle_Q\quad(j=1,2).
\]

The two head evaluation functionals are independent: the displayed \(F_{x,y}\) realizes every pair \((x,y)\). Thus the two predictor coefficients are uniquely determined here; no pseudoinverse choice is involved.

### 1.2 A rational certificate for amplification

Define

\[
\Delta=-18A+9B_0-V.
\]

Then

\[
-\beta_1+\beta_2-1=\frac{\Delta}{2V}.
\]

Using \(v=3b-5c\),

\[
\Delta
=\langle v,-18a+6b+5c\rangle_Q
=\frac1Z\sum_{n\ge1}\frac{q(n)}{n^2},
\]

where the integer-valued, 30-periodic function is

\[
q(n)=\big((n\bmod3)-(n\bmod5)\big)
\big(-9(n\bmod2)+2(n\bmod3)+(n\bmod5)\big).
\]

Its values at sites 1 through 30 are

```text
0, 0, 18, -18, -10, -1, 5, -7, 20, 2,
-4, -4, 8, -16, 0, 0, 0, -9, 9, 8,
8, -4, 2, -16, -7, 5, 14, -10, 2, 0.
```

In particular, \(q(n)\ge-18\) for every n. Exact rational arithmetic gives

\[
\sum_{n=1}^{30}\frac{q(n)}{n^2}
=\frac{415447910698667671751}{670372984619858520000}
=\frac35+
\underbrace{\frac{13224119926752559751}{670372984619858520000}}_{\eta>0}.
\]

The elementary decreasing-integrand bound gives

\[
\sum_{n>30}\frac{q(n)}{n^2}
\ge-18\sum_{n>30}\frac1{n^2}
\ge-18\int_{30}^{\infty}\frac{dx}{x^2}
=-\frac35.
\]

All series above are absolutely convergent because q is bounded. Therefore

\[
\Delta\ge\frac\eta Z>0,
\qquad
|\beta_1|+|\beta_2|
\ge-\beta_1+\beta_2>1.
\]

Equivalently, the exact head data \((x,y)=(-1,1)\) have sup norm one, while their minimum-norm legal extension satisfies \(h_{-1,1}(4)>1\). This disproves an arbitrary-data contraction claim for the actual head-prediction operator. It does not rule out a smaller signed action on the special head values of \(b_N=P_NBr_N\).

### 1.3 Reproducible exact computation

The following Python check was run locally and all assertions passed. It uses only integer and rational arithmetic.

```python
from fractions import Fraction

q = []
for n in range(1, 31):
    r2, r3, r5 = n % 2, n % 3, n % 5
    q.append((r3 - r5) * (-9*r2 + 2*r3 + r5))

assert q == [0, 0, 18, -18, -10, -1, 5, -7, 20, 2,
             -4, -4, 8, -16, 0, 0, 0, -9, 9, 8,
             8, -4, 2, -16, -7, 5, 14, -10, 2, 0]
assert min(q) == -18
s = sum((Fraction(q[n-1], n*n) for n in range(1, 31)), Fraction())
assert s == Fraction(415447910698667671751, 670372984619858520000)
margin = s - Fraction(3, 5)
assert margin == Fraction(13224119926752559751, 670372984619858520000)
assert margin > 0
```

## 2. Complete screening leaves a residual-energy dispersion functional

This argument concerns an arbitrary real physical \(r\in\ell^2(Q)\). Put

\[
a_n=Q(n)|r(n)|^2,\qquad
\lambda_n=\frac1{n+1},\qquad
T_k=\sum_{n>k}a_n,\quad
C_k=\sum_{n>k}a_n\lambda_n,\quad
E_k=\sum_{n>k}a_n\lambda_n^2.
\]

Let \(\delta_0=4\), \(\delta_k=2k+3\) for \(k\ge1\), and use zero for \(C_k^2/T_k\) when \(T_k=0\). Set

\[
\Gamma_\infty(r)=\sum_{k\ge0}\delta_k\frac{C_k^2}{T_k}.
\]

The cumulative identity

\[
\sum_{k=0}^{n-1}\delta_k=(n+1)^2
\]

and Tonelli imply \(\sum_k\delta_kE_k=\sum_na_n=\|r\|_Q^2\). Cauchy-Schwarz gives \(0\le C_k^2/T_k\le E_k\), so the gain is summable and

\[
S(r):=\|r\|_Q^2-\Gamma_\infty(r)
=\sum_{k\ge0}\delta_k\left(E_k-\frac{C_k^2}{T_k}\right).
\]

For positive \(T_k\), the quantity in parentheses is \(T_k\) times the variance of \(\lambda_n\) under the tail distribution \(a_n/T_k\). It also has the exact pairwise form

\[
E_k-\frac{C_k^2}{T_k}
=\frac1{T_k}\sum_{k<n<m}a_na_m(\lambda_n-\lambda_m)^2.
\]

If \(T_k=0\), both sides are zero with the stated convention. A second Tonelli rearrangement yields

\[
\boxed{
S(r)=\sum_{n<m}a_na_m(\lambda_n-\lambda_m)^2
\sum_{k=0}^{n-1}\frac{\delta_k}{T_k}.
}
\]

Whenever \(a_na_m>0\), all denominators in its inner sum are positive. Thus totalized division introduces no ambiguity into a nonzero summand.

### 2.1 The unscreened budget cannot vanish for a nonzero annihilator

Keeping only the k=0 term proves

\[
S(r)\ge4\left(\|Br\|_Q^2-
\frac{\langle Br,r\rangle_Q^2}{\|r\|_Q^2}\right).
\]

Suppose r is nonzero and \(S(r)=0\). Equality in Cauchy-Schwarz forces \(Br=tr\) for a scalar t. Since \(\lambda_n=(n+1)^{-1}\) takes distinct values at distinct sites, r has support at a single physical site.

If, additionally, \(r\perp g_d\) for every squarefree conductor \(d\ge2\), one-site support is impossible. For its support site n, choose a prime \(p>n\); then \(g_p(n)=n/p>0\), and \(\langle r,g_p\rangle_Q=Q(n)r(n)n/p\ne0\). Therefore

\[
r\in V^\perp\quad\Longrightarrow\quad
\boxed{S(r)=0\iff r=0.}
\]

This is a statement about the surviving budget itself. It does not imply that \(S(r_N)D_N(n)\) is bounded.

### 2.2 Strong-limit compatibility

For \(M\ge1\), Cauchy-Schwarz and the cumulative weights give

\[
0\le\Gamma_\infty(r)-\Gamma_M(r)
\le\sum_{k\ge M}\delta_kE_k
=\sum_{n>M}a_n\left(1-\frac{(M+1)^2}{(n+1)^2}\right)
\le\|\mathsf T_Mr\|_Q^2.
\]

The same final inequality also holds for \(M=0\), using the complete energy identity directly.

Each finite partial gain is continuous in r. Away from \(T_k=0\) this follows from the quotient formula; at \(T_k=0\), use \(C_k^2/T_k\le\|\mathsf T_kBr\|_Q^2\) and boundedness of B. If \(r_j\to r\) strongly, their tails are uniformly tight. The omitted-gain bound therefore upgrades finite-partial continuity to

\[
\Gamma_\infty(r_j)\longrightarrow\Gamma_\infty(r),
\qquad S(r_j)\longrightarrow S(r).
\]

For the actual residuals \(r_N\to r=P_{V^\perp}1\), this proves that a nonzero limiting residual would retain a strictly positive limiting complete surviving budget. Increasing M alone cannot remove that budget. The sought product estimate may still hold only through genuine control of the actual diagonal and residual together.

## 3. Precise outstanding arithmetic obligation

No unconditional constant was established for

\[
\sup_{N\ge1,\ 1\le n\le N}W_ND_N(n),
\quad
\sup_{N\ge1,\ 1\le n\le N}S(r_N)D_N(n),
\quad\text{or}\quad
\sup_{N\ge1,\ 1\le n\le N}|b_N(n)|.
\]

Likewise, no bound was obtained for the signed actual head action
\(\sum_{m\le\lfloor n/2\rfloor}\beta_m b_N(m)\). The exact amplification example explains why an arbitrary-data row contraction cannot supply this bound. The variance identity explains why infinite screening alone does not supply it. An estimate must still exploit the specific residual, actual normal equations, and arithmetic stage structure jointly.


# Strictly positive surviving screening budget at each finite squarefree stage

Status: ordinary mathematical argument. The algebraic two-point inequality and the application below have **not** been separately verified in Lean. This does not supply a uniform arithmetic product provider.

Use physical sites n >= 1, Z = zeta(2), Q(n) = 1/(Z n^2), and Bf(n) = f(n)/(n+1). For any complete-Q vector f, let epsilon = ||f||_Q^2, and let Gamma_infinity be the complete residual screening gain from the handoff. The complete layer-energy identity gives

\[
\epsilon-\Gamma_\infty
=\sum_{k\ge0}\delta_k\left[
 \|\mathsf T_k Bf\|_Q^2
 -\frac{\langle\mathsf T_k Bf,\mathsf T_k f\rangle_Q^2}
 {\|\mathsf T_k f\|_Q^2}\right].
\]

All summands are nonnegative. For nonzero f, put

\[
\lambda=\frac{\langle Bf,f\rangle_Q}{\epsilon}.
\]

The k=0 summand, with delta_0=4, is 4||Bf-lambda f||_Q^2. Consequently, for two distinct sites a,b, set x=Q(a)|f(a)|^2 and y=Q(b)|f(b)|^2. If x+y>0, the elementary identity

\[
x(A-\lambda)^2+y(B-\lambda)^2
=\frac{xy}{x+y}(A-B)^2
 +(x+y)\left(\lambda-\frac{xA+yB}{x+y}\right)^2
\]

with A=1/(a+1) and B=1/(b+1) proves

\[
\epsilon-\Gamma_\infty
\ge\frac{4xy}{x+y}
\left(\frac1{a+1}-\frac1{b+1}\right)^2.
\]

Now let f=r_N=1-P_N1 be the actual finite squarefree-stage residual. Choose any positive common multiple L of every active conductor in stage N. For the zero stage, L=1 is permitted. Every legal stage function vanishes at both L and 2L because every atom g_d does. Hence

\[
r_N(L)=r_N(2L)=1,
\qquad x=\frac1{ZL^2},\quad y=\frac1{4ZL^2}.
\]

The two-point bound simplifies exactly to

\[
\boxed{
\epsilon_N-\Gamma_{N,\infty}
\ge\frac{4}{5Z(L+1)^2(2L+1)^2}>0.
}
\]

This is stronger than the also-valid pairwise-variance bound

\[
\epsilon_N-\Gamma_{N,\infty}
\ge\frac{1}{Z^2L^2(L+1)^2(2L+1)^2\epsilon_N},
\]

because epsilon_N >= x+y = 5/(4ZL^2).

Thus no finite stage exhausts its residual energy merely by taking the screening cutoff M to infinity. The lower bound depends on the stage period and may tend to zero rapidly as N grows. It neither contradicts RH nor rules out SP or WP. It prevents the unsupported inference Gamma_N,infinity=epsilon_N at a fixed finite stage.


## Verification record before final checkpoint

Combined candidate `job_rtpIlSxx_7-KtAzsJuP8CTlLvHdI0oyz` succeeded, exit 0, verified=true, server-reported worker duration 40.774 seconds. Central complete-tail, exact-remainder, actual-product, and pivot-classification declarations printed only propext, Classical.choice, and Quot.sound. The candidate is subsequently placed in owning modules and rechecked before the final publication checkpoint. Workspace-opening round-trip and queue/polling delays were not separately measured; they are not kernel-check timings. The final successful checkpoint and published commit must be reported separately.

Persisted-module verification `job_d20ZHcYjb07P4UcD-vD0jr2fLy9uywMI` subsequently succeeded, exit 0, verified=true, server-reported worker duration 137.192 seconds. It rebuilt the four changed/new child modules and checked the saved declarations. All eight audited central declarations used only propext, Classical.choice, and Quot.sound. Exact printed types confirmed arbitrary positive cutoff tolerance, the largest-active-conductor pivot equivalence, and the N-site injectivity statement. The publication checkpoint remains a separate acceptance gate.

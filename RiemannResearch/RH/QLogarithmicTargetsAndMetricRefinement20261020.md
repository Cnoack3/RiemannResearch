# Complete-Q metric refinement and actual logarithmic-head targets

20 October 2026 UTC. Continuation of the user-provided
`RH_CRT_Lean_Continuation_Agenda_2026-10-20(1).md`, based on published
commit `75271daadaab4e33d7bf3c124be2713e3ac333a8`.

## Scope and remaining goal

Let Q(n)=1/(zeta(2)n²) on positive integers, let H be the closed span of
**all** squarefree residue atoms g_d(n)=(n mod d)/d, and put
D=||1-P_H 1||_Q². The objective remains D=0, or equivalently 1 in H.
This continuation does not prove that assertion or unconditional RH.

The results below preserve complete tails, signed cross terms, and exact
norm-square remainders. They are submitted for server checkpoint validation;
publication is conditional on that checkpoint's successful final-source check.
The final server job and published commit are reported by the checkpoint.
No GitHub Actions verification is used.

The final module-boundary check imported all ten new Lean modules and
completed successfully in server job
`job_xg2SXYEeJBOesi0qcq5oCVUENFmCIhie`. Eleven representative theorem
axiom audits reported only `propext`, `Classical.choice`, and `Quot.sound`;
these include the gap estimate, exact budget, target Mellin formula,
conditional RH consumers, and uniform-loss sieve bound. This audit does not
discharge any explicit energy-bound or closure-membership hypothesis.


Publication recovery: checkpoint `job_wGbTTiP83QIS1SyaQw914gr1xeVIEJ0J`
completed compilation but could not publish because newer main changed the
shared import list and catalog. The verified local commit was preserved as
`964c89206fa96fbc5fc75eda97ddfa5074dc5104`. The same theorem sources were
transferred onto main commit `1a1335b5e30a65b6ec37b4259bb513be3abfe2dd`,
preserving its new coefficient-limit, Dirichlet-tail, and signed-closure
results. A new server checkpoint validates this reconciled source before
publication; the earlier failed publication is not treated as final acceptance.

## 1. A coefficient-independent rational-weight estimate

Write w_L(a)=sum_{j>=0}Q(a+jL),
u_L(a)=1/a²+2/[L(2a+L)], and
Gap_L(f)=sum_{a=1}^L [u_L(a)-zeta(2)w_L(a)](1-f(a))².
The first positive midpoint defect gives, for 1<=a<=L,

    1/(60L²) <= u_L(a)-zeta(2)w_L(a) <= 2/L².

The complete weight gap retains at least

    L² / ((a+L)²(4(a+L)²-L²)).

For every L-periodic sequence f and positive integer k, exact replication
of the unweighted residue block now yields

    Gap_(kL)(f) <= (120/k) Gap_L(f).

This is uniform over the coefficients of f. It applies to moving vectors;
it does not require the fixed pointwise bound used by the previous 2B²/L
estimate. Factors at least 120 give monotonicity; factors at least 240
give Gap_(kL)(f)<=Gap_L(f)/2.

Owner: `QRationalPeriodRefinement.lean`, particularly
`midpointDefect_le_weight_gap`, `weight_gap_lower`, `rationalGap_mul_le`,
and `rationalGap_mul_le_half`.

## 2. Actual rational minima: exact cross-stage accounting

Use the actual normal-equation minimizers f_n at exhaustive primorial
periods L_n and R_n=E_(L_n)(f_n). For n<=m define

    Disp(n,m)=sum_{a=1}^{L_m} u_(L_m)(a)(f_n(a)-f_m(a))².

Completion of the square and the exact weight-gap identity give

    R_n-R_m = Gap_(L_n)(f_n)-Gap_(L_m)(f_n)+Disp(n,m).

If L_m=kL_n with k>=240, then

    Gap_(L_n)(f_n)/2 + Disp(n,m) <= R_n-R_m.

For any increasing stage chain satisfying these ratio conditions,

    sum_{j<N} [Gap_(L_j)(f_j)/2 + Disp(j,j+1)] <= R_0-R_N <= R_0.

The exact cumulative formula retains R_N and the signed metric refunds.
The already proved limit is R_N -> zeta(2)D along cofinal chains; the
finite budget does not make D vanish.

Disp is the improvement from reoptimizing in the later **rational metric**.
It can include reoptimization within the old span caused by changing the
metric. It is not the complete-Q projection gain D_n-D_m.

Owner: `QRationalStageGain.lean`, including
`rationalMinimum_drop_exact`,
`rationalMinimum_drop_ge_half_gap_add_displacement`, and
`rationalMinimum_chain_exact` / `rationalMinimum_chain_budget`.

## 3. Exact legal capture of parity leakage

For projection spaces V<=W containing g_2, put p_V=P_V1,
D_V=||1-p_V||² and a_V=1-4D_V. Let C_2 be actual complete-Q parity
projection. The earlier parity formula now gives

    C_2 p_V = a_V 1 + 8D_V g_2,
    (I-P_W) C_2 p_V = a_V(1-P_W1),
    ||P_W C_2p_V-P_V C_2p_V||² = a_V²(D_V-D_W).

Moreover the old space captures exactly

    ||P_V(p_V-C_2p_V)||² = 4D_V²(1-4D_V).

That last energy is already in V; it must not be counted as an innovation
from new conductors. The earlier leakage magnitude D_V(1-4D_V) therefore
does not itself provide a lower bound on new legal gain.

Owner: `QParityLegalGain.lean`.

## 4. Exact two-stage legal heads and their full cost

Let A_x be the published gcd-two primorial sieve, and let a_x be the
finite Euler product through x. Whenever a_x!=a_y, set

    T_(x,y) = (a_x A_y-a_y A_x)/(a_x-a_y).

For 2<=x<=y, this is a finite squarefree legal vector and
T_(x,y)(n)=floor(log_2 n) for every n<=x. Its exact signed Gram formula is

    ||T||² = [a_x²||A_y||²+a_y²||A_x||²
              -2a_x a_y <A_y,A_x>]/(a_x-a_y)².

Equivalently,

    ||T||² = [a_x||A_y||²-a_y||A_x||²]/(a_x-a_y)
              +a_x a_y ||A_y-A_x||²/(a_x-a_y)².

The positive displacement term cannot be dropped. For each fixed x,
the corrected family still has ||T_(x,y)|| -> infinity as y -> infinity,
while its physical coordinates tend to floor(log_2 n). In particular,
finite exact fitting alone does not supply norm control.

Every finite logarithmic head has an actual finite squarefree interpolant;
the nonzero-denominator condition is attained using the proved decay a_y->0.

Owner: `QPrimePowerTwoStage.lean`.

## 5. Actual constrained optimization, not just a feasible seed

The general same-head extension of `QResidueHeadSpace.lean` identifies
the full affine feasible set for any attainable head. Applied to T_(x,y),
it defines U_(x,y), the actual complete-Q minimum-norm logarithmic-head
vector, retaining every divisor of the squarefree period. The chosen anchor
is merely a coordinate for the full compensated-direction space.

For every feasible f in that full dictionary,

    ||f||² = ||U_(x,y)||² + ||f-U_(x,y)||².

The inverse-Gram formula records the exact energy removed from T. At a
fixed head x and nested periods y<=z,

    ||U_(x,y)||² = ||U_(x,z)||² + ||U_(x,y)-U_(x,z)||².

Thus fixed-head minima decrease under enlargement even though the explicit
two-stage seeds diverge. Seed divergence is not a divergence theorem for
the constrained minima.

Owners: `QResidueHeadSpace.lean` and `QPrimePowerConstrainedHead.lean`.
The bounded-target-head lemma in `QExactHeadAverages.lean` proves that
uniformly bounded legal exact heads converge weakly to the specified
actual Q target, which therefore belongs to the closed legal span.

The application `QPrimePowerInterpolationClosure.lean` keeps flexible
period choices and also supplies a selected feasible family. Its selected
cutoff is the least y>=max(x+1,3) with a_y<a_x; its anchor is the full
primorial period. Finite feasibility is discharged internally.
The remaining hypothesis is the actual bound

    exists B, forall N, ||selectedLogarithmicHeadOptimizer N||_Q² <= B.

This hypothesis is **Open**. Larger period choices are allowed by the
flexible-family theorem and may be preferable for supplying a bound.

## 6. The actual prime-power target and its exact Mellin transform

For every integer p>1, the contraction

    F = D_p(F+1),   (D_p f)(n)=f(floor(n/p)),

constructs an actual Pareto Hilbert vector. Strong induction identifies
its sequence as F_p(n)=floor(log_p n), with the usual zero anchor.
The same equation gives

    <F_p,1>_P = 1/(p-1),
    ||F_p||_P² = (p+1)/(p-1)².

Complete norm comparison constructs the actual Q vector and proves

    ||F_p||_Q² <= 2(p+1)/[zeta(2)(p-1)²].

This improves the loose bound in the handoff by a factor (p-1)/p.
For Re(s)>1/2, the already constructed Hilbert vector satisfies the exact
normalized Mellin identity

    Phi_s(F_p) = s M_s(F_p) = 1/(p^s-1).

The proof uses the continuous dilation formula and the fixed-point equation;
no unproved termwise interchange is inserted. The transform is nonzero.
Consequently F_p in the squarefree Q closure implies RH, by the existing
zero-annihilation theorem and the complete Q-to-Pareto map.
Membership remains an explicit hypothesis. No converse is asserted here.

The p=2 target also satisfies the squarefree-divisor jump relations and
positive-power jump invariance, by finite-coordinate limits of the legal
sieve. These necessary relations are not a sufficiency theorem for closure.

Owners: `PrimePowerHilbertTarget.lean`, `PrimePowerTargetMellin.lean`,
`QPrimePowerTargetJumps.lean`, and the generic transfer extension in
`ZetaTwoParetoTransfer.lean`.

The constructed target also sharpens the raw sieve's quantitative lower bound.
Instead of estimating its logarithmic head by the maximum (log_2 H)²,
the full target energy gives, for H>=2,

    ||A_H||_Q² >= a_H² H/(2 zeta(2))-||F_2||_Q²
                >= a_H² H/(2 zeta(2))-6/zeta(2).

The growing logarithmic loss is replaced by a fixed constant. The supporting
head identity keeps the signed term explicitly:

    sum_{n=1}^H Q(n) A_H(n)²
      = a_H² H/zeta(2)
        -(2a_H/zeta(2)) sum_{n=1}^H F_2(n)/n
        +sum_{n=1}^H Q(n)F_2(n)².

The lower bound compares this head with the complete norms of both A_H and
F_2; the rest of the Q tail is nonnegative. Owner: `QPrimePowerSieveEnergy.lean`.

## 7. Exact finite symbolic checks

Wolfram verified the norm-correction algebra symbolically. It also verified
the complete head identity for the following six consecutive primorial
pairs, using divisor compression and exact rational arithmetic:

| L_x | L_y | a_x | a_y | head coordinates checked |
|---:|---:|---:|---:|---:|
| 2 | 6 | 1/2 | 1/3 | 2 |
| 6 | 30 | 1/3 | 4/15 | 3 |
| 30 | 210 | 4/15 | 8/35 | 5 |
| 210 | 2310 | 8/35 | 16/77 | 7 |
| 2310 | 30030 | 16/77 | 192/1001 | 11 |
| 30030 | 510510 | 192/1001 | 3072/17017 | 13 |

All 41 coordinates passed. The cap is the seventh primorial, 510510;
no stage beyond it was used. These checks do not calculate all seven
rational minima or supply an infinite energy estimate.

The separate symbolic refinement identity is

    u_L(a)-u_(2L)(a)-u_(2L)(a+L)
       = L(L-a)/[2(a+L)²(a+2L)(2a+L)].

This last displayed identity was checked symbolically, not added as a
separate Lean theorem in this change.

## 8. Next substantive work

1. Bound actual complete-Q legal gains or signed tails relative to the
   remaining minimum/error. The new rational-metric refunds isolate a
   separate controlled term; they do not provide that relative lower bound.
2. Study the exact inverse-Gram energy of U_(x,y) with both head and period
   varying. Find a uniform full-energy bound or a concrete obstruction.
3. Keep the new target Mellin test available to audit proposed regularizations.
   Pointwise fitting, radical-invariant jumps, fixed-head energy decrease,
   and contraction of the rational-weight gap are each insufficient alone.

The original signed absorption target remains Open:
S_L>=-theta R_L-epsilon_L with fixed theta<1 and independently controlled
epsilon_L->0. Together with S_L+R_L=5 phi(L)/(3L²), it would force D=0.

Source/provenance: user-provided continuation agenda and existing project
modules. The contraction, projection, finite inverse-Gram, and weak-limit
arguments are ordinary mathematical constructions; no novelty claim is
made merely because these formalizations are new to the repository.

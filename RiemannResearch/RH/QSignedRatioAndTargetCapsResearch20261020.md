# Signed-tail cancellation, sharper metric refinement, and capped-target energy

20 October 2026. Continuation of the user-provided
`RH_CRT_Lean_Continuation_Agenda_2026-10-20 (1).md` from current main
`0305b41a36a6f63d3195449613c1a39e698331cd`.

## Scope

Write H for the complete-Q closed span of all squarefree legal residue atoms,
Q(n)=1/(zeta(2)n^2), h=P_H 1, and D=||1-h||_Q^2.
All squarefree composite conductors remain in the dictionaries.
Constant membership in H and RH remain unresolved.

The new ratio result removes a substantive assumption from the earlier result:
it no longer assumes D>0. It does not establish D>0 or D=0.
The capped-target results formalize an obstruction mentioned in the handoff.
Final publication is gated by the server checkpoint, which validates the actual
saved source and reports its exact commit and verification scope.

## 1. All-cutoff signed ratio, with an explicit rate

The repository stages are L_n=primorial(n+3), the product of primes at most
n+3. Composite cutoffs therefore repeat a period. Let R_L be the actual
rational minimum, S_L its signed tail, and B_L=5 phi(L)/(3 L^2).
The previous exact identity R_L+S_L=B_L is retained.

Three applications of Bertrand's postulate give distinct primes in
(m,2m], (2m,4m], and (4m,8m]. Their product divides primorial(8m), so

    8 m^3 <= primorial(8m),                       m>=1,
    8 floor(x/8)^3 <= primorial(x),               x>=8.

For x=n+3>=24 choose a prime q with x<q<=2x. It is coprime to L_n.
The cubic bound makes q<L_n and gives

    q^2 floor(x/8) <= 128 L_n.

The actual three-site resistance bound in `QRationalCoprimeLower` then yields

    0 <= 1+S_(L_n)/R_(L_n)
       = B_(L_n)/R_(L_n)
       <= 1280/[3 floor((n+3)/8)],                n>=21.

Consequently S_(L_n)/R_(L_n) -> -1 **unconditionally**. The proof applies to
all cutoffs, including repeated composite stages; no prime number theorem,
RH, or positive limiting-defect hypothesis is used.

Owners: `NumberTheory/PrimorialPolynomialLower.lean` and
`RH/QRationalSignedTailRatio.lean`, especially
`rationalSignedTail_div_minimum_tendsto_unconditional`.

Reference for the neighboring-prime ingredient:
Mathlib.NumberTheory.Bertrand, `Nat.exists_prime_lt_and_le_two_mul`,
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Bertrand.html>.
The reference supports that ingredient, not an RH conclusion.

## 2. Exact scale of any additive absorption error

For a fixed real theta define the least real error required by the budget:

    A_theta(L) = -S_L-theta R_L
               = (1-theta)R_L-B_L.

Then, at every period,

    S_L >= -theta R_L-epsilon  iff  epsilon >= A_theta(L).

The new unconditional ratio gives

    A_theta(L_n)/R_(L_n) -> 1-theta,
    A_theta(L_n) -> (1-theta) zeta(2) D.

For every c<1-theta, all sufficiently late valid budgets must satisfy
epsilon/R_(L_n)>c. In particular, when theta<1:

* epsilon_n=o(R_(L_n)) makes the proposed budget eventually false, even if
  validity was requested only on a cofinal subsequence;
* epsilon_n=C B_(L_n), for any fixed real C, also makes it eventually false.

These are impossibility results for particular error scales. An absolute
vanishing error epsilon_n->0 remains possible and is still the open arithmetic
provider. Defining epsilon_n=A_theta(L_n) would satisfy the inequality by
definition; proving that error tends to zero would still require D=0.

Owner: `RH/QRationalAbsorptionError.lean`. The normalized-limit and rejection
theorems have no unresolved closure hypothesis. The little-o rejection has
the displayed explicit relative-error limit as its hypothesis.

## 3. Exact capped logarithmic targets and their nonlegality

For any integer p>1 let F_p(n)=floor(log_p n), with the repository's auxiliary
zero coordinate. Define C_(p,K)(n)=min(F_p(n),K).
The actual Pareto Hilbert vectors are constructed by

    F_p-C_(p,K) = U_(p^K) F_p,
    (U_d f)(n)=f(floor(n/d)).

The existing exact dilation norm and exact target norm give

    ||F_p-C_(p,K)||_P^2 = (p+1)/[p^K(p-1)^2] = E_(p,K).

Complete Q/P norm comparison gives

    E_(p,K) <= zeta(2)||F_p-C_(p,K)||_Q^2 <= 2 E_(p,K).

Thus the complete-Q squared error tends to zero. These are full infinite-norm
statements, not estimates of only a finite head.

Nevertheless every K>=1 cap lies outside H. Its jumps satisfy

    Delta C_(p,K)(p)=1,
    Delta C_(p,K)(p^(K+1))=0,

contradicting the proved positive-power jump invariance of every member of H.
This argument needs only p>1, not primality. It does not exclude F_p itself:
the offending later site moves to infinity with K, and the caps are ambient
approximants throughout.

Owner: `RH/PrimePowerTargetCap.lean`, including
`paretoCappedTarget_error_exact`, `qCappedTarget_error_sq_tendsto_zero`, and
`qCappedTarget_not_mem_squarefreeClosure`.

## 4. Sharper complete rational-metric refinement

For the rational periodic weight u_L(a)=1/a^2+2/[L(2a+L)], let
delta_L(a)=u_L(a)-zeta(2)w_L(a) and
Gap_L(f)=sum_(a=1)^L delta_L(a)(1-f(a))^2.
The complete infinite residue tails are retained throughout.

The proof starts with the exact positive remainder

    1/x^3-1/(x+L)^3-3L/(x+L)^4
      = L^2(L^2+4Lx+6x^2)/[x^3(x+L)^4].

Telescoping and summability give the full quartic progression-tail bound.
The previous exact midpoint defect is at most L^2/(3x^4), while its first
term bounds the coarse gap below. All-order residue-class regrouping then
proves, for every integer k>=2 and every L-periodic f,

    Gap_(kL)(f) <= [20/(3k)] Gap_L(f).

This improves the previous coefficient-independent factor 120/k by eighteen.
It applies to moving optimizer coefficients without any coefficient bound.
The sufficient thresholds are now k>=7 for nonincrease and k>=14 for a
half-contraction. The proof uses elementary reciprocal series and exact
telescoping, not a special-function convergence estimate.

Owners: `RH/QResiduePowerRefinement.lean` and
`RH/QRationalQuarticRefinement.lean`.

For actual nested primorial stages L_m=k L_n, n<=m, put G_n=Gap_(L_n)(f_n)
and Disp(n,m)=sum_(a=1)^(L_m) u_(L_m)(a)(f_n(a)-f_m(a))^2.
The existing exact identity remains

    R_n-R_m = G_n-Gap_(L_m)(f_n)+Disp(n,m).

The sharper comparison supplies

    R_n-R_m >= [1-20/(3k)]G_n+Disp(n,m),       k>=2,
    R_n-R_m >= G_n/2+Disp(n,m),               k>=14.

`QRationalStageGain.lean` now proves the factor-dependent bound and strengthens
the existing stage and cumulative-budget declarations to thresholds 7 and 14.
No duplicate compatibility wrapper is introduced. Their exact squared
displacement and terminal minimum remain present.

The gain is measured in the changing rational metric. It must not be identified
with the complete-Q projection gain without an additional proved comparison.
Summability of metric gaps and movements does not force the terminal defect D
to vanish.

## 5. Circularity audit and next substantive obligation

The signed ratio tends to -1 whether or not the minimum tends to zero.
There is no inference from that ratio to a positive residual defect.
The capped targets converge in norm but are not legal; there is no inference
from their explicit error formula to squarefree closure.

The remaining direct target is an independent upper estimate forcing
R_(L_n)->0, or a concrete legal-gain estimate for the actual complete-Q
optimizer. An equivalent sharp constrained-dual upper bound is still only
a reformulation until an arithmetic provider bounds it.

Promising next work is to retain the exact signed metric refunds and
optimizer displacement in a genuine arithmetic upper certificate. Any proposed
absorption error must pass the necessary-scale test in Section 2. For F_2,
study the actual complete-Q constrained minimum over all squarefree divisors;
neither divergent two-stage seeds nor nonlegal capped targets determine those
constrained minima.

## 6. Verification evidence and finite scope

Coherent development job `job_8cJpDaH3AgKWMagUj3LKiWP3_94CkIVj` returned
`verified=true`, exit 0 for the cubic primorial estimate, unconditional ratio,
and the initial exact/relative absorption-error suite. This is development
evidence, not a substitute for the final saved-source checkpoint.

Job `job_iRKtIhdTN8KRVsDPPOHPP-cIF947LAW4` returned `verified=true`, exit 0
for the complete capped-target construction, norm identities, convergence,
and nonlegality proof. Final module imports are checked again before publication.

Job `job_J4wUA7ZJ1g_qCbI1zMEH2jooy--HhcBz` returned `verified=true`, exit 0,
with no diagnostics for the full quartic refinement, exact all-order residue
regrouping, and the strengthened stage-gain and cumulative-budget results.

Wolfram checked the exact absorption rearrangements, cubic telescoping remainder,
and refinement-coefficient factorization symbolically. No new
optimizer numerical solve or finite primorial enumeration was performed in
this continuation, so the seventh-primorial experimental cap was preserved.
The all-cutoff Lean proof is a mathematical theorem, not an extension of those
finite experiments.

Saved-module audit `job_awqRyI7OtahWXdqkX6zwSEvCMZALDqt6` completed successfully
with `verified=true`, exit 0. It imported all seven changed mathematical modules
and inspected six key declarations. Their axiom dependencies were only
`propext`, `Classical.choice`, and `Quot.sound`. The printed theorem types retain
the explicit periodicity, stage-nesting, and relative-error assumptions.

The exact checkpoint job, final validation scope, and published commit are
reported to the user after terminal success. No GitHub Actions run is used.

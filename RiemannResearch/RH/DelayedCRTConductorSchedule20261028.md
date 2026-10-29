# Delaying the head behind conductor growth

Research continuation, 28 October 2026 (America/New_York).
Starting repository commit: `d9e99de3c9c8e889f79cd3fd8b4dcd132b56d474`, which
already contains the signed period/head balance and prime-repair developments
after the question's `dd07648` baseline. Those results and all earlier
fixed-stage minimizer definitions are retained.

## Outcome and verification levels

**The requested period enlargement works.** There is a legal squarefree vector
with period 510510, exact head through 15 (indeed 16), and complete squared
Q-energy strictly below one. The actual constrained minimum is therefore
strictly below one too. This is now a Lean theorem for an explicit rational
14-conductor witness, rather than a conclusion inferred from numerical optimization.

The stronger bound

    E(510510,15) <= 80205043617271/82245000000000 < 0.975197

is an independently checked exact computational certificate for a different,
127-conductor rational witness. That particular tighter inequality is not a
Lean numerical theorem. Full signed Gram optimization gives approximately
0.9751351445376681, a floating-point discovery value rather than a certified
value of the minimum.

There is also a Lean-checked complete-energy certificate at period 9699690,
head 19 (its vector is exact through 20). Further rigorous finite computational
certificates reach period 223092870, head 23. No uniformly bounded cofinal
schedule has been established. RH is not proved.

## Complete signed constrained Gram system

Put D_L={d>1:d divides L}, g_d(n)=(n mod d)/d, and

    E(L,H) = min { ||sum_(d in D_L) c_d g_d||_Q^2 : F(1)=...=F(H)=1 },
    Q(n)=1/(zeta(2)n^2), n>=1.

For ell=lcm(d,e), the exact Gram entry is

    G[d,e] = (1/zeta(2)) sum_(r=1)^ell g_d(r)g_e(r) W_ell(r),
    W_ell(r) = sum_(k>=0) 1/(r+k ell)^2 = psi_1(r/ell)/ell^2.

The special-function identity is NIST DLMF 5.15.1:
<https://dlmf.nist.gov/5.15.E1>. It supports the complete progression-sum
formula. Special functions are used for numerical discovery only; all new
arithmetic certificates use rational inequalities for these infinite sums.

The objective is the entire signed quadratic form c^T G c, with every diagonal
and off-diagonal entry. Equivalently solve Gc=A^T lambda, Ac=1, after removing
dependent head rows. No diagonal, independent-coordinate, or truncated-tail
surrogate is used in the reported complete-Gram optimizations.

The exact first difference is

    F(n)-F(n-1) = a - sum_(d|n,d in D_L) c_d,
    a = sum_(d in D_L) c_d/d = F(1).

For squarefree L, 1<=H<L, and all primes up to H dividing L, divisor inversion
reduces the constraints to

    c_d=-mu(d) for d<=H,       sum_d c_d/d=1.

Let I be the fixed indices, J the free indices, u=(-mu(d))_(d in I),
K=G[J,J], b=G[J,I]u, a=(1/d)_(d in J), and t=1-sum_(d in I)u_d/d.
Then the exact reduced solution and minimum are

    z* = -K^{-1}b + K^{-1}a (t+a^T K^{-1}b)/(a^T K^{-1}a),
    E = u^T G[I,I]u - b^T K^{-1}b
        + (t+a^T K^{-1}b)^2/(a^T K^{-1}a).

These formulas preserve the signed interactions with the fixed coefficients.
Positive definiteness follows from linear independence of the distinct
residue atoms, which can also be seen from the first-difference formula and
induction on conductor divisibility. The experiments solve this reduced
positive-definite system numerically, then reconstruct rational feasible
coefficients for separate exact certification.

## A small kernel-checked witness at the requested stage

The explicit vector is

    F = g2+g3+g5-g6+g7-g10+g11+g13-g14-g15+g30
        +(29518/15015)g17-2g34-(3/2)g51.

All 14 conductors are squarefree divisors of 510510. Its values at 1,...,16
are exactly one. Its next values are

    F(17)=F(18)=512/15015,
    F(19)=F(20)=15527/15015.

Only three of its conductors are absent from the old period: 17,34,51.
Thus a small structured part of the added dictionary already suffices to
defeat the old constant-one obstruction.

For a short complete-tail proof, group the terms into blocks with periods
30,14,11,13,102. Their exact ranges are respectively

    [-2/3,14/15], [-1/2,3/7], [0,10/11], [0,12/13], [-2,6584/15015].

Thus |F(n)|<=4 at every site, not just on the sampled prefix. Write
P(n)=510510 F(n), an integer-valued signed residue sum. Lean evaluates

    sum_(n=1)^1024 ceil(10^8 P(n)^2/(510510^2 n^2)) = 162048069.

Each ceiling is an upward bound. The complete tail obeys
sum_(n>1024) F(n)^2/n^2 <= 16/1024. With the existing checked inequality
1/zeta(2)<76/125, this proves

    ||F||_Q^2 <= (76/125)(162048069/10^8+16/1024)
               = 3108600811/3125000000 < 1.

`QCRTPeriod510510Certificate.lean` checks the rational vector, periodic block
bounds, exact head, squarefree legality, integer ceiling sum, infinite-tail
estimate, and its consequence for the actual minimum `minimumAt 15 15`.
No certificate premise about a numerical energy is left undischarged.

## What happened to the old conductor-gap obstruction?

At L=30030,H=15, the previously checked forced values are 1 through 16,
2 at 17,18, and 3 at 19,20. The existing theorem that every feasible energy
exceeds one remains unchanged.

After inserting 17, the actual constraints for any feasible vector become

    F(16)=1, F(18)=F(17), F(19)=F(20)=F(17)+1.

`QCRTGapRefinement.lean` derives these identities on the actual divisor
dictionary, then proves the exact completion

    sum_(n=1)^20 F(n)^2/n^2
      = 32932869651286797001/20748169979939001600
        +(39943549/3380259600)(F(17)+17814249/39943549)^2.

Consequently every feasible complete energy is at least

    32932869651286797001 / (20748169979939001600*zeta(2))
      = 0.9649421622341109... .

The decimal is only a display; the exact expression is the proved lower
bound. The same module proves the entirely rational consequence E>9649/10000.
Wolfram independently confirmed the square completion in exact arithmetic.

The old lower bound above one and the new upper bound below one therefore
give a rigorous strict improvement of the actual constrained minimum.

## Subsequent primorial comparisons

The exact computational bounds below include every inverse-square tail.
They bound feasible vectors and therefore the true minima; they do not
assert that the witnesses are optimal.

| Period L | Head H | Rational complete-energy upper bound | Decimal display |
|---:|---:|---|---:|
| 510510 | 15 | 80205043617271/82245000000000 | 0.9751965908842 |
| 510510 | 17 | 162709990384841/164490000000000 | 0.9891786150212 |
| 9699690 | 17 | 2717400901/2741500000 | 0.9912095207004 |
| 9699690 | 19 | 543483191/548300000 | 0.9912150118548 |
| 223092870 | 23 | 17378821007/17545600000 | 0.9904945403406 |

The full-dictionary numerical minima at (9699690,17) and (9699690,19) are
approximately 0.9758656518546 and 0.9783718881638. At period 223092870 we
optimized only the 68 divisor conductors at most 300. The value
0.9859942421486 is a floating-point estimate of that restricted-dictionary
minimum. The separate rational certificate supplies the rigorous upper bound
on the full-dictionary minimum.

For the 510510 witnesses, residuewise integral comparison gives

    W_L(r) <= 1/r^2 + 1/(Lr).

The checker forms the signed rational F(r) before squaring and rounds each
nonnegative term upwards on a fixed integer grid. The other witnesses use
an exact global amplitude bound and the tail B^2/K. Normalization uses the
exact rational lower estimate

    zeta(2) > sum_(n=1)^200 1/n^2 + 1/201 > 16449/10000.

The [reproducibility packet](DelayedCRTComputations20261028.md) includes immutable rational witnesses, an exact
integer verifier, numerical discovery scripts, a manifest, and a README.
After extracting its 18 text-preserved files, `python verify_all.py` recomputes all six recorded computational certificates
using only Python's standard library and leaves the inputs unchanged.

The 17-conductor head-19 witness is also formalized independently in
`QCRTPeriod9699690Certificate.lean`. Its signed integer residue numerator
has denominator 9699690000. A global bound of eight and 4096 upward-rounded
prefix squares give the checked full-energy estimate

    ||F||_Q^2 <= (76/125)(16225558099/10^10+64/4096)
               = 311254353881/312500000000 < 1.

Its exact head extends through 20. The checked actual-minimum consequence
uses `minimumAt 18 19`, since primorial(20)=9699690 and 19<=18+1.
The stronger head-19 fraction in the table uses a longer rational prefix
and tighter zeta normalization, and remains an external computational bound.

## Exact conditions for synchronizing head and conductor growth

`QCRTDelayedSchedule.lean` proves that a conductor gap makes the entire
zero-head subspace constant, and hence the actual minimum-norm adjustment
constant. Its interpretation as equality of exact-one minima additionally
requires exact-one feasibility at both heads, as in the concrete cases below.
This is stronger than agreement of a few physical coordinates.
It gives, in particular, head 15=head 16 at period 510510, and
head 17=head 18 at period 9699690. The new conductor 17 genuinely breaks the
old gap (15,20]; the following primorial also adds the missing prime 19.

For an actual new conductor q with a larger anchor conductor still available,
let F be the current minimum at head q-1 in the already enlarged dictionary.
Let kappa be the squared norm of coordinate evaluation at q restricted to
the legal zero-head space. It is the positive `stepCapacity` used in
`QCRTMinimumHeadCost.lean`. Then

    E(L,q) = E(L,q-1) + (1-F(q))^2/kappa.

If c_q is the coefficient of g_q in F, the same module proves exactly

    1-F(q)=c_q+mu(q),
    E(L,q)-E(L,q-1)=(c_q+mu(q))^2/kappa.

Thus the necessary and sufficient finite acceptance condition at a ceiling C is

    (1-F(q))^2 <= (C-E(L,q-1))*kappa.

This condition is kernel checked for the actual minimum-norm family, not
borrowed from the distinct minimizer of distance to the constant vector.
Precisely, the checked primorial theorem uses L=primorial(j+2), q<=j+1,
1<q, q dividing L, and an anchor conductor r with q<r. The wider arbitrary
feasible-period identity is its mathematical interpretation, not an expanded
claim about the declaration's formal type.
In reduced Gram coordinates kappa equals B[q,q], where

    B=K^{-1}-K^{-1}aa^T K^{-1}/(a^T K^{-1}a).

A missing prime must be inserted before the head reaches it. At fixed period,
heads at or beyond the first missing prime are infeasible; additional head plateaux
do not change this fact. Increasing the period cannot increase E at a fixed
head, but the new head cost must still be paid. The existing checked exact
balance is reused without dropping either squared-distance term:

    E_new = E_old - period_gain + head_cost.

For the particular transition (30030,14) -> (510510,15), the full-Gram
numerical values illustrate the proposed order of operations:

    E(30030,14)  = 0.9752439277902 approximately,
    E(510510,14) = 0.9678902581261 approximately,
    E(510510,15) = 0.9751351445377 approximately.

The numerical period gain is about 0.00735367 and the numerical head cost
about 0.00724489. Their difference favors this step by about 0.00010878.
These differences are floating-point evidence; the proved identity retains
their exact counterparts and does not infer an infinite induction from them.

## Paper-level arithmetic repair and the remaining obligation

There is an explicit useful direction behind the capacity test. If p is prime,
p does not divide q, and pq divides the enlarged squarefree period, put

    w=g_q-p*g_(pq)=-floor((n mod pq)/q).

This is zero before q, equals -1 at q, and satisfies |w|<=p-1. For the
already re-minimized old head, orthogonality gives

    ||F-delta*w||_Q^2 = ||F||_Q^2+delta^2||w||_Q^2,
    delta=1-F(q),
    ||w||_Q^2 <= (p-1)^2/(zeta(2)*(q-1)).

This supplies a sufficient arithmetic acceptance test. For odd q one can
take p=2. If one starts from the old-period minimizer before enlarging and
re-minimizing, the cross term -2 delta <F,w> must instead be retained.
These explicit repair observations are paper-level derivations in this memo,
not additional newly checked Lean declarations.

The tests at heads 15,17,19,23 do not prove termination of the period-enlargement
search for every subsequent head. No quantitative uniform bound on the
discrepancies, capacities, or accumulated head costs has been obtained.
The bound |F|<=4 belongs to the displayed finite witness. The existing
half-period logarithmic-oscillation result prevents retaining one fixed
global amplitude bound along cofinal exact heads; it does not prohibit
uniform control of the weighted Q-energy.
The exact signed cumulative budget remains the substantive open arithmetic
obligation. No new conditional RH wrapper is added in this continuation.

## Verification record

Saved-module job `job_ECBn9w__qWy0MD8WJnyxpHagfnreSdMD` built the four modules
QCRTDelayedSchedule, QCRTGapRefinement, QCRTMinimumHeadCost, and
QCRTPeriod510510Certificate successfully: verified=true, exit_code=0,
server elapsed 18.471 seconds. The eight inspected declarations, including
the integer ceiling certificate and the actual-minimum upper theorem,
reported only propext, Classical.choice, and Quot.sound.

The additional head-19 candidate and axiom audit passed in
`job_DBVKUJ4cQyIfjhwBbcxOKJ4mzrR-hVSP`: verified=true, exit_code=0, server
elapsed 54.598 seconds. The actual-minimum theorem again reported only
propext, Classical.choice, and Quot.sound. This was an isolated check before
the saved-module publication gate. An earlier secondary check was interrupted
when its server owner exited; its terminal status was established before
submitting this revised candidate. That interruption was not a mathematical
refutation and did not invalidate the already successful primary checks.

Workspace opening and client-side polling elapsed times were not individually
instrumented; neither is described as kernel-checking time. The job's reported
submission/start timestamps differed by less than 0.001 seconds. Publication
requires the separate final checkpoint validation; the final chat reports its
job, scope, and exact published commit.

Retained workspace token: `ws_QFveXDsvFCugkYEt1zm30WYbaFjWt_iC`.
Project root:
`/home/cri_2025/lean-agent-workspaces/ws_QFveXDsvFCugkYEt1zm30WYbaFjWt_iC/RiemannResearch`.
Follow any continuation workspace returned by publication.

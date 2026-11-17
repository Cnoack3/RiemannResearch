# Complete occurrence certificates and quantitative reuse tests

Date: 17 November 2026 (America/New_York).
Starting main: `1c97b73fbf62d39bd58baad6b71242c6443576d2`.
Namespace unless stated otherwise:
`RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection`.

This continuation develops the finite certification agenda in
[the occurrence-block catalog](THEOREM_CATALOG_OCCURRENCE_BLOCKS_20261116.md).
It proceeds from finite weighted-variance algebra, through actual optimizer
stability, to complete rational enclosures and reuse-energy certificates.
All mathematical derivations build on the existing repository; no claim of
literature novelty is made.

**Status:** the new finite identities, estimates, and certificate theorems
are proved in Lean. The final managed full-project checkpoint is the
publication gate. RH and the uniform cofinal arithmetic providers remain open.

## Complete weights and exact loss accounting

For fixed P>0 and cutoff x, use the actual canonical free positions
F={n : 1<=n<P, x<gcd(n,P)}, block endpoints a_i, complete progression weights
w(r), and target T(r)=atom(P,1,r)-1. No progression tail is dropped.
The finite occurrence objective uses 1<=r<P. The terminal residue r=P
continues to be handled by the existing RH energy split.

For any finite positive-weight block with mass W, mean mu, target values
in [lo,hi], and optimized variance V, the new exact identity is

    V + sum_r w(r)(hi-T(r))(T(r)-lo) = W(hi-mu)(mu-lo).

The endpoint product gives a sharper budget than the quarter-range bound.
Summing over the canonical blocks, while retaining the constrained initial
interval, gives

    occurrenceMeanBudget = occurrenceEnergy + occurrenceEndpointRemainder,
    occurrenceGapBudget  = occurrenceEnergy + occurrenceEndpointRemainder
                           + occurrenceMidpointRemainder.

Both remainders are proved nonnegative. The midpoint remainder is the
sum of W_i times the squared displacement of each mean from its midpoint.

The theorem `riemannHypothesis_of_cofinal_mean_green_budget` is a
**conditional implication** using the smaller mean budget plus the complete
signed Green trial. It still requires a common cofinal uniform bound.
No such provider is supplied in this continuation.

## Stability of the actual optimizer

For a fixed period P and x<=y, shrinking the allowed occurrence dictionary
gives an exact Pythagorean identity and

    occurrenceEnergy(P,x) <= occurrenceEnergy(P,y).

Equality holds exactly when every removed active coefficient of the x-fit
is zero. Strict inequality holds exactly when at least one is nonzero.
Every strict increase is additionally equivalent to a positive rational lower
endpoint for a removed coefficient at some finite refinement depth.
These statements keep P fixed; they are not a monotonicity theorem for
the changing primorial sequence.

A trial vector whose excess objective is E controls each active coefficient:

    (c*(n)-c(n))^2 <= 2(1/w(n)+1/w(n-1)) E.

This applies in particular to the actual shared atom coefficients, where
E is exactly reuseEnergy.

## Arbitrarily accurate finite rational certificates

Write t=r+PK and S_K=sum_(0<=k<K) 1/[(r+Pk)(r+Pk+1)]. The already sound
complete progression interval has rational endpoints

    L_K = S_K + 1/(Pt),
    U_K = S_K + 1/[t(t+1)] + 1/[P(t+1)].

The new proofs give exact endpoint increments, monotonicity, and

    U_K-L_K = (P-1)/[Pt(t+1)] <= 1/(PK)^2   (P,r,K>0).

The optimized occurrence objective is monotone in the weights. The
rational weighted-mean minimizers are allowed to move with those weights;
the proof does not substitute an approximate optimizer for the actual one.

Let E_K^- and E_K^+ be the finite rational occurrence objectives using
L_K and U_K. Then

    E_K^- <= occurrenceEnergy(P,x) <= E_K^+,
    0 <= E_K^+-E_K^- <= S(P,x)/(PK)^2,

where the explicit finite sensitivity S(P,x) is the initial sum of T(r)^2
plus, for each block, its cardinality times its target oscillation squared.
The lower endpoints increase, the upper endpoints decrease, and both
converge to the actual optimum. Every positive requested tolerance admits
a finite certified enclosure.

Automatic rational block-mean intervals use a rational lower-weight mean
and an explicit perturbation radius. Subtracting adjacent block intervals
produces an interval for every actual active coefficient. Its width is
exactly the depth-one width divided by K^2. Both endpoints converge to the
actual coefficient, and every strict coefficient ordering is eventually
certified by disjoint rational intervals.

Those original limits were proved with P and x fixed. The continuation below
now supplies uniform relative complete-budget errors and oscillation-normalized
block-mean radii. Neither the actual combined budget nor the block oscillations
have been bounded uniformly along P=greenPeriod(x).

## Exact characterization of reuse cost

The actual atom fit is a legal occurrence trial with excess exactly equal
to reuseEnergy. Therefore

    reuseEnergy(P,x)=0

if and only if the actual occurrence coefficients are constant on every
gcd fiber. Moreover, strict positivity is equivalent to the existence of
a single finite depth K and two free positions in the same gcd fiber whose
automatic rational coefficient intervals are strictly separated.

This equivalence supplies finite witnesses for every positive reuse cost;
it is not a finite termination claim for deciding equality to zero.

## Cutoff-five kernel certificates

At P=30 and x=5, all seven active coefficients are enclosed. Endpoint
arithmetic is replayed by Lean using exact rationals. All 29 nonterminal
residues and every infinite progression tail remain present.

| Quantity | Certified lower endpoint | Certified upper endpoint |
|---|---:|---:|
| occurrenceEnergy(30,5) | 342/10000 = 0.03420 | 3427/100000 = 0.03427 |
| reuseEnergy(30,5) | 363/100000 = 0.00363 | 39/10000 = 0.00390 |

The reuse interval combines the new occurrence interval with the previously
proved complete atom-energy interval [0.0379,0.0381] and the exact identity
atomEnergy=occurrenceEnergy+reuseEnergy.

| Active position n | 10000 times the coefficient lower bound | 10000 times the coefficient upper bound |
|---|---:|---:|
| 6 | 6494 | 6499 |
| 10 | 8088 | 8102 |
| 12 | 11619 | 11640 |
| 15 | 6770 | 6797 |
| 18 | 11764 | 11799 |
| 20 | 7437 | 7476 |
| 24 | 9189 | 9225 |

All seven coefficients are strictly positive. In the common gcd-six fiber,

    c*(12)-c*(6) >= 64/125.

A positive finite reuse cost is compatible with a bounded cofinal reuse
cost. This is not an obstruction to RH.

## Cutoff-seven kernel certificate

At P=210 and x=7, Lean replays all 209 nonterminal residues and all 45
free blocks, using depth K=2 complete-weight intervals:

    212/6250 = 0.03392 <= occurrenceEnergy(210,7)
                          <= 853/25000 = 0.03412.

Consequently,

    occurrenceEnergy(210,7) < occurrenceEnergy(30,5).

This is a theorem about two particular stages, not an inference of
asymptotic monotonicity.

## Quantitative lower certificates from separated coefficients

For active n,m>1 in the same gcd fiber, the new stability consequence is

    (c*(n)-c*(m))^2
      <= 4(1/w(n)+1/w(n-1)+1/w(m)+1/w(m-1)) reuseEnergy.

Replace the four reciprocal weights by the reciprocals of their positive
rational lower endpoints, giving the explicitly positive rational factor
C_K. Every certified gap delta>=0 with delta<=c*(m)-c*(n) yields

    delta^2 / C_K <= reuseEnergy.

In particular, the gap between automatic coefficient intervals produces a
fully rational lower certificate. The hypotheses n,m>1 are explicit;
the certificate does not silently use a positive-residue tail formula at zero.

## Declaration map and foundations

The original `2cbae18d` continuation added 100 public theorem declarations in
13 proof modules. The table below records that original addition; subsequent
mean--Green additions are described separately below.
This count includes supporting lemmas; it is not a count of solved uniform
research obligations. There are also eight private arithmetic checks and 20 explicit definitions.
Every module is exported from `RiemannResearch.lean` and belongs to an
existing Bazel package.

| Module | Public theorems | Role |
|---|---:|---|
| [Analysis/FiniteWeightedVarianceCertificates.lean](Analysis/FiniteWeightedVarianceCertificates.lean) | 15 | Exact endpoint variance identity; certified means and variances. |
| [Analysis/FiniteWeightedVariancePerturbation.lean](Analysis/FiniteWeightedVariancePerturbation.lean) | 5 | Movement of means and optimized variance under weight perturbation. |
| [RH/ExactHeadOccurrenceStability.lean](RH/ExactHeadOccurrenceStability.lean) | 11 | Fixed-period cutoff Pythagoras, equality/strictness tests, coefficient stability. |
| [RH/ExactHeadOccurrenceMeanBudget.lean](RH/ExactHeadOccurrenceMeanBudget.lean) | 9 | Exact budget remainders and the explicitly conditional cofinal RH consumer. |
| [RH/ExactHeadOccurrenceEnclosures.lean](RH/ExactHeadOccurrenceEnclosures.lean) | 6 | Transfer of complete weight enclosures to the actual optimizer. |
| [RH/ExactHeadOccurrenceRational.lean](RH/ExactHeadOccurrenceRational.lean) | 6 | Finite rational energy and block-mean certificate soundness. |
| [RH/ExactHeadOccurrenceStageFive.lean](RH/ExactHeadOccurrenceStageFive.lean) | 7 | Exact intervals for energy, all block means, and all active coefficients. |
| [RH/ParetoRationalWeightConvergence.lean](RH/ParetoRationalWeightConvergence.lean) | 7 | Exact progression endpoint increments and inverse-square width. |
| [RH/ExactHeadOccurrenceWeightConvergence.lean](RH/ExactHeadOccurrenceWeightConvergence.lean) | 9 | Nested energy enclosures, effective error, and arbitrary precision. |
| [RH/ExactHeadOccurrenceCoefficientIntervals.lean](RH/ExactHeadOccurrenceCoefficientIntervals.lean) | 11 | Automatic coefficient intervals, limits, separation, and cutoff certificates. |
| [RH/ExactHeadOccurrenceReuseCertificates.lean](RH/ExactHeadOccurrenceReuseCertificates.lean) | 7 | Fiberwise zero-cost criterion, complete finite positivity certificates, cutoff-five reuse bounds. |
| [RH/ExactHeadOccurrenceStageSeven.lean](RH/ExactHeadOccurrenceStageSeven.lean) | 2 | Complete cutoff-seven energy interval and strict comparison with cutoff five. |
| [RH/ExactHeadOccurrenceReuseLowerBounds.lean](RH/ExactHeadOccurrenceReuseLowerBounds.lean) | 5 | Quantitative coefficient-gap lower bounds and rational reuse certificates. |

The original `RH/ExactHeadOccurrenceCertificationAudit.lean` added 19 guarded
transitive axiom audits; the proposed continuation extends the total to 28. Their required foundations are exactly `propext`,
`Classical.choice`, and `Quot.sound`. These checks do not erase mathematical
premises: in particular the cofinal RH implication retains its uniform
arithmetic hypothesis. No placeholder proof or new axiom is introduced.


## Mean--Green upper certificates and exact remaining hypothesis

The reviewed continuation is documented in
[MEAN_GREEN_CONTINUATION_REVIEW_20261117.md](MEAN_GREEN_CONTINUATION_REVIEW_20261117.md).
The user approved committing and publishing this continuation on 17 November 2026.
The managed checkpoint record identifies the validated integrated commit.

For P>0 let C(P,x,u) be the mean budget plus the complete Green trial.
The exact identities in `ExactHeadOccurrenceMeanBudget.lean` give

    C = ||target-synthesis(u)||^2 + endpointRemainder
      = atomEnergy + endpointRemainder + ||synthesis(u*)-synthesis(u)||^2.

Thus the minimum over shared corrections is exactly atomEnergy+endpointRemainder.
The cofinal provider is equivalent to bounding this sum on cofinal stages;
the endpoint remainder cannot be canceled by a correction. This is an exact
reduction, not a provider of the uniform bound.

For 1<=r<=P and K>=1, `progressionWeight_endpoint_relative_errors` proves
that each complete-weight endpoint error is at most w(r)/K^2, uniformly
in the period. The proof uses w(r)>=1/(Pr)>=1/P^2.

`RH/ExactHeadMeanGreenCertificate.lean` defines a complete rational upper
certificate Q_K, using the direct target trial and the endpoint products.
Its central theorem `rationalMeanGreenBudget_relative` proves, for every
rational trial and positive P,K,

    C <= Q_K <= (1+1/K^2) C.

`RH/ExactHeadOccurrenceRelativeIntervals.lean` also bounds each existing
rational block-mean radius by its target oscillation divided by K^2, for
1<=a<b<=P and K>=1. The actual mean error satisfies the same bound. No
uniform bound on the oscillations is asserted.

Depth ten therefore gives at most one percent multiplicative certification
loss at every cutoff, without propagating coefficient intervals.
`cofinal_rationalMeanGreenBudget_iff` equates cofinal boundedness of Q_K
and C for any fixed positive K and prescribed rational correction family.
The RH consumer still explicitly requires the common cofinal bound.

`RH/ExactHeadMeanGreenStages.lean` retains the endpoint loss in the finite
comparison. It proves endpointRemainder(30,5)=0 and
endpointRemainder(210,7)>=2/143 from the first free block [10,14).
Consequently every cutoff-seven combined budget is at least

    212/6250 + 2/143 > 0.04790,

whereas the best cutoff-five combined budget is at most 0.0381.
This reverses the direction of the occurrence-only comparison, without
implying anything about asymptotic boundedness.

Status: finite identities, relative estimates, and finite comparison are
checked declarations; the common cofinal arithmetic provider remains **Open**.
The exact final verification record and floating-point diagnostics are in
the linked review. Numerical evaluations at cutoffs 11 and 13 are diagnostics,
not kernel certificates. The existing gcd-fiber lower bounds do not supply
an upper bound, and the total coefficient-dispersion bound still needs its
own uniform arithmetic estimate.

## Remaining research obligations

1. Prove a bound independent of the stage for the exact occurrence energy
   or a sufficient mean/variance budget along cofinal primorial stages.
2. Construct legal shared atom vectors with uniformly bounded complete
   signed Green trial at the same stages.
3. Establish any required squarefree smooth-gap or translated-sieve
   estimates with their actual arithmetic normalization.
4. Use the rational certificates to test proposed finite inequalities
   before attempting their uniform versions.

The earlier finite-enclosure task is now supplied in general, with
convergence and effective fixed-stage rates. The uniform cofinal tasks
remain open.

## Verification evidence

Before publication approval, the reviewed continuation passed the full `//:RiemannResearch` build,
including all 28 axiom guards, in 325.178 server verification seconds:
[Full-project BuildBuddy record](https://app.buildbuddy.io/invocation/c10a81f4-efe9-4471-be79-9e3ef6491698).
Its base is `325eabb4a52ceb0f616e15567f032919078761f9`; the complete draft
verification record is in the linked review. The subsequent managed checkpoint
records the final integrated verification and publication outcome.

For the original finite-certification work, the focused integration and all
19 guarded axiom audits passed using
Bazel/BuildBuddy: job `job_QTRp1GikP6Qe-0RPaJkJUdMq4bxcYg78`,
42.404 server-reported verification seconds.
[Integrated proof and axiom audit](https://app.buildbuddy.io/invocation/1e2690c8-f2b5-4cd2-8169-82ba3d706463).

The cutoff-seven exact replay also passed independently in
`job_77QRA6H0kzdWZAKPIc9z643J8fOwVbf5`:
[Exact finite replay](https://app.buildbuddy.io/invocation/80adcdbd-3346-4f48-96ba-5109424be837).

The managed checkpoint performs the full `//:RiemannResearch` validation,
source audit, commit, and push. Its terminal record identifies the exact
published commit and full-project BuildBuddy invocation. The focused
records above certify their targets and imports; publication still depends
on the complete checkpoint succeeding.

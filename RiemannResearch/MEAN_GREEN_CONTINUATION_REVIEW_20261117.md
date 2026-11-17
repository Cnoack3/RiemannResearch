# Mean--Green continuation for review

Date: 17 November 2026 (America/New_York).
Base: `325eabb4a52ceb0f616e15567f032919078761f9`, the main revision immediately after
`2cbae18d29f1f2d395c8257ad4db910943cdfc45`.
Workspace: `ws_lNlvzByMM1tsjDYFOsMTpLGHOdXx8QXZ`.
Approval: the user approved committing and publishing these reviewed changes on
17 November 2026. The managed checkpoint's terminal record is authoritative
for the integrated validation and published commit.

## Established mathematics

Let P>0, x be any natural cutoff, w(r)=progressionWeight(P,r), and
T(r)=atom(P,1,r)-1 for 1<=r<P. Let S(u) be the legal upper-divisor atom synthesis.
Write C(P,x,u) for the existing occurrence mean budget plus the complete
Green correction residual energy, and E(P,x) for occurrenceEndpointRemainder.

The new exact identities are

    C(P,x,u) = sum_(1<=r<P) w(r)(T(r)-S(u)(r))^2 + E(P,x),

    C(P,x,u) = atomEnergy(P,x) + E(P,x)
                 + ||S(atomNormalCoefficients)-S(u)||_w^2.

The constrained initial interval and all progression tails are retained.
The endpoint remainder is nonnegative, depends only on the actual blocks
and target, and cannot be canceled by adjusting u. Consequently

    min_u C(P,x,u) = atomEnergy(P,x) + E(P,x).

This minimum is attained by the existing actual atom-normal coefficients.
The new cofinal equivalence is exact, with the SAME bound B:
existence of a shared correction family bounded by B on cofinal stages is
equivalent to atomEnergy+E being bounded by B on cofinal stages.
It supplies no provider for either statement.

## Uniform certification accuracy

For any P>0, 1<=r<=P, and integer refinement depth K>=1, complete weight
endpoints L_K,U_K satisfy

    w-L_K <= w/K^2,        U_K-w <= w/K^2.

The proof combines the existing absolute endpoint error 1/(PK)^2 with
w(r)>=1/(Pr)>=1/P^2. Thus the relative constant is independent of P, x,
the number of free positions, and the correction coefficients.

For any fixed rational trial vector q, define Q_K(P,x,q) by replacing w
with its rational upper endpoint U_K in the exact direct-trial formula.
All target values, atom counts, endpoint products, and q are rational.
The resulting finite rational expression obeys

    C(P,x,q) <= Q_K(P,x,q) <= (1+1/K^2) C(P,x,q).

In particular K=1 gives factor 2, and K=10 gives factor 1.01, at every
cutoff. No coefficient-interval propagation or atom normal solve is needed
to certify a proposed q. All signed cross terms remain inside the trial square.

For any prescribed rational family q_x and fixed K>=1, the existence of
some finite common bound for Q_K on cofinal stages is equivalent to the
same boundedness property for C. The comparison can enlarge the bound by
1+1/K^2; it does not assert equality with the same B.

The existing rational block-mean radius also satisfies

    radius(P,a,b,K) <= (T(b-1)-T(a))/K^2

for 1<=a<b<=P and K>=1. The actual complete-weight mean differs from its
rational lower-weight mean by at most the same quantity. These are
`rationalBlockMeanRadius_le_oscillation` and
`rationalBlockMean_error_le_oscillation` in
`RH/ExactHeadOccurrenceRelativeIntervals.lean`. Since each occurrence
coefficient is a difference of adjacent block means, this identifies the
remaining arithmetic scale in its interval widths. A bound independent
of cutoff for the oscillations themselves is not proved.

## Finite-stage warning

The new kernel-checked finite theorems prove

    E(30,5)=0,       E(210,7)>=2/143,

and hence, for EVERY shared correction u at cutoff seven,

    C(210,7,u) >= 212/6250 + 2/143 > 0.04790.

The existing atom-energy certificate and E(30,5)=0 give

    C(30,5,atomNormalCoefficients) <= 0.0381.

Therefore `optimal_meanGreenBudget_five_lt_seven` proves that the best
combined mean budget at five is strictly smaller than every combined mean
budget at seven. The smaller occurrence energy at seven does not produce
a smaller combined budget. This is a finite result, not an asymptotic
obstruction to boundedness.

The endpoint lower bound uses only the first free block [10,14):
its endpoint target values are 0 and 2, with target 1 at residues 11 and 12.
Its contribution is w(11)+w(12)>=1/132+1/156=2/143. All remaining
nonnegative block terms and progression tails are retained.

## External exact-rational trial evaluations

Python Fraction arithmetic evaluated the lower- and upper-weight direct-trial
functionals at depth K=1, using the shared six-decimal coefficient proposals.
The following displayed endpoints were rounded OUTWARD exactly to denominator
10^8. This arithmetic has not been replayed as concrete Lean certificates.

| x | P | lower-weight functional, rounded down | upper certificate Q_1, rounded up |
|---|---:|---:|---:|
| 5 | 30 | 3656059/100000000 | 3897009/100000000 |
| 7 | 210 | 5580523/100000000 | 5656530/100000000 |

The cutoff-five coefficients are 743144, 974745, 1068929 over 10^6 at
divisors 6,10,15, respectively. The cutoff-seven coefficients are listed below.
The exact upper evaluations are both below 3/50. These are finite external
arithmetic checks, not uniform providers or newly kernel-replayed numerals.

## Floating-point diagnostics, not kernel certificates

The following are floating evaluations using complete elementary weight
endpoints at K=10. Weighted least squares proposes a shared correction,
then its coefficients are rounded to six decimal places. These values are
not outward-rounded floating intervals and must not be cited as rigorous
bounds.

| x | P | occurrence objective (upper weights) | endpoint penalty (upper weights) | combined trial (upper weights) | 5 x coefficient dispersion |
|---|---:|---:|---:|---:|---:|
| 5 | 30 | 0.034258716 | 0 | 0.038048887 | 0.936979726 |
| 7 | 210 | 0.034036978 | 0.021506949 | 0.056278423 | 3.708565290 |
| 11 | 2310 | 0.029072509 | 0.014041072 | 0.044917876 | 263.185048990 |
| 13 | 30030 | 0.021187872 | 0.008328761 | 0.033226932 | 4857.140666678 |

The dispersion column uses occurrence coefficients from the upper-weight
block means and their unweighted gcd-fiber averages. It is diagnostic
evidence that the coefficient l2/Hardy majorant loses too much at these
stages. It is not a proof that the actual return dispersion diverges.

The nine six-decimal trial numerators for x=7, over denominator 10^6, are

| d | numerator |
|---:|---:|
| 10 | 922655 |
| 14 | 963949 |
| 15 | 871758 |
| 21 | 958502 |
| 30 | 1124156 |
| 35 | 884042 |
| 42 | 1089236 |
| 70 | 1774182 |
| 105 | 1714263 |

## Exact remaining obligation and next step

Still open: construct B and legal shared correction coefficients u_x such
that, for every J, some x>=J satisfies C(greenPeriod(x),x,u_x)<=B.
Equivalently, prove a common cofinal bound for the actual atom energy plus
the nonnegative endpoint remainder. Choosing the actual optimizer does
not prove such a bound: its required energy estimate is the open problem.

The existing gcd-fiber discrepancy certificates are LOWER bounds for reuse
cost. The existing five-times-dispersion theorem is an UPPER bound, but
needs control of the total dispersion; no such uniform control was found.
Fixed-stage coefficient refinement and a two-stage decrease cannot supply
the cofinal quantifiers.

The repository already has `riemannHypothesis_of_cofinal_bounded_green_trial`,
which uses the exact occurrence energy rather than the larger mean budget.
A bound on the direct target-trial energy alone is sufficient along that route;
the endpoint penalty is an additional obligation of the mean-budget route.

The next analytic target should preserve signed cumulative cancellation:
bound the weighted square of T(r)-sum_d u_x(d) atom(P,d,r), together with
the endpoint penalty, on the SAME cofinal stages. The new Q_K provides a
finite exact certificate for candidate vectors with uniformly controlled
certification loss. Increasing K alone cannot manufacture a bounded family.

RH remains conditional. No hypothesis asserting RH, target membership,
or the desired cofinal bound is used in the unconditional finite identities
or relative enclosure theorem.

## Changed files

- RH/ExactHeadOccurrenceMeanBudget.lean: exact direct-trial and optimal-budget identities.
- RH/ParetoRationalWeightConvergence.lean: uniform relative endpoint errors.
- RH/ExactHeadMeanGreenCertificate.lean: complete rational upper certificate and conditional cofinal consumer.
- RH/ExactHeadMeanGreenStages.lean: finite endpoint comparison.
- RH/ExactHeadOccurrenceRelativeIntervals.lean: uniform oscillation-normalized mean radii.
- RH/ExactHeadOccurrenceCertificationAudit.lean: guarded transitive axiom checks.
- RiemannResearch.lean: exports.
- THEOREM_CATALOG_OCCURRENCE_CERTIFICATION_20261117.md: result status and remaining provider.
- This review note.

## Verification and publication

The general certificate file passed Bazel/BuildBuddy:
job `job_OuCkNhFfQZW0iwZxAUCPQkzSMm7AQf7x`, server verification 92.817 seconds.
[Focused check](https://app.buildbuddy.io/invocation/6a5bf60c-9c6b-4d72-8bb5-f398fd50565e).

The integrated finite comparison, prior certificates, 26 guarded axiom checks,
and the two normalized-radius candidates passed in
`job_EqYbkXgueqXsLiOJD1VXsqCCvweJDY5J`, 78.604 server verification seconds.
[Integrated audit and radius candidates](https://app.buildbuddy.io/invocation/7b126487-1103-4b99-bb8a-635d2b0593bc).

The complete project build **succeeded** for the base revision above plus
the reviewed Lean changes before publication approval:

- Job: `job_nhphvAbEnPo0J9xF2xYDIEm3TEPlYcRP`.
- Command: `bazel build --config=buildbuddy --color=no --curses=no //:RiemannResearch`.
- Server verification: 325.178 seconds.
- [Full-project BuildBuddy record](https://app.buildbuddy.io/invocation/c10a81f4-efe9-4471-be79-9e3ef6491698).
- Request SHA-256: `df5fe1978e4686cdef4e0c41858479a0251140b2040eaa5d8962a53be0f41e75`.

The final audit contains 28 guarded transitive axiom checks, all passing with
exactly `propext`, `Classical.choice`, and `Quot.sound`. These include the
prior finite certificates, the new relative estimates and finite comparison,
and the conditional RH implication. No placeholder proof or project-local
axiom is introduced. Successful compilation does not discharge the explicit
cofinal hypothesis.

Only this verification note and historical catalog wording were updated
after the successful build; the checked Lean source was unchanged.
This pre-publication record certifies the reviewed draft. The managed publication
checkpoint separately validates the integrated source before pushing.

The user subsequently approved committing and publishing the reviewed changes.
Publication uses the managed checkpoint, which audits and validates the integrated
source before committing and pushing. No GitHub-hosted CI result is being used.

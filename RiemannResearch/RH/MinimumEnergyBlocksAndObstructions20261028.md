# Remaining minimum-energy agenda: blocks, tails, and range obstructions

28 October 2026. Continuation of the user-provided minimum-energy exact-head
research agenda. Base commit: dd0764863f7aba964b44daec865142a7b99e621c.

## Status of the RH target

The new results establish complete-tail enclosures, actual-family block
comparisons, a strict finite convex-block gain, a signed head-six certificate,
universal range obstructions for squarefree periods, and logarithmically growing
coordinate oscillation for the actual canonical family. They do not establish
a common complete-Q energy bound with expanding heads, a bounded cofinal
subsequence, or RH. No new conditional RH theorem is substituted for the missing
arithmetic provider.

## Complete arithmetic-progression tails

QResidueWeightEnclosures.lean proves the exact finite-prefix identity before
bounding the remaining infinite progression. For positive real L,a and K a
nonnegative integer, the complete mass w(a) is bounded by

    sum_(k=0)^K 1/[Z(a+kL)^2] + 1/[Z L (a+(K+1)L)]
       <= w(a)
       <= sum_(k=0)^K 1/[Z(a+kL)^2] + 1/[Z L (a+KL)].

Here Z=zeta(2). The proof telescopes reciprocal differences and includes every
omitted atom. periodic_square_prefix_exact retains the exact shifted tail in
each residue class, and periodic_square_prefix_bounds gives two-sided complete
periodic square-energy enclosures. The positive representatives include r=L,
so the zero residue class is retained. The existing qNorm_eq_inversePowerMean
identifies these with actual Q norms for Hilbert vectors.

## Blocks and slower heads

QCRTConvexBlocks.lean defines finiteBlock from actual minimumEnergyApproximant
vectors. Finite affine coefficients summing to one retain the smallest head;
nonnegative coefficients give the requested convex subclass. Legality is
proved without a sign restriction. The energy is the full double sum of mixed
inner products.

At a larger primorial period, with the earlier head kept fixed, the full
minimum dominates the block. The theorem retains the complete squared-distance
remainder. The period inclusion follows from inequalities between the actual
stage indices; it is not an unproved arithmetic provider.

For two stages i<=j with exactly the same period,

    ||(1-t)Fhat_i+t Fhat_j||^2
      = ||Fhat_i||^2+t^2||Fhat_j-Fhat_i||^2.

Thus mixing along a period plateau cannot improve the earliest-head minimum,
even with signed affine coefficients. Blocks across growing periods remain a
constructive subclass of the larger-period, slower-head search.

## An explicit finite convex gain

QCRTBinaryBlockGain.lean uses the previously verified binary vectors f6 and f30.
For B(t)=(1-t)f6+t f30, the primary identity is

    ||B(t)||^2 = ||f6||^2 - 2t<f6,f6-f30> + t^2||f6-f30||^2.

The difference has complete norm square at most one. Every term in the source
pairing is nonnegative, and coordinate 20 contributes Q(20). The rational
coefficient t=1/1000 therefore gives

    ||B(1/1000)||^2 <= ||f6||^2 - 1/1000000.

This is a strict gain over that explicit feasible vector. The block has period 30
and exact head 2. It is not asserted to improve the canonical period-six
minimizer, nor to supply an expanding-head schedule.

## A signed certificate with head six

QCRTPeriod210Certificate.lean defines

    f = g2+g3+g5-g6+2g7-g14-g21-g30.

It is legal in the squarefree period 210 stage, equals one at 1,...,6, and takes
only the values -1,0,1. In particular f(105)=-1 and f(109)=1.

An exact rational sum through 210, together with the complete tail majorant
1/210 and the proved inverse-zeta bound, establishes

    ||f||^2 < 47/50.

Consequently minimumEnergyApproximant_five_lt gives the same upper bound on the
actual canonical minimum at j=5. All finite rational reductions use kernel
checking. No floating-point inverse or truncated Gram norm is used in this
Lean certificate.

## Why the bounded-range construction stops

QHalfPeriodHeadOscillation.lean proves full signed coordinate identities on
every divisor stage of period 2m with m odd. Exact head 6 forces

    f(m+4)=f(m)+2.

Exact head 14 forces

    f(m+8)=f(m)+3.

The squarefree-stage specializations discharge the period arithmetic: a
squarefree even period has an odd half; an odd period embeds into twice itself.
Thus no squarefree-period exact-head 6 vector can remain in [0,1], and no
squarefree-period exact-head 14 vector can remain in [-1,1], regardless of period
enlargement.

These are range obstructions, not common-Q-energy obstructions. The forced
oscillations occur near half the period, where the atomic probability weights
can be small. The head-six signed certificate attains the allowed range [-1,1]
and saturates the displayed difference 2.

## Logarithmic oscillation of the actual family

QHalfPeriodLogarithmicOscillation.lean proves an exact generalization. Let
L=2m be squarefree, m odd, H<L, and assume every prime up to H divides L.
For any vector in the divisor stage with exact head H, and 0<t with 2t<=H,

    f(m+t)-f(m)=floor(log_2(t)).

The proof decomposes the vector into the actual coprime seed and a zero-head
correction. The correction contributes exactly zero to this increment; the
seed contributes the existing exact prime-power count. No signed term is
removed by an inequality.

The canonical specialization discharges every arithmetic hypothesis for
L=primorial(j+2), H=j+1. Taking t=2^k shows that there is no finite B with
|Fhat_j(n)|<=B for every stage j and every coordinate n. Thus a common global
amplitude bound cannot supply the sought Q-energy estimate. This does not
exclude a common Q norm bound, because the forced large coordinates move
out to half of increasingly large periods.

## Additional exact finite experiments

The [continuation experiment bundle](https://chatgpt.com/library?file_id=libfile_03406b562cb88191a3558ec2f0aa3edb&account_id=personal)
contains the previous exact coefficient inputs and the new reproduction scripts.
These are separately checked Python integer certificates, not Lean numerical
theorems.

- A block of period 2310/head 10 and period 30030/head 12 candidates, with weights
  5/8 and 3/8, has complete energy <0.960787693 and improves both inputs.
- A half-and-half block of period 30030/head 14 and period 510510/head 16 candidates
  has complete energy <0.968995207 and improves both inputs.
- At period 510510, direct exact candidates give complete energies
  <0.961982437 at head 12, <0.967890264 at head 14, <0.975135153 at head 16,
  and <0.989132868 at head 18.

The scripts retain signed mixed terms, reverse interval endpoints for negative
products, and include the whole infinite tail. Candidate upper endpoints bound
the corresponding minima. Candidate lower endpoints are not claimed as lower
bounds on the minima.

Independent review found no mathematical error in the interval assembly.
The exploratory Gram systems are ill-conditioned, and synthesized coefficients
have sign changes inconsistent with a simple nonnegative Mobius taper.
Certified energy statements remain valid, but these data do not justify a
uniform recurrence or a common bound.

## Agenda obligations

Priorities 1--2 remain open at the uniform arithmetic-estimate level.
Priority 3 now has general Lean tail enclosures and an additional concrete
complete-energy certificate. Priorities 4--5 have exact comparison theorems,
finite strict improvements, and larger-period experiments. Their cofinal
boundedness deliverables remain open. Priority 6 cannot be completed until an
actual uniform provider is proved. The canonical Moore--Penrose construction
remains secondary and was not pursued in this continuation.

## Verification

The saved six-module import check and eleven principal declaration axiom audits
succeeded in server job job_-exEiWm4F1SCWjUKmlCJ02Nr5paoTqI6 (exit code 0,
verified=true). The server-reported duration was 15.498 seconds. Every audited
declaration depends only on propext, Classical.choice, and Quot.sound; no
project-local axiom occurs in those dependencies.

The general logarithmic theorem explicitly assumes a squarefree period, odd
half-period, prime coverage, and the stated finite exact head. Its canonical
specialization proves all period and coverage hypotheses for the actual
minimumEnergyApproximant family. No RH assumption or uniform-energy provider
is used by these new theorems.

The final publication checkpoint validates the unpublished project delta
before committing and pushing. Its job, validation scope, and exact commit are
reported in the chat. The source check above alone is not publication evidence.
Workspace-opening and client-polling delays were not separately timed and must
not be read as kernel-checking durations. Earlier transport failures and timed-out
checks provided no verification evidence and were recovered before resubmission.

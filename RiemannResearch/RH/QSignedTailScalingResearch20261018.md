# Signed tail scaling after the five-pass program

Research for Christian Noack. 18 October 2026.
This is a separately authorized continuation of 17 October's completed
five-pass program. Its counter remains 5/5 and its automation remains disabled.

## Mathematical outcome

The growing squarefree-block power-cost estimate remains open.
The continuation supplies a sharper complete-Q tail certificate, finite
signed component assembly, a concrete location obstruction to transporting
the earlier gain profile, and a stronger unconditional gain for the original
legal composite-anchor trial.

For B_Y=QMobiusExactHead.exactHead Y and
F=(3/4)B_4+(1/4)B_5, the new proved bound is

||1-B_4||_Q^2 - ||1-F||_Q^2 >= 1/(3100*zeta(2)).

The actual optimized gain source^2/denominator on the legal line through
B_4,B_5 obeys the same lower bound. This improves the previous
1/(10000*zeta(2)) certificate by the factor 100/31.
The established legality and exactness on coordinates 1,...,4 are unchanged.

This is finite arithmetic progress. No SPC exponent below one, infinite
annihilator mean-zero implication, or RH claim is obtained.

## 1. Complete signed mean and inverse-square Abel remainder

For a real sequence a(k), cutoff K>=0, and real mu, write

w_K(k)=1/(k+K+1)^2,
P_mu(N)=sum_(0<=k<N) (a(k)-mu).

Assume the weighted series is summable and |P_mu(N)|<=B for every N.
The exact identity and checked estimate are

sum'_k a(k)w_K(k)
 = mu*sum'_k w_K(k) + sum'_k (a(k)-mu)w_K(k),

|sum'_k a(k)w_K(k) - mu*sum'_k w_K(k)| <= B/(K+1)^2.

This follows by applying the existing finite Abel identity with its boundary
term, then taking the limit of the summable weighted series.
The signed mean is retained; it is not absorbed into an absolute error.
The complete mass satisfies

1/(K+1) <= sum'_k w_K(k),
sum'_k w_K(k) <= 1/K for K>0.

Both inequalities are proved by telescoping reciprocal differences.
There is no trigamma convergence argument or unsupported limit interchange.

For finitely many signed components c_i*a_i, the combined mean is exactly
sum_i c_i*mu_i and the certified centered error is at most

(sum_i |c_i|*B_i)/(K+1)^2.

This keeps every signed component in the series and in its mean.
Applied to a full Gram expansion, all index pairs, including cross terms,
must be included. The theorem does not supply uniform bounds for a growing
family by itself. It permits component periods to be treated separately
rather than forcing a single enormous common period.

## 2. Interface in the actual Q-Hilbert space

For actual f,g in QHilbert let

h(n)=qSequence(f,n)^2-qSequence(g,n)^2.

The existing complete norm identity is

zeta(2)*(||f||_Q^2-||g||_Q^2)=sum'_n h(n)/n^2.

The new energy_difference_centered_tail theorem retains the exact prefix
through K, the signed mean of the remaining physical sequence, and the
entire centered infinite complement. If

|sum_(0<=k<N) (h(k+K+1)-mu)|<=B for every N,

then

|zeta(2)*(||f||_Q^2-||g||_Q^2)
 - sum_(0<=n<=K) h(n)/n^2
 - mu*sum'_k 1/(k+K+1)^2| <= B/(K+1)^2.

This is an actual-Q certificate, not a replacement space or a formal
analytic continuation. The centered primitive estimate must be supplied for
the actual physical tail and actual coefficients.

## 3. Arithmetic period means and a location obstruction

Use the earlier actual residual and change:

r(n)=1-(n mod 2)/2-(n mod 3)/3-(n mod 5)/6,
e(n)=((n mod 6)-(n mod 5))/30,

where the subtraction in e is real subtraction.
For any real t define

h_t(n)=r(n)^2-(r(n)+t*e(n))^2=t*L(n)+t^2*J(n),
L(n)=-2*r(n)*e(n), J(n)=-e(n)^2.

The profile is exactly the signed physical energy difference for the legal
line B_4+t*(B_5-B_4). The full Q energy series is verified as well.

Kernel rational normalization of all 30 residue classes gives the exact
means

mean(L)=-1/540,
mean(J)=-31/5400,
mean(h_t)=-(10*t+31*t^2)/5400.

Starting with physical coordinate 1, the centered primitive bounds are

|sum_(1<=n<=N)(L(n)+1/540)|<=11/54,
|sum_(1<=n<=N)(J(n)+31/5400)|<=13/450.

For the quarter profile h_(1/4), the exact mean is -71/86400 and the
centered primitive bound is 2249/43200.

Consequently the complete translated series obeys

sum_(n>=1) h_t(n)/(K+n)^2 < 0 for every t>0 and K>=110,

and, with the sharper quarter bound,

sum_(n>=1) h_(1/4)(n)/(K+n)^2 < 0 for K>=63.

These are strict inequalities for the entire infinite series. The same
profile that gives a positive gain at its original location gives a
negative gain after sufficiently large translation.

Scope is essential: the phase is fixed at profile coordinate n=1.
The theorem does not identify translated profiles with growing legal
canonical heads and does not disprove SPC for any family.
Nor may these constants be used for an arbitrary actual cutoff tail without
adjusting its starting phase. The refined original certificate below uses
K=240, an exact multiple of the period 30.

## 4. Stronger actual legal gain

For h=h_(1/4), exact kernel normalization gives

sum_(0<=n<=240) h(n)/n^2 >= 329/1000000.

Since 240 is a multiple of 30, the centered primitive bound for the entire
remaining tail is exactly the one above. Its complete contribution is at
least

-71/(86400*240) - 2249/(43200*241^2).

Adding the prefix yields a bound exceeding 1/3100 after normalization by
zeta(2). No negative term or later physical block is discarded.
The existing exact line completion then gives the same lower bound for
the actual optimized source^2/denominator gain.

## Formal declarations and status

### General analysis module

File: RiemannResearch/Analysis/InverseSquareAbelTail.lean
Namespace: RiemannResearch.Analysis.InverseSquareAbelTail

- weight, weight_nonneg, weight_antitone, weight_summable;
- bounded_summable;
- centered_identity, centered_error_bound;
- periodic_centered_error_bound;
- weight_mass_lower, weight_mass_upper;
- weighted_sum_neg;
- finite_signed_error_bound.

### Actual Q certificate module

File: RiemannResearch/RH/QMeanTailEnergyCertificate.lean
Namespace: RiemannResearch.RH.QMeanTailEnergyCertificate

- energy_difference_centered_tail.

### Concrete arithmetic application

File: RiemannResearch/RH/QCompositeGainProfile.lean
Namespace: RiemannResearch.RH.QCompositeGainProfile

- linearGain, quadraticGain, profile, profile_eq;
- linearGain_mod, quadraticGain_mod, linearGain_period, quadraticGain_period;
- linearGain_abs, quadraticGain_abs;
- linearGain_mean, quadraticGain_mean, profile_period_mean;
- linearGain_short, quadraticGain_short, linearGain_prefix, quadraticGain_prefix;
- linearGain_tail_negative, quadraticGain_tail_negative, profile_tail_eq;
- positive_profile_translation_negative;
- quarter_mean, quarter_short, quarter_prefix, quarter_translation_negative;
- line_error_sequence, profile_signedEnergy, profile_energy_series;
- quarter_weighted_prefix;
- trial_gain_lower_refined, optimized_gain_lower_refined.

The concrete arithmetic results have no unresolved arithmetic hypothesis.
The generic certificates state their bounded-primitive hypotheses explicitly.
Printed axioms for the principal translation, refined gain, and finite signed
assembly declarations are only propext, Classical.choice, and Quot.sound.

## Verification and retention

Base main commit: 498a4517c7c85819156ce52aa36ab2a6125023eb.
Workspace: ws_IBzeK9XLt7RqCpgeQebxlfp9z6ux8UwS.
Project root:
/home/cri_2025/lean-agent-workspaces/ws_IBzeK9XLt7RqCpgeQebxlfp9z6ux8UwS/RiemannResearch.

The entire coherent candidate passed terminal snippet verification
job_bufXE-ZcMiNdnNjPsb50O8Yca7emHVcK, with ordinary Mathlib foundations.
This is development evidence; durable publication still requires the
mandatory server source audit and actual aggregate/changed-module checkpoint
with push=true. The terminal publication job and commit are reported in the
run handoff. Do not infer final project verification from the snippet alone.

No modification is made to the completed program's five-pass state.
No automation is created, resumed, or extended.

## Remaining arithmetic gap and concrete next target

The new estimate replaces a pointwise tail penalty C/K by a signed mean
term plus B/(K+1)^2. For growing legal blocks, neither the actual mean,
the centered primitive B, the signed source defects, nor the full Gram
denominators have yet been controlled strongly enough for an exponent
below one. The location obstruction shows why repeating a small successful
profile without preserving its physical weighting cannot supply that bound.

A concrete next legal-family test is anchors 57 and 58, both squarefree.
Explore the actual source for B_56 toward B_57 before imposing a positive
mixing parameter. Exploratory computations suggest that source is negative;
that sign has not been verified here and is not used in any theorem.
A possible certificate decomposes residue products into their individual
periods, each at most 58^2, and uses the new finite signed tail assembly.
If confirmed it would obstruct a fixed positive-step rule while leaving
signed optimization available. For a positive growing-block result, the
remaining requirement is a uniform quantitative saving for the actual
legal family, with all mixed terms and the entire tail retained.

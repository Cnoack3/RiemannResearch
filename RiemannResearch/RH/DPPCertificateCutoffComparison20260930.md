# Old vacancy certificates and weighted physical cutoffs

Date: September 30, 2026.
Research base: Cnoack3/RiemannResearch commit
0330eb1553c2c843446b2434fedbe1b741277dee.

The verified bridge is in
[IntegerDPPCertificateCutoffBridge.lean](IntegerDPPCertificateCutoffBridge.lean).
Source: user-requested comparison of the repository's existing frameworks.
These are exact consequences of those frameworks, not a claimed new proof of RH.

## The three different kinds of certificate

1. A finite **trial** c has reciprocal source S and full tail energy E.
   It supplies an upper bound on the first-site vacancy:
   vacancy(n) <= 2E/(S^2+2E), when E>0.
2. A finite **observation certificate** z satisfies the reciprocal observations
   on n tail atoms. Its energy is exactly
   ||z||^2 = tailCapacity(n) + ||z-tailMinimum(n)||^2.
   Large energy of an arbitrary such z need not mean large capacity.
3. A genuine **infinite dual certificate** z satisfies every reciprocal
   observation and has finite Hilbert norm. It is an obstruction:
   limitingVacancy >= 2/(||z||^2+2) > 0.
   Its existence has the opposite implication from a family of large-ratio trials.

The trial energy always includes
E = sum_i sum_j c_i c_j <tailAtom_i, tailAtom_j>.
No Gram cross term or physical tail has been truncated.

## Unconditional equivalence of provider propositions

The new declarations prove

WeightedVacancyCutoffCertificates
  iff (for every real B, some finite trial has E>0 and B E < S^2)
  iff (there is no genuine infinite dual certificate)
  iff closedSpace = top.

These equivalences do not assume RH and do not construct any of the
equivalent providers. Each condition still implies the existing
Mathlib RiemannHypothesis endpoint.

Relevant declarations:

- weightedVacancyCutoffCertificates_iff_finiteTrial_certificates
- weightedVacancyCutoffCertificates_iff_no_tailCertificate

The first equivalence follows through the actual limiting first-site vacancy
and the actual closed residue space. Thus a full old large-ratio provider
does imply the new cutoff provider, after choosing arithmetic rank N and
physical cutoff M. A single finite trial only bounds the first site; the
equivalence by itself supplies no same-rank numerical bound on the other sites.

## Exact finite-stage bridge

Write q=M+1, so the observed physical sites are 1,...,q, and let

H(n,q) = weightedVacancyPrefix n q,
C(n,q) = H(n,q) + 1/(q+1),
R(n,M) = sum_{i=1}^M w_i (1-K_n(i,i)),
tau_n = tailCapacity n,
v = sum_i c_i tailAtom_i,
t_n = tailMinimum n,
S = finiteTrialSource n c,
E = finiteTrialEnergy n c.

Counting coordinate i corresponds to physical site i+1. The exact identities are

H(n,M+1) = vacancy(n)/2 + R(n,M),

tau_n E - S^2 = E ||t_n - (S/E) v||^2,

Delta = (tau_n E - S^2)/((tau_n+2)(S^2+2E)) >= 0,

C(n,M+1) = E/(S^2+2E) - Delta + R(n,M) + 1/(M+2).

The second identity requires E>0. Delta is exactly the excess of the trial
upper bound over half the true vacancy. It is not set to zero. The
declarations are finiteTrial_capacity_gap_eq_square,
finiteTrialVacancySlack_nonneg, and weightedVacancyCutoff_eq_trial_split.

For every later rank N>=n, the verified bound is

C(N,M+1) <= E/(S^2+2E) + R(N,M) + 1/(M+2).

Here E and S belong to the trial at n, while R belongs to the later rank N.
This is weightedVacancyCutoff_le_trial_offsite.

At the same rank n, the exact necessary-and-sufficient inequality for a
cutoff certificate of size epsilon is

R(n,M) + 1/(M+2)
  < epsilon - E/(S^2+2E) + Delta.

This is weightedVacancyCutoff_lt_iff_trial_budget. It isolates the full
remaining off-first-site budget without losing the trial square.
Replacing Delta by zero yields a sufficient, potentially stronger condition.
The two global providers are already equivalent; this inequality describes
what is needed to convert a chosen individual trial at a chosen rank.

For a finite observation certificate z, the complete formula is instead

C(n,M+1)
  = 1/(||z||^2 - ||z-t_n||^2 + 2) + R(n,M) + 1/(M+2).

This is finiteTailCertificate_weightedVacancyCutoff_exact.
Its subtracted square cannot be dropped to turn arbitrary large certificate
energy into a small-cutoff upper bound.

## Quantitative dual obstruction, with the tail allowance retained

For every genuine infinite certificate z, every arithmetic rank N, and every
positive physical cutoff q,

H(N,q) >= 1/(||z||^2+2),

C(N,q) >= 1/(||z||^2+2) + 1/(q+1),

weightedVacancyMass >= 1/(||z||^2+2).

The first inequality follows directly from the complete first-site split.
The last two are tailCertificate_weightedVacancyCutoff_lower and
tailCertificate_weightedVacancyMass_lower.

There is a stronger exact decomposition in the obstruction case. When
limitingVacancy>0, let z_* be canonicalTailCertificate and p be the first
physical point. Then

C(N,M+1)
  = 1/(||z_*||^2+2)
    + ||P_closed p - P_N p||^2
    + R(N,M) + 1/(M+2).

This is weightedVacancyCutoff_eq_canonical_split. The canonical energy split

||z||^2 = ||z_*||^2 + ||z-z_*||^2

remains the existing certificate_canonical_energy_split. Neither square is
discarded in the exact identities.

The full mass also retains the actual tail through the existing equality

finiteWeightedVacancyMass N
  = weightedVacancyPrefix N q + weightedVacancyTail N q,

0 <= weightedVacancyTail N q <= 1/(q+1).

## Damped minimum: equivalent endpoint, quantitative obstruction

For any window containing counting site zero, with every damping weight in
(0,1), IntegerDPPDampedMinimum's exact benchmark equality is equivalent to
WeightedVacancyCutoffCertificates. The declaration is
weightedVacancyCutoffCertificates_iff_dampedWindow_minimum.

For the infinite prefix limit, the bridge also proves

WeightedVacancyCutoffCertificates
  iff dampedPrefixLimit = paretoProductBenchmark.

The quantitative comparison from IntegerDPPWeightedDeterminant transfers a
genuine dual certificate into the positive lower bound

paretoProductBenchmark/(||z||^2+2)
  <= dampedPrefixLimit - paretoProductBenchmark.

The declaration is tailCertificate_dampedPrefixLimit_lower.
Neither damped module supplies an unconditional approach to its minimum;
it detects the same unresolved condition rather than filling in the provider.

## Verification and remaining obligation

The coherent bridge candidate passed agent_workspace_run_code with exit
code 0. Axiom inspection of the original equivalences and decisive bridge
declarations reported only propext, Classical.choice, and Quot.sound.
No project-local axiom, placeholder proof, or unsafe declaration is introduced.
Repository acceptance additionally uses the change-aware checkpoint for the
new module and its exported dependents.

Established: the proposition equivalences, exact finite-stage identities,
nonnegative square slack, later-rank comparison, dual lower bounds, canonical
split, and damped endpoint comparison.

Open: construct arbitrarily large source-to-full-energy ratios, equivalently
arbitrarily small weighted vacancy cutoffs, or exclude every genuine infinite
dual certificate. For a chosen finite trial the exact budget above isolates
the remaining numerical obligation. This continuation does not prove RH.

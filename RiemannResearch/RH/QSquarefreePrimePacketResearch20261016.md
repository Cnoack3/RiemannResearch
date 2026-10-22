# Squarefree primorial prime packets: exact covariance screening

Date: 16 October 2026.

Source: user-provided
Q_Squarefree_Primorial_Cofinality_Verified_Results_and_Agenda_2026-10-16.md,
Sections 7--8. The development below continues its first research target.
Publication requires the final server checkpoint; finite identities do not
establish an arithmetic growth provider.

## Actual stages and the divisor partition

Use the existing cutoff-indexed L_n=primorial(n+3), with
D_n={d>1:d divides L_n}. Let p be prime and not divide L_n. The packet index
contains EVERY divisor of L_n, including one. Its conductors are p*d.

QSquarefreePrimePacket.adjoinedConductor_injective proves disjointness and
absence of repeated conductors. mem_range_adjoinedConductor and
adjoinedStage_eq_divisorSpan prove that the joined family is the entire
legal divisor family of p*L_n. No additive prime-only CRT span identity is
used. For example, L=6 and p=5 give old conductors 2,3,6 and packet
conductors 5,10,15,30.

This parameterization adjoins any fresh prime to an actual old primorial
stage. At a prime cutoff p=n+4, equivToNext identifies the joined index with
the existing next-stage divisor index, and adjoinedCapacity_eq_next proves
equality of the actual capacities. Composite cutoffs leave the stage unchanged.
A separate first-M-primes enumeration is not introduced.

## Full signed block identities

All means and covariances use the actual full-Q inner product, where
Q(N=k)=1/(zeta(2)*k^2), k>=1. Write the joined centered covariance and mean as

    C_join = [C V; V^T S],    b_join = [b; beta].
    R = S - V^T C^(-1) V,    delta = beta - V^T C^(-1) b.

QCovarianceScreening defines R as the Gram matrix of the genuinely screened
centered Q vectors and proves the displayed Schur identity.
Positive definiteness of R follows from actual residue independence and
the fresh-prime divisor partition; it is not an additional premise.

The exact identities are

    kappa_join - kappa_old = delta^T R^(-1) delta,
    u_T = R^(-1) delta,
    u_D = C^(-1) b - C^(-1) V u_T,
    c_join = u / (1 + kappa_join),
    ||1 - sum_d c_join(d) g_d||_Q^2 = 1/(1+kappa_join).

The entrywise old coefficient correction retains every signed mixed term.
The general Hilbert-space block inverse identity is
FiniteGramCapacity.inverseSource_screened_sum
(in Analysis/FiniteGramScreenedInverse.lean). Its Q specialization is
QCovarianceScreening.covarianceInverseSource_blocks; the normalized
least-squares coefficients are gramInverseSource_blocks.
The actual primorial old capacity is used in
QSquarefreePrimePacket.adjoinedCapacity_sub_primorialCapacity.

## Residual correlation and exact accumulation

The signed source has the checked exact interpretation

    delta(d) = (1+kappa_old) * <1-F_old, g_(p*d)>_Q.

For every packet coordinate j, the full packet gain Gamma satisfies

    delta(j)^2 <= Gamma * R(j,j).

This uses the actual screened covariance, not the unscreened variance.
It supplies a precise location for a possible arithmetic estimate, but no
asymptotic lower bound is supplied by this inequality.

Define cutoffGain(n) as the actual packet gain for prime n+4 and zero at
composite n+4. The exact finite identity retains the initial capacity:

    kappa(N) = kappa(0) + sum_(n<N) cutoffGain(n).

The declaration is primorialCapacity_eq_initial_add_sum.

## Targeted server evidence

The server audit job job_8_pdzAKD200I296svlSp2GbSWZ-TrpQ6 succeeded with
exit code 0 and verified=true. It checked the complete module import, the
exact telescope and conditional consumer types, and an explicit application
whose conclusion is Mathlib's root RiemannHypothesis.

The generic inverse-source theorem and conditional RH consumer depend only
on propext, Classical.choice, and Quot.sound. No project-local axiom or
sorryAx appears in those transitive axiom reports. This targeted check is
distinct from the final aggregate-project publication checkpoint.

## RH-facing interpretation and remaining work

This completes the finite prime-packet algebra requested by agenda target 1,
subject to successful final server validation. The prior cofinality result
still identifies primorial capacity divergence with squarefree target
closure, which has an existing checked consumer for Mathlib RH.

Conditional research reduction:
riemannHypothesis_of_packetGain_sum_tendsto consumes divergence to infinity
of these actual partial sums and concludes Mathlib RiemannHypothesis.
Open: the divergence hypothesis. No checked arithmetic provider discharges it.

Open: supply an arithmetic lower bound for the actual signed screened source
and its covariance energy, sufficiently often to force unbounded accumulated
packet gains. Nonnegative gains, packet cardinality, positive definiteness,
and independence of prime valuations do not prove this.

For a next-prime chain, retain every exact gain before summing. A conditional
summation theorem is not a provider of the arithmetic lower bound.
Any finite numerical experiment must use full-Q moments with controlled
tail error and account for covariance conditioning. Such experiments may
reject proposed estimates; they do not establish asymptotic divergence.

## A concrete arithmetic trial for the next investigation

Informal derivation, not formalized in this development: choose packet weights
t(d)=mu(d), for every d dividing L. The legal packet synthesis is

    h_(L,p)(n) = sum_(d|L) mu(d)*g_(p*d)(n)
               = n*phi(L)/(p*L) - A_L(floor(n/p)),

where A_L(x) counts positive k<=x with gcd(k,L)=1. This follows by retaining
the floor terms and applying finite Mobius inclusion-exclusion. In particular,
h_(L,p)(n)=n*phi(L)/(p*L) for 0<=n<p. Its later signed discrepancy is retained.

For these weights the general trial-source Cauchy inequality provides a
lower bound for the full gain from the squared signed source pairing and
the actual screened covariance energy. The unresolved task is to estimate
both quantities uniformly along the actual prime steps. Neither the short
initial segment nor a sieve-density heuristic supplies that estimate.
This is a candidate for arithmetic investigation, not a claimed capacity
growth theorem.

Do not identify the limiting legal projection residual with zero until an
arithmetic provider proves it. All CRT carry contributions remain within
the actual residue inner products.

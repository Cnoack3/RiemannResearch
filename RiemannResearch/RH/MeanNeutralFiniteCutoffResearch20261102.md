# Finite-cutoff Cesaro criterion — 2 November 2026

Source: the finite-cutoff recovery handoff from the preceding conversation of 1 November 2026,
RH_Finite_Cutoff_UNVERIFIED_2026-11-01.zip.
Baseline workspace: 4533d2f7f0e98ecb6060a9c188e8bcd9f6f0ffc6.

## Mathematical scope

This development formalizes the finite-cutoff draft. It does not establish
the remaining arithmetic growth estimate or prove RH unconditionally.
The exact signed functions and their cubic tail estimate are reused from
SquarefreeMobiusCesaroEnergy. No independence assumption or diagonal-only
energy replacement is introduced.

Let Cg(n) = n^{-1} sum_{m=1}^n g(m), and let
lambda_P(n) = 2/((n+1)(n+2)), for n >= 1. Define

J_P(g) = sum_{n>=1} lambda_P(n) Cg(n)^2,
P_N(g) = sum_{n=1}^N lambda_P(n) Cg(n)^2,
T_N(g) = sum_{n>N} lambda_P(n) Cg(n)^2.

Every use of an infinite split requires summability. Actual finite legal
membership supplies this summability in the arithmetic application.
The primary identity is exactly

J_P(g) = P_N(g) + T_N(g),    T_N(g) >= 0.

The existing conditionalMeanPrefix definition is reused, with the same
argument order and meaning. It is moved from MultiRangeCertificateConvergence
to the lower-level ConditionalMeanFiniteCutoff module; certificate and
optimizer consumers import that owner. There is no duplicate prefix definition.

## Normalized comparison

For a cofinal real head scale H_j, suppose the exact normalized tail is
eventually at most a fixed K:

T_{N_j}(g_j)/|c_j|^2 <= K.

Then the two nonnegative normalized energies satisfy

P_{N_j}(g_j)/|c_j|^2 <= J_P(g_j)/|c_j|^2
  <= P_{N_j}(g_j)/|c_j|^2 + K.

The existing multiplicative and affine comparison lemmas prove equivalence
of zero lower logarithmic growth for these two energies. In the arithmetic
application c_j = 1. Nonzero amplitudes are required in the interpretation of
the general normalized expression.

For K=1, one can see the comparison directly:
0 <= log(1+J_P(g_j)) - log(1+P_{N_j}(g_j)) <= log 2.
After division by log H_j, the discrepancy tends to zero.

## Actual mean-neutral Mobius family

Write S_H = sum_{d<=H} mu(d)/d and M_H = sum_{d<=H} mu(d).
For 0 < H < D < E, the existing family is

g_{H,D,E}(n) = -sum_{d<=H} mu(d) r_d(n)
  + D(E S_H-M_H)/(E-D) r_D(n)
  + E(M_H-D S_H)/(E-D) r_E(n),

where r_d(n) = (n mod d)/d. This is the same two-repair family as the
existing weighted-average definition. It is legal, has g(n)=1 for every
1<=n<=H, and has zero period mean. If D and E are squarefree, existing
literal divisor-span membership applies, retaining composite squarefree
Mobius conductors as well as primes.

Let w_D and w_E be the existing two signed repair weights. Define the
actual coefficient budget

B(H,D,E) = (sum_{d<=H} |mu(d)| d)/8
  + |S_H| (|w_D| D^2 + |w_E| E^2)/8.

The previously proved complete cubic-tail estimate is

T_N(g_{H,D,E}) <= 2 B(H,D,E)^2 / ((N+2)(N+1)^2).

No mixed terms in the true energy have been discarded: this absolute
coefficient budget is used only to certify the far tail.

## Certified cutoff and finite window

The new arithmetic cutoff condition is

2 B(H,D,E)^2 <= (N+2)(N+1)^2.

A natural N satisfying it and N>=H always exists, without a bound uniform
in H,D,E. The canonical cutoff meanNeutralCubicCutoff is defined with
Nat.find and satisfies these two conditions. The resulting complete
certificate is

P_N(g_{H,D,E}) <= J_P(g_{H,D,E}) <= P_N(g_{H,D,E}) + 1.

The development does not prove a rate for this cutoff as H grows.
Existence of a cutoff does not imply a subpolynomial prefix-energy bound.

## Conditional RH endpoint and Open obligation

For cofinal positive heads H_j, with H_j<D_j<E_j, take the canonical
certified cutoffs N_j. Then RH follows if

liminf_j log(1+P_{N_j}(g_{H_j,D_j,E_j}))/log H_j = 0.

The full-energy and finite-prefix zero-growth statements are equivalent
for this family and cutoff. Legality, exact heads, summability, cutoff
existence, and the infinite-tail certificate are proved providers.

Open: construct schedules for which the displayed actual finite-prefix
energy has zero lower logarithmic growth. All signed Mobius-prefix,
prefix-repair, and repair-repair interactions remain inside its squares.
An arbitrarily large cutoff retains more prefix terms; choosing it does
not supply cancellation.

The theorem riemannHypothesis_of_meanNeutral_certifiedPrefix_lower_growth
retains hsmall explicitly. Its type does not assume RH, but its hsmall
premise is a substantive unproved arithmetic provider.

## Verification

Saved-module import and all 12 principal axiom inspections succeeded in
job_CzE6C_P63il_wqCJLF9KKEz9X-DqeN_-: verified=true, exit_code=0.
The server reported 766.465 seconds of job execution, including preparation
of imported modules; this is not an isolated kernel-checking measurement.
The queued-to-started interval was below 0.001 seconds. The submission
request round trip was approximately 2.6 seconds; workspace reopening was
a separate earlier request.

Every inspected declaration depends only on propext, Classical.choice,
and Quot.sound. The exact printed RH theorem retains its hsmall premise.
This check imported the two saved modules and the existing
MultiRangeCertificateConvergence consumer after definition relocation.

The final source makes the inferred cutoff arguments explicit to remove
an unused-binder warning. That changes no theorem type. Final project
acceptance and publication, including integration of newer main changes
when needed, are governed by the enclosing successful server checkpoint.
The import-and-axiom job alone is not described as an aggregate project build.

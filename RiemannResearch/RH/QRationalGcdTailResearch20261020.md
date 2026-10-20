# All-gcd rational signed-tail formalization — 20 October 2026 UTC

This continuation completes the concrete finite bridge identified in
`CRTCarryVerificationResearch20261019.md`. It uses the actual rational
weights and the existing attained divisor minimum. It proves no
asymptotic signed-tail estimate and makes no unconditional RH claim.

## Definitions and exact scope

For every integer L>0, set

    w_L(a) = 1/a^2 + 2/[L(2a+L)],    1 <= a <= L,
    f(a) = sum_{d|L} c_d (a mod d)/d,
    r(a) = 1-f(a),
    T_L(k) = sum_{a=k}^L w_L(a) r(a),
    C_e = {1 <= k <= L : gcd(k,L)=e},
    c_L = 5/(3L^2).

The normal equations are the weighted equations against **every** divisor
atom, including the harmless zero atom d=1. Coefficients are real. As in the
existing minimizer module, rationality of the coefficients is not asserted.

`QRationalGcdTail.exists_all_class_minimum` constructs coefficients
satisfying all the normal equations and attaining the global finite minimum.
It then supplies all gcd-class charges, cardinalities, centered identities,
square decompositions, and the endpoint tail for those same coefficients.
Thus the normal equations in the individual assembly lemmas have an existing
checked finite provider; they are not new research assumptions.

Squarefreeness is unnecessary for these finite statements. For squarefree L,
the divisor fit uses all squarefree divisors of L; no composite divisor is
discarded. These statements concern the rational finite objective, not an
unproved limiting transfer to the complete Q projection.

## Arithmetic bridge and theorem locations

`NumberTheory/DivisorIncidence.lean` specializes the existing
`Analysis/FiniteIncidenceTailCharge.extract_class_charge`:

- `moebius_left_inverse` proves the actual divisor-matrix inverse:
  sum_{j|L} 1_{e|j} mu(j/e) 1_{j|b} = 1_{e=b}, for e,b dividing L.
- `gcd_class_charge_moebius` extracts a gcd-class charge from the actual
  divisor-incidence totals. The inverse is displayed explicitly.
- `gcd_class_card` proves |C_e|=phi(L/e) by the bijection
  j -> e*j from positive reduced residues modulo L/e.
- `gcd_class_endpoint` proves C_L={L}.

The specialization in `RH/QRationalGcdTail.lean` then proves

    sum_{k=1}^L 1_{d|k} T_L(k) = 5/(3Ld),                 d|L,
    sum_{d|L} 1_{e|d} mu(d/e)/d = phi(L/e)/L,             e|L,
    B_e := sum_{k in C_e} T_L(k) = 5 phi(L/e)/(3L^2).     e|L.

The first identity uses finite signed Fubini, the concrete floor formula
for the divisor prefix, the existing residual first moment, and each
actual normal equation. The second uses the concrete divisor reindexing
and the existing finite Möbius/totient density theorem.

The principal declarations are `multiple_tail_charge`,
`divisor_moebius_reciprocal`, and `gcd_class_charge`.

## Means, fluctuations, and endpoint

Every class is nonempty. `gcd_class_average` proves the literal division
formula

    B_e / |C_e| = c_L.

Set U_L(k)=T_L(k)-c_L. The checked declarations
`gcd_class_centered_zero`, `gcd_class_square_decomposition`, and
`period_square_decomposition` retain the exact identities

    sum_{k in C_e} U_L(k) = 0,
    sum_{k in C_e} T_L(k)^2
      = phi(L/e)c_L^2 + sum_{k in C_e} U_L(k)^2,
    sum_{k=1}^L T_L(k)^2
      = L c_L^2 + sum_{k=1}^L U_L(k)^2.

The squares here are unweighted finite tail squares, distinct from the
weighted residual energy and from complete Q energy.

The endpoint is explicitly retained:
`residualTail_endpoint` proves T_L(L)=c_L. Therefore U_L(L)=0.
The case L=1 is covered: the divisor dictionary is zero, E_1=T_1(1)=5/3,
the sole class is {1}, and the noninitial coprime set is empty.

For the actual divisor normal solution, `residualTail_one_eq_error`
proves T_L(1)=E_L. Hence U_L(1)=E_L-c_L. Classwise centering does not
annihilate this particular fluctuation.

## What the identities imply for negative coprime mass

Write n=phi(L), t=n*c_L, and let P,N denote respectively the positive
mass and the magnitude of the negative mass on C_1 minus {1}.
Define

    V = sum_{k in C_1} (T_L(k)-c_L)^2.

The exact checked Jordan identity is

    N = E_L-t+P.

No signed tail is replaced by a positive quantity.
`coprime_negative_mass_exact` is the actual-minimizer specialization.

The additional finite inequality, now formalized, is

    4 N(N+t) <= n V.

It follows from the exact centered-square identity and finite
Cauchy-Schwarz applied to the absolute tail sum. The nonnegative initial
tail T_L(1)=E_L contributes no negative mass, so N is exactly the
negative mass of the full coprime class as well. The checked declaration
is `coprime_negative_mass_quadratic_budget`.

The reusable results are in `Analysis/FiniteSignedVariance.lean`.
They include the quadratic signed-mass budget and the direct pointwise
linear budget 4 c N <= sum (x-c)^2. These use standard finite inequalities;
no mathematical novelty is asserted.

Thus the class equations give an upper budget **in terms of V**, alongside
the exact lower constraint N>=E_L-t. They give no independent asymptotic
upper bound on V or N. In particular, positivity of B_e does not imply
positivity of the individual T_L(k), and centering preserves their
nonzero signed fluctuations.

## Remaining RH obligation

The required one-sided estimate remains Open:

    S_L >= -theta E_L-epsilon_L,
    theta<1 fixed, epsilon_L -> 0,

where S_L=P-N. Equivalently one needs a sufficiently strong actual
upper bound on N-P. A usable estimate for the displayed variance budget
would be an additional analytic input, not a consequence already proved
by the all-class identities.

The rational-to-complete-Q comparison and limiting approximation assembly
also remain separate obligations. No inference from finite class
centering to squarefree residual exhaustion is made.

## Verification and provenance

Targeted server job `job_2v3YDTbnveeeqnjt0SRdOBCs2aGOBf5K` succeeded
with exit code 0 in 16.109 seconds. It built the three new modules or reused
their already checked artifacts, then inspected axioms for six principal
declarations: the concrete left inverse, gcd-class cardinality, all-class
charge, attained-minimum assembly, full-period square decomposition, and
actual coprime negative-mass budget. Every inspected list is exactly
`propext`, `Classical.choice`, and `Quot.sound`. This targeted check is not
a claim of whole-project validation.

All three new Lean modules are exported by `RiemannResearch.lean`.
The source audit and affected-module server validation are required before
publication through `agent_workspace_checkpoint`. The session publication
receipt identifies its terminal job, validation scope, and exact commit.

The argument formalized here is the user's finite all-gcd argument in the
19 October research memorandum. Existing finite incidence inversion,
normal-equation existence, and centering theorems are reused. Finite
experiments at L=30 remain illustrations; the general results do not depend
on a numerical computation or a sign assumption.

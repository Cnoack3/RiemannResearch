# Damped Möbius errors: an unconditional signed P/Q discrepancy bound

Date: 2026-10-19.
Inspected baseline: 4650466d6a7d65d9bbd49f217b094b9e1063d9cd.

## Result and scope

This continuation formalizes the finite comparison previously left as an
ordinary proof in BalazardDeRotonResearch20261019.md and improves its head
constant. It uses the actual squarefree legal damped Möbius approximants.
It does not prove RH or the RH-conditional second-order asymptotic in that note.

Write Z=zeta(2), P(n)=1/[n(n+1)], Q(n)=1/(Z n^2), and

    F_(N,epsilon)(n) = -sum_(1<=d<=N) mu(d)d^(-epsilon) g_d(n),
    r(n) = 1-F_(N,epsilon)(n),
    A = sum_(1<=d<=N) mu(d)d^(-epsilon)/d,
    E_P = ||r||_P^2,  E_Q = ||r||_Q^2.

For epsilon>=0 and 1<=H<=N define

    b = epsilon log H,
    B = max(|A|, |A-b|),
    E_head = sum_(1<=n<=H) r(n)^2/[n(n+1)].

The complete exact metric identity is

    Z E_Q - E_P = D = sum_(n>=1) r(n)^2/[n^2(n+1)].

The new unconditional estimate is

    0 <= D <= B^2 log(H+1) + (E_P-E_head)/(H+1).

In particular, since B <= |A|+epsilon log H and E_head>=0,

    0 <= D <= (|A|+epsilon log H)^2 log(H+1) + E_P/(H+1).

The stronger head constant satisfies B^2=max(A^2,(A-b)^2). No sign
assumption is made on the finite charge A. All infinite tails are retained;
the quantity E_P-E_head is exactly the full Pareto tail.

## Exact identities before estimates

The existing Euler-product theorem gives

    h_epsilon(k) = sum_(d|k) mu(d)d^(-epsilon)
                 = product_(p|k) (1-p^(-epsilon)).

For included positive sites, the new arithmetic identity gives

    r(n) = n A - S(n),    S(n)=sum_(2<=k<=n) h_epsilon(k).

The proved positivity and epsilon-log bounds yield

    0 <= S(n) <= n epsilon log H,   1<=n<=H.

Consequently n(A-b)<=r(n)<=nA and |r(n)|<=nB. This endpoint
estimate uses the sign information that the triangle bound loses.

For an arbitrary Q Hilbert vector, QMetricApproximateHeads proves the
exact head/tail split of D and the sharper inequality

    D <= D_head + (E_P-E_head)/(H+1).

The head bound is first given with the finite harmonic factor
sum_(1<=n<=H)1/(n+1), then with log(H+1). The specialization to the
damped family uses the literal physical coordinates, not a surrogate
sequence or an assumed representation.

## Lean declarations

- RH/QMetricApproximateHeads.lean:
  metricCorrection_head_tail, metricCorrection_le_head_tail,
  metricCorrection_head_le_of_linear_bound,
  metricCorrection_le_linear_head_harmonic,
  metricCorrection_le_linear_head_log_tail, and
  norm_ratio_tendsto_one_of_linear_heads.
- RH/DampedMobiusMetricDiscrepancy.lean:
  realCharge, headEnvelope, q_residual_head_identity,
  q_residual_head_abs_le_envelope, q_residual_metric_discrepancy,
  q_residual_discrepancy_le_signed_head_tail,
  q_residual_discrepancy_le_charge_log, and
  q_residual_norm_ratio_tendsto_one.

The existing qDampedMobiusPartial legality result supplies squarefree
support. The generic metric estimates require actual Hilbert vectors,
so their summability is intrinsic rather than an omitted assumption.

## Conditional sharp transfer and remaining obligations

For any sequence with nonnegative damping, H_j<=N_j, H_j tending to
infinity, and E_P(j)>0, the new checked consumer says

    B_j^2 log(H_j+1)/E_P(j) -> 0
       implies Z E_Q(j)/E_P(j) -> 1.

No uniform bound or zero limit for E_P is assumed in this implication.
It is a conditional research reduction: the relative-head-budget provider
for the intended damping diagonal remains Open in Lean. The earlier
ordinary argument under RH is not relabeled as an unconditional provider.

The principal RH obligation remains Open: exhibit a suitable sequence
of actual legal vectors whose complete Pareto (equivalently Q) error tends
to zero, or discharge another established RH consumer's arithmetic budget.
A vanishing P/Q discrepancy or a ratio tending to one does not imply this:
both errors can remain positive.

The second-order limit D/epsilon^2 -> C_psi from the earlier note remains
an ordinary RH-conditional argument. Its analytic estimates and its weighted
strong-convergence provider have not been formalized by this update.

## Verification

Proof candidates were checked on the Lean server. Axiom inspection of the
principal declarations is part of the candidate check. Publication is only
through the push-enabled workspace checkpoint, which audits and validates
the changed modules and its required project scope. The terminal checkpoint
result is the authoritative record of the published source and validation.
No admitted proof, project-local axiom, or hosted-CI substitute is introduced.

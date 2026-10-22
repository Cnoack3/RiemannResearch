# RH continuation: exact next-head cost and complete periodic tails

Date: 2026-10-19 (UTC).

Source: the user-provided squarefree profinite lattice research agenda of
2026-10-16, Targets 1–3, and the conditional-carry agenda of 2026-10-18.
Those sources motivate the research questions. The proofs below specialize
the repository's finite Hilbert geometry and use the literal complete
inverse-square Q law. No special-function asymptotic estimate is used.

## Established next-head formula

Write g_d(k) = (k mod d)/d. Fix a positive period L containing all squarefree
conductors needed through n, with n>1, n dividing L, and an anchor r dividing
L with r>n. Let F_old be the actual complete-Q least-error vector constrained
to equal one at positive sites below n, and let E_(n-1,L) be its squared
error. Set delta_n = 1-F_old(n).

The old zero-head space is spanned by the independent compensated vectors

    v_d = g_d - (r/d) g_r,    d|L, d>=n, d!=r.

At site n their observations are exactly -1 for d=n and zero otherwise.
Let G be their complete Q Gram form and b this observation vector. The
capacity C_n = b^T G^(-1) b is constructed from the actual independent
vectors and is strictly positive; invertibility is not an extra hypothesis.

In RH/QSquarefreeHeadStep.lean:

- correction_completion retains the entire nonnegative norm remainder for
  every old zero-head correction with prescribed value delta.
- minimumError_single_head_cost proves the exact identity

      E_(n,L) = E_(n-1,L) + delta_n^2 / C_n.

- inverse_stepCapacity_le_trial_energy bounds 1/C_n by the complete Q
  squared norm of v_n, without removing any conductor from C_n.
- compensatedResidue_energy_le proves

      ||v_n||_Q^2 <= (r/n)^2 / (zeta(2) (n-1)).

  The proof uses the exact cancellation of reciprocal slopes, the vanishing
  head of v_n, and a bound on its entire inverse-square tail.
- minimumError_single_head_near_anchor_bound therefore gives, for n<r<=2n,

      E_(n,L) <= E_(n-1,L) + 4 delta_n^2 / (zeta(2) (n-1)).

For any actual coefficient representation F_old = sum_(d|L,d>1) c_d g_d,
the boundary Mobius inversion identity gives

    delta_n = c_n + mu(n).

This is proved in the owning module
RH/NormalizedResidueExactHeadCharges.lean as
residueFraction_exact_head_next_coefficient, including the case of an
absent conductor. The new head-step module assembles it into
minimumError_single_head_coefficient_bound. The c_d in that theorem are
coefficients of the actual optimizer, not arbitrary desired coefficients.

The reusable scalar completion and scaled-vector energy lemmas live in
Analysis/FiniteGramCapacity.lean.

## Exact periodic tail and its finite scale

For bounded L-periodic R and L>0, define

    S_L(R) = sum_(a=1..L) R(a)^2,
    T_L(R) = sum_(a=1..L) w_L(a+L) R(a)^2,

where w_L(x) is the complete Q mass on x, x+L, x+2L, ... .
RH/QPeriodicTailEnergy.lean proves

    E_Q[R^2] = (1/zeta(2)) sum_(a=1..L) R(a)^2/a^2 + T_L(R),
    (1-1/zeta(2)) S_L(R)/L^2 <= T_L(R) <= S_L(R)/L^2.

The lower constant is proved strictly positive directly from the Q atoms.
periodicTailEnergy_tendsto_zero_iff then identifies, for varying positive
periods, vanishing of the entire omitted tail with S_L(R)/L^2 tending to zero.
periodic_qError_first_tail specializes the exact equality to the actual
QHilbert error ||qOne-f||^2.

The earlier ZetaTwoCRTReciprocalEnergy module already proves boundedness
and zero-limit equivalences between the full energy and the first-period
reciprocal energy. The new contribution identifies and estimates the
exact remainder; it does not supply a bounded approximating family.

## Individual step carries have growing energy

The additions carry_square_atom and carry_norm_sq_lower in
RH/QResidueConditional.lean show that for d>0 and p>=1,

    ||p g_(dp) - g_d||_Q^2 >= (p-1)/(zeta(2) d^2).

At each site d*k, 1<=k<p, the carry has value k and the weighted square is
exactly 1/(zeta(2)d^2). Summing these atoms gives a positive finite subseries
of the complete norm. Thus a fixed-d unscaled carry cannot have uniformly
bounded energy as p grows. This statement does not estimate or discard
the signed mixed terms of combinations of carries.

## Open RH obligations and next proof objective

The exact cost/period-gain telescope from QSquarefreeAffineHead remains

    E_N + sum_(i<N) G_i = E_0 + sum_(i<N) C_i,

with actual optimizer differences defining every G_i and C_i. At squarefree
next sites, the new formula evaluates the head cost as delta_i^2/C_i^capacity.
Nonsquarefree boundaries still have zero cost under the existing legality
hypotheses.

Open: construct a cofinal sequence of squarefree legal stages and control
the signed cumulative balance of these evaluated costs and period gains
uniformly. A suitable summable weighted coefficient-defect budget is one
sufficient route when nearby anchors are available; no such budget or
growing-stage provider is asserted here. A bound on each isolated step
does not itself bound the total cost.

Open: exhibit an actual exact-head family with the uniform complete-Q bound
required by riemannHypothesis_of_bounded_affine_minima. The existing theorem
is a conditional research reduction until that provider is proved.

RH is not proved by this update. The new results are unconditional finite
identities and inequalities under their explicit elementary feasibility
hypotheses. Their checked axiom dependencies are the ordinary Lean/Mathlib
foundations propext, Classical.choice, and Quot.sound; those checks do not
discharge any open research hypothesis.

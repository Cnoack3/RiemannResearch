# Measure-change regularity: theorem catalog supplement

25 October 2026. Source: the user's ProjectionMeasureChangeResearch20261025.md.

## Established identities, implications, and obstructions

- RH/QScaledTailPerturbation.lean, namespace QAnnihilatorTailEscape:
  tail_sub, tail_sub_energy_exact, scaled_tail_transfer_sub.
- RH/QSquarefreeDisplacementRigidity.lean:
  witness_mem_orthogonal and witness_mean_energy retain the exact equality
  zeta(2)<1,u>=zeta(2)<r,B r>+||T d||^2 for u=B r_P-d.
  residual_eq_zero_iff_displacement_physically_bounded and
  residual_zero_iff_frequently_bounded_displacement_tail are equivalences.
  displacement_scaled_tail_tendsto describes the nonzero-residual branch.
- RH/QSquarefreeSmoothedProjection.lean:
  screened_mean_eq_energy, correction_bounded_iff_residual_zero,
  correction_scaled_tail_tendsto,
  residual_zero_iff_correction_frequently_bounded_scaled_tail.
  finiteCorrection_tendsto, movingCorrection_error_bound,
  movingCorrection_tendsto establish actual finite-stage convergence.
- RH/QSquarefreeReciprocalObstruction.lean:
  fourSiteFunctional_B_qResidue_two, B_qResidue_two_not_mem,
  B_not_preserves_closure prove the exact 1/8 multiplier obstruction.

All four modules use actual QHilbert vectors. Pareto projections use the same
physical squarefree closed span. No RH or target-membership premise is hidden
in these identities or equivalences.

## Conditional research reductions

- QSquarefreeDisplacementRigidity.riemannHypothesis_of_displacement_bounded.
  Open: a global physical bound for the actual Q/P projection displacement.
- QSquarefreeDisplacementRigidity.riemannHypothesis_of_frequently_bounded_displacement_tail.
  Open: one cofinal bound for the complete scaled Q tail of that displacement.
- QSquarefreeSmoothedProjection.riemannHypothesis_of_correction_bounded.
  Open: physical boundedness of P_V(B r).
- QSquarefreeSmoothedProjection.riemannHypothesis_of_frequently_finite_bound,
  riemannHypothesis_of_frequently_moving_bound, riemannHypothesis_of_uniform_moving_bound.
  Open: their displayed common coordinate bounds.
- QSquarefreeSmoothedProjection.riemannHypothesis_of_moving_head_bound.
  Open: C>=0 with |P_{V_N}B(1-F_N)(n)|<=C for all 1<=n<=N.

The concluding proposition is Mathlib's RiemannHypothesis, supplied by the
existing QSquarefreeCapacity bridge after target membership is established.
No theorem discharges the listed regularity obligations.

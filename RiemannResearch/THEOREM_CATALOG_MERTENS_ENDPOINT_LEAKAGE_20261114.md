# Mertens endpoint and harmonic leakage — 14 November 2026

This development extends repository base `6ee8111fc0a35e4b7194b6dbd7ed7238a5fda6ee`.
All statements below concern the actual Möbius function and complete Q norm.
Publication requires the server's full-project Bazel/BuildBuddy checkpoint.

## Established arithmetic endpoint

Module: [RH/MertensEnergyEndpoint.lean](RH/MertensEnergyEndpoint.lean).

For every fixed natural a, Lean proves
$$
\sum_{n\ge1}\frac{|M(n)|(6+\log n)^a}{n^2}<\infty,
\qquad
\sum_{n\ge1}\frac{M(n)^2(6+\log n)^a}{n^3}<\infty.
$$

Declarations:
- `mertensPrefix_eq_M_nat`: identifies the new cumulative representation with the existing PNT Mertens function.
- `summable_absolute_mertens_log_moment`: unconditional absolute first moments.
- `summable_mertens_endpoint_log_energy`: unconditional logarithmic second moments.
- `hasFiniteEnergy_half`, `hasFiniteEnergy_of_half_le`: replace the previous strict epsilon > 1/2 baseline by epsilon >= 1/2.
- `offDiagonal_converges_of_half_le`: the signed cross term actually converges throughout this unconditional range.

The provider is the already proved `M_shiftedLog_all_nat_powers`; no external
analytic provider is assumed. Constants may depend on the logarithmic exponent.
This does not establish finite energy at every positive damping.

## Exact signed convergence

Module: [RH/MertensEnergyConvergence.lean](RH/MertensEnergyConvergence.lean).

For epsilon > 0, `summable_diagonal_integrand` proves unconditional summability
of the diagonal. Given `HasFiniteEnergy epsilon`,
`offDiagonal_tendsto_of_hasFiniteEnergy` identifies the signed limit exactly as
the full total-energy sum minus the full diagonal-energy sum.
`hasFiniteEnergy_iff_offDiagonal_converges` strengthens the existing boundedness
criterion to an equivalence with convergence. The energy hypothesis at small
positive damping remains an Open arithmetic obligation.

## Quantitative leakage and harmonic centering

Module: [RH/QDensityLeakageQuantitative.lean](RH/QDensityLeakageQuantitative.lean).

Let Z = zeta(2), V be the full legal residue closure, r = 1 - projection_V(1),
and h_k = projection_(V perpendicular)(B g_k). For k >= 2:
$$
\|Zk h_k-r\|_Q^2\le\frac1{Z(k-1)}.
$$
Writing c_k = h_k - r/(Zk), for every n >= 0:
$$
\|c_{n+2}\|_Q^2\le\frac1{Z^3(n+1)^3},
\qquad \sum_{k\ge2}\|c_k\|_Q<\infty.
$$
Thus the partial sums of h_k minus their exact harmonic residual converge in Q.
No signed residual is discarded.

Declarations:
- `approximation_error_norm_sq_le`, `scaled_residue_leakage_error_norm_sq_le`: complete arithmetic and projected error estimates.
- `summable_residue_leakage_sq`: unconditional square summability.
- `eventually_residue_leakage_lower`: a positive harmonic lower bound if r is nonzero.
- `summable_residue_leakage_norm_iff`: absolute summability iff 1 belongs to V.
- `riemannHypothesis_of_summable_residue_leakage_norm`: conditional research reduction; absolute summability is Open.
- `residue_leakage_norm_sum_tendsto_atTop`: if 1 is not in V, the sum of the norms diverges to positive infinity.
- `centeredLeakage`, `scaled_centeredLeakage`, `centeredLeakage_norm_sq_le`: exact signed decomposition and cubic square estimate.
- `summable_centeredLeakage_norm`, `centered_residue_leakage_partial_sums_tendsto`: absolute convergence of the centered remainder and the exact vector asymptotic.

## Proof boundary

Established: endpoint arithmetic estimates, diagonal convergence, complete
leakage error bounds, centered absolute summability, and the stated equivalences.
Conditional: signed convergence at all small positive dampings, absolute
summability of the uncentered leakage, and constant-target membership.
No theorem here establishes RH unconditionally or asserts the unformalized
RH-to-full-Q-totality converse.

The modules include explicit axiom-audit commands for the main conclusions.
Acceptance uses queued Bazel verification and the full-project checkpoint,
including downstream and unexported modules. The terminal checkpoint record
provides the exact published SHA and verification job.

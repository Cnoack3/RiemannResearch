# Full-conductor prime decomposition and complementary forcing

Date: 13 November 2026.

## Scope and notation

These results use `QFullDisplacement.displacement`, the difference of the
actual Q and P projections of the unit target onto the closed span of
**all** residue atoms. They do not identify this displacement with the
squarefree displacement in `QPrimeCarryProjection`.

Write V for the full closure, W for the existing closed prime span, and
C = V intersect W-orthogonal in Q. Set d_W = projection_W(d) and
d_C = projection_C(d). The physical reciprocal multiplier is Rf(n)=f(n)/(n+1);
its existing Lean name is `QShiftedReciprocal.B`. The density multiplier
`QDensityMetric.B=dQ/dP` is a different operator.

## Established exact identities and estimates

The namespaces below are prefixed by `RiemannResearch.RH.`.

| Declaration | Result |
| --- | --- |
| `QFullDisplacement.conductor_forcing_deficit` | Complete signed forcing deficit at every conductor m >= 2, before any tail estimate. |
| `QFullDisplacement.conductor_forcing_error` | Absolute deficit <= sqrt(1/m) times the actual Pareto residual tail norm. |
| `QFullDisplacement.pResidual_cube_le_prime_projection` | (Pareto residual energy)^3 <= 64 zeta(2) times squared projected displacement norm, for any closed W containing every prime atom. |
| `QFullDisplacement.pResidual_norm_cube_le_prime_projection` | Equivalent norm form: norm_P(r_P)^3 <= 8 sqrt(zeta(2)) norm_Q(projection_W(d)). |
| `QFullDisplacement.prime_projection_eq_zero_iff_one_mem` | Zero prime-visible displacement iff the unit target belongs to the full legal closure. |
| `QFullDisplacement.prime_projection_eq_zero_iff_displacement_eq_zero` | Zero prime-visible displacement iff the actual full displacement is zero. |
| `QFullPrimeDecomposition.conductorComplement_eq_closed_nonprimeSpan` | C is precisely the closed span of (I - projection_W) g_m over composite m. |
| `QFullPrimeDecomposition.fullClosure_eq_prime_sup_closed_nonprimeSpan` | V = W orthogonal-sum closed-span{(I - projection_W) g_m : composite m}. |
| `QFullPrimeDecomposition.displacement_eq_prime_add_complement` | d = d_W + d_C. |
| `QFullPrimeDecomposition.displacement_norm_sq_split` | norm_Q(d)^2 = norm_Q(d_W)^2 + norm_Q(d_C)^2. |
| `QFullPrimeDecomposition.primeComponent_eq_projected_source` | d_W = projection_W(R r_P). |
| `QFullPrimeDecomposition.complementaryComponent_eq_projected_source` | d_C = projection_C(R r_P). |
| `QFullPrimeDecomposition.complementaryComponent_eq_zero_iff_pairings` | d_C=0 iff all <r_P, R (I-projection_W) g_m>_Q vanish for composite m. |

## Improvement: remove the complementary component from its forcing

Define F_C = projection_C(R(r_Q + d_W)). The following are exact or
unconditional estimates; none assumes either component vanishes.

| Declaration in `QFullPrimeDecomposition` | Result |
| --- | --- |
| `complementaryComponent_fixed_point` | d_C = F_C + projection_C(R d_C). |
| `complementaryComponent_norm_le` | norm_Q(d_C) <= 2 norm_Q(F_C). |
| `complementaryComponent_eq_zero_iff_forcing` | d_C=0 iff F_C=0. |
| `complementaryComponent_eq_zero_iff_reduced_pairings` | d_C=0 iff <r_Q+d_W, R (I-projection_W)g_m>_Q=0 for every composite m. |
| `complementaryComponent_eq_zero_of_primeComponent_eq_zero` | d_W=0 implies d_C=0. |
| `reciprocal_parity_not_mem_primeClosure` | Rg_2 does not belong to W; its four-site prime-span identity fails. |
| `reciprocal_not_commute_prime_projection` | R and projection_W do not commute. This concerns R itself and does not assert a separate claim about its compression to V. |

The factor two follows from norm(R) <= 1/2 and contractivity of the
orthogonal projection. The fixed-point identity retains both the forcing
and the compressed reciprocal term before the norm estimate is taken.

## Conditional research reductions and open obligations

- `QFullPrimeDecomposition.riemannHypothesis_of_primeComponent_eq_zero`
  proves Mathlib's RiemannHypothesis from d_W=0. Its sole substantive
  arithmetic premise, **d_W=0**, remains **Open**.
- `QFullPrimeDecomposition.riemannHypothesis_iff_primeComponent_eq_zero`
  proves the biconditional with the explicit
  `Pareto.BaezDuarte.BaezDuarteMobiusApproximation` provider.
  The classical RH-to-approximation implication is not independently
  formalized by this change. That provider remains **Open** in the
  repository's formalization boundary.
- **F_C=0**, equivalently the reduced composite pairing cancellations,
  remains **Open**. This change does not prove that d_C=0 alone implies RH.
- No theorem asserts that an orthogonal decomposition forces one component
  to vanish. No prime-coordinate independence under the physical Q measure
  is assumed.

## Files and verification

- `RH/QFullPrimeProjectionControl.lean`
- `RH/QFullPrimeDecomposition.lean`
- Both modules are exported from `RiemannResearch.lean`.

Successful development acceptance, using Bazel with BuildBuddy:

- Core proof snippet: `job_KJVIVfLUcW0xYXElihMuuZNJA_SO9XTX`;
  [BuildBuddy record](https://app.buildbuddy.io/invocation/cefa6267-fb22-4e8b-8751-9911c975599e).
- Complete decomposition, forcing criterion, RH reduction, and
  noncommutation snippet: `job_PVJNsKGsr4prncKqHUTA1fPVNhwrkyKI`;
  [BuildBuddy record](https://app.buildbuddy.io/invocation/f5781156-9426-4945-9515-a14fb3edb8b2).

These snippet records are development checks. Publication is gated by a
separate final checkpoint of the complete project target
`bazel build --config=buildbuddy //:RiemannResearch`, including integrated
main changes if publication requires them. The final checkpoint receipt
records the published commit and acceptance scope.

Source: user-provided Full_Conductor_RH_Projection_Machinery.pdf, Sections
4.2 and 10.3, followed by the user-directed argument on 13 November 2026.
The classical converse is contextualized by Bagchi, Theorem 1,
[arXiv:math/0607733](https://arxiv.org/abs/math/0607733); it is retained as
an explicit analytic provider, not imported as an axiom.

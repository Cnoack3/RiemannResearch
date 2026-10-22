# Integration of the recovered Pareto parity continuation

Source: Christian Noack's Pareto parity research agenda and its saved
20-theorem continuation, originally checked in workspace
`ws_UNbWT-AdA4dQjvOJG3eQ6Dhf91lPYjb5`, source commit
`3e698b7e48af90aae6d91bb159333f83cbb8ec35`.

The earlier source passed checks `job_x5pWaK80dFQaqzFIN8YlJgjbxI2T6PGh`
and aggregate build `job_kBHz15qc0vVy84v1ymYZ75Y0PaeCduJ3`.
Its publication job `job_Oj7HasaGnW5WugauiwqOKnXjonkkrjxS` failed on a
theorem-catalog integration conflict. The old checked source and unpublished
commit remain preserved.

This integration starts from published main
`9f974063f7edfd25ec1d9b997bd9fc4cee67c74c`. It preserves the newer
`ParetoProjectionOvershoot` definition and published consumers rather than
exporting a second overshoot module with conflicting declarations.

## Recovered additions

- `ParetoL1DualTest`: the general bounded-sequence dual test for the complete
  L1 norm, under the original lowest general-purpose namespace.
- `ParetoProjectionOvershoot`: the original explicit bounded sign test is
  reused to prove the existing odd-orthogonality detector; the finite residual
  coordinate identity, full positive-part sum, and cofinal critical overshoot
  endpoint equivalence and RH consumer are integrated here.
- `FiniteDyadicEndpoint`: the exact all-real scaled completion, rational
  specialization, rational estimate, and explicit-provider estimate retain
  the original checked proof scripts.
- `GramEndpointCriterion`: the raw signed inverse-Gram cofinal equivalence
  and RH consumer retain the original checked proof scripts.

The recovery adds 12 public theorems and one definition. It preserves the
mathematical content of the remaining original statements through the current
published definitions and canonical results, without duplicate aliases.
The further endpoint-gap module below adds seven theorems, for a combined
19 new theorems and one definition.

## Coverage of the original twenty statements

| Original item | Integrated coverage |
|---|---|
| 1, general bounded test | `ParetoL1DualTest.lean`: `Pareto.inner_le_l1_of_sequence_abs_le_one` |
| 2, explicit sign test | `firstPointSignTest_abs_le_one` and `firstPointSignTest` |
| 3, first-coordinate L1 gap | The sign-test proof now supplies the canonical `odd_orthogonal_first_le_negativeMass`; `oddIndicator = 2 • residueAtom 0` and `hilbertNegativeMass_eq` give the original formulation |
| 4, overshoot nonnegative | `hilbertNegativeMass_nonneg` applied to the current `projectionOvershoot` definition |
| 5, finite first-coordinate detector | `projectionResidual_odd_inner`, `odd_orthogonal_first_le_negativeMass`, and `projectionOvershoot_first_lower` |
| 6, coordinate convergence | Existing `one_sub_projection_first_tendsto` plus the recovered finite coordinate identity |
| 7, full negative-part sum | Definitional equality of current `projectionOvershoot` and `hilbertNegativeMass` |
| 8, vanishing overshoot iff zero residual | Existing `overshoot_tendsto_iff_residual_zero` |
| 9, RH consumer | Existing `riemannHypothesis_of_projectionOvershoot_tendsto_zero` |
| 10, finite coordinate identity | Recovered `projectionResidual_first_eq_one_sub_projection` |
| 11, full positive-part sum | Recovered `projectionOvershoot_eq_tsum_positive_projection` |
| 12, positive first-coordinate detector | Existing `projectionOvershoot_first_lower` |
| 13-14, critical overshoot endpoint | Recovered cofinal endpoint equivalence and RH consumer |
| 15-18, scaled/rational dyadic completion | All four original declarations in `FiniteDyadicEndpoint` |
| 19-20, raw mixed Gram condition | Both original declarations in `GramEndpointCriterion` |

## Exact finite equality

For the actual complete-Pareto projections, with unscaled
`D f(n) = f(floor(n/2))`,

    (2t-1) δ_(2M) = (t²/2) δ_M + t r_(2M)(1)
                     - ||r_(2M) - t D r_M||².

The kernel interface writes the unscaled operator as
`(1/2) • doubleDilation`. No signed term, boundary contribution, or remainder
square is discarded in this primary result.

## Conditional research reductions and open obligations

The raw Gram criterion and the cofinal overshoot endpoint are implications
for actual optimizers under the full infinite Pareto law and all conductors.
Open: prove the actual cofinal arithmetic Gram lower bound or the actual
overshoot upper bound. Neither the preserved verification nor this integration
discharges those hypotheses. No RH proof or formal RH-to-closure converse is
claimed here.

The integrated source must pass the mandatory server checkpoint before
publication. Original-source verification does not certify the changed import
graph or integrated current-main proof scripts.

## Supporting-module layout

The recovered bounded-test theorem lives in `RH/ParetoL1DualTest.lean`.
`RH/ThresholdHilbertL1.lean` is unchanged from the starting main revision.
The application imports the new owner explicitly, and the aggregate exports it.
No existing declaration is relocated and no compatibility wrapper is introduced.
The current-main module/axiom check and the final checkpoint are separate gates.

## Further exact endpoint-gap results

The new `RH/ParetoOvershootEndpointGap.lean` retains the exact slack in the
bounded sign test. Write `r` for the limiting residual, `delta = ||r||^2`,
`omega = NegMass(r)`, and `T = (sqrt(2)/2) doubleDilation`, the normalized
dyadic isometry. Let `h` be `firstPointSignTest` and set

    G = ||r||_1 - <r,h> >= 0,
    a = 1 - sqrt(2)/2,
    b = (3 sqrt(2) - 4)/4 > 0.

The primary result is the complete equality

    omega - a delta = G/2 + (sqrt(2)/4) ||r - T r||^2.

At each positive finite stage, the corresponding equality is

    omega_n - a delta_n + finiteDyadicDefect(n)/2
      = G_n/2 + (sqrt(2)/4) finiteDyadicResidualRemainder(n).

The finite signed defect is retained. The first-coordinate contribution to
the full mismatch square gives the verified quantitative bounds

    omega >= a delta + (sqrt(2)/8) r(1)^2
          >= a delta + b delta^2.

Consequently an explicit estimate `omega <= a delta + eta` implies
`b delta^2 <= eta`. This is a quantitative conditional consumer; it does not
supply an arithmetic upper estimate for the actual overshoot. The additional
quadratic term refines the previously checked critical endpoint and quantifies
the obstruction when the remaining residual energy is positive.

## Recovered verification evidence

The interrupted connection was recovered without discarding the workspace.
The combined current-main module and axiom check succeeded as
`job_1WyiVS9Kkn58zTabjBDa399JcV-CsGAT`.
The seven new endpoint-gap declarations and all seven axiom checks succeeded
as `job_qiE3BO2Vyy78TlZUs_CXtOgzC3Vp75NW`; each uses only `propext`,
`Classical.choice`, and `Quot.sound`.
These targeted checks are distinct from the mandatory final checkpoint,
which validates the complete unpublished delta and aggregate before publication.

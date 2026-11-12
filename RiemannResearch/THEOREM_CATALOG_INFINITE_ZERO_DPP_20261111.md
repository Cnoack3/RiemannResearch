# Infinite zero-ordinate FMZ DPP and pair-transfer catalog

Research note: [FMZ_Infinite_Zero_DPP_20261111.md](FMZ_Infinite_Zero_DPP_20261111.md).
Starting revision: 8d91c2e44fa978205f4d8b4a59a636398f4bca9d.

## Established finite and infinite constructions

* Probability/DeterminantalPairTransfer.lean:
  pairDefect_exact, IsDPP.pairDefect_bounds,
  pairMass_sub_expected_exact, IsDPP.pairMass_error_le,
  pairVacancyBudget_eq_degrees, IsDPP.pairStatistic_integrable,
  IsDPP.expected_pairStatistic, IsDPP.pairStatistic_error_le,
  IsDPP.totalVacancy_bounds, IsDPP.pairVacancyBudget_le_count.
* Probability/ZeroOrdinateInfiniteDPP.lean:
  bounded_sites_finite, selected_sites_locally_finite, enumeration_surjective,
  limitingLaw_probability, limitingLaw_isDPP, kernel_tendsto,
  inclusion_tendsto, vacancy_eq_projection_residual, limitingLaw_two_point,
  cutoffVector_coordinate, collision_projection_eq,
  collision_pair_probability_zero, ordinate_injective_ae,
  collision_vacancy_lower, zero_pair_transfer_bound.
  The ground set is all actual positive zeta zeros with analytic multiplicity.
  Neither RH nor distinct-ordinate nor Selberg assumptions are used.

## Conditional research reduction

Analysis/PairVacancyMoment.lean:
count_vacancy_young, integral_pair_error_le, tendsto_zero_of_young_bounds,
integral_tendsto_zero_of_vacancy.

The last theorem assumes the displayed integrability conditions, a positive
uniform third-moment majorant, and convergence to zero of the averaged
vacancy. It proves disappearance of the averaged pair-statistic error.
It does not prove these hypotheses for a moving zeta-zero model.

Open providers:
* Published Fujii local count moments: external input, not newly formalized.
* Averaged actual projection-vacancy decay in microscopic moving windows.
* Sine pair limit for the same auxiliary zero-label family.
* Required height-window, measurability, and tail assembly for full PCC.

The optimized square-root rate, higher-moment Holder rate, finite-rank trace
obstruction, and full weak-process interpretation are paper deductions in the
note. No unconditional PCC, RH, or full GUE theorem is claimed.

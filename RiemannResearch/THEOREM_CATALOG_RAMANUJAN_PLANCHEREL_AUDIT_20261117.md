# Theorem catalog: corrected Ramanujan–Plancherel audit

Date: 2026-11-17.

[Full audit and research continuation](RAMANUJAN_PLANCHEREL_A1_A2_AUDIT_20261117.md).

Source: [89-page audited revision and supplement](https://drive.google.com/file/d/1DHIp4gGwApIL1V6nHwV4HDxuOAFdijwG/view), main section 8, supplement sections 11.2 and 21–23. The source's section 2.2 uniform-energy justification is invalid; the claimed bound is unproved.

This catalog covers 56 named theorems and eight definitions in six modules, all exported from RiemannResearch.lean. General finite identities are established with their stated algebraic hypotheses. The RH implications are **conditional research reductions**, not proofs of the energy hypotheses or RH.

## Domain-specific obligation status

| Obligation | Status |
| --- | --- |
| Uniform/cofinal bound on actual exact-head atom energy | Open; sufficient for RH |
| Absolute low-conductor decay after retaining the q_x factor | Open under the cited inputs; no automatic q_x<=1 |
| Actual arithmetic signed-return curvature bound | Open |
| Physical-window identification of the original z_Y field with activated coordinates | Discharged with prime coverage, p<=x<2p, and Y<p^2; full correction retained beyond the window |
| A1, A2, and RH | Not proved |

## RamanujanFinitePlancherel.lean

Namespace: RiemannResearch.RH.Pareto.RamanujanFinitePlancherel.

Squarefree conductor kernel, complete Plancherel, inversion, and exact mass remainder.

| Declaration | Kind |
| --- | --- |
| [primeContrast](RH/RamanujanFinitePlancherel.lean#L20) | Definition |
| [totient_prime_product](RH/RamanujanFinitePlancherel.lean#L22) | Checked finite/structural theorem |
| [conductor_kernel_product](RH/RamanujanFinitePlancherel.lean#L33) | Checked finite/structural theorem |
| [squarefree_prime_factors_ext](RH/RamanujanFinitePlancherel.lean#L54) | Checked finite/structural theorem |
| [conductor_kernel_off_diagonal](RH/RamanujanFinitePlancherel.lean#L66) | Checked finite/structural theorem |
| [conductor_kernel_diagonal](RH/RamanujanFinitePlancherel.lean#L91) | Checked finite/structural theorem |
| [conductor_kernel](RH/RamanujanFinitePlancherel.lean#L117) | Checked finite/structural theorem |
| [transform](RH/RamanujanFinitePlancherel.lean#L126) | Definition |
| [transform_one](RH/RamanujanFinitePlancherel.lean#L129) | Checked finite/structural theorem |
| [polarized_plancherel](RH/RamanujanFinitePlancherel.lean#L133) | Checked finite/structural theorem |
| [corrected_plancherel](RH/RamanujanFinitePlancherel.lean#L173) | Checked finite/structural theorem |
| [nontrivial_conductor_energy](RH/RamanujanFinitePlancherel.lean#L178) | Checked finite/structural theorem |
| [omitted_conductor_identity_iff](RH/RamanujanFinitePlancherel.lean#L189) | Checked finite/structural theorem |
| [transform_inverse](RH/RamanujanFinitePlancherel.lean#L201) | Checked finite/structural theorem |
| [weighted_mass_remainder](RH/RamanujanFinitePlancherel.lean#L240) | Checked finite/structural theorem |
| [weighted_mass_sq_le](RH/RamanujanFinitePlancherel.lean#L266) | Checked finite/structural theorem |

## ExactHeadRamanujanPlancherel.lean

Namespace: RiemannResearch.RH.ExactHeadRamanujanPlancherel.

Internal gcd coordinates and the actual optimizer's corrected conductor energy.

| Declaration | Kind |
| --- | --- |
| [gcdScore](RH/ExactHeadRamanujanPlancherel.lean#L23) | Definition |
| [conductorScore](RH/ExactHeadRamanujanPlancherel.lean#L26) | Definition |
| [ramanujanSum_gcd_period](RH/ExactHeadRamanujanPlancherel.lean#L29) | Checked finite/structural theorem |
| [atom_ramanujan_synthesis](RH/ExactHeadRamanujanPlancherel.lean#L36) | Checked finite/structural theorem |
| [conductorScore_prefix](RH/ExactHeadRamanujanPlancherel.lean#L49) | Checked finite/structural theorem |
| [conductorScore_one](RH/ExactHeadRamanujanPlancherel.lean#L63) | Checked finite/structural theorem |
| [conductorScore_nontrivial](RH/ExactHeadRamanujanPlancherel.lean#L71) | Checked finite/structural theorem |
| [conductorScore_primitive](RH/ExactHeadRamanujanPlancherel.lean#L85) | Checked finite/structural theorem |
| [corrected_exact_head_plancherel](RH/ExactHeadRamanujanPlancherel.lean#L102) | Checked finite/structural theorem |
| [nontrivial_exact_head_energy](RH/ExactHeadRamanujanPlancherel.lean#L120) | Checked finite/structural theorem |
| [lower_gcd_score_sum](RH/ExactHeadRamanujanPlancherel.lean#L136) | Checked finite/structural theorem |
| [beta_sq_le_lower_score_energy](RH/ExactHeadRamanujanPlancherel.lean#L153) | Checked finite/structural theorem |
| [atomResidual_upper_score](RH/ExactHeadRamanujanPlancherel.lean#L164) | Checked finite/structural theorem |
| [atomResidual_plancherel](RH/ExactHeadRamanujanPlancherel.lean#L172) | Checked finite/structural theorem |

## ExactHeadEnergyAudit.lean

Namespace: RiemannResearch.RH.Pareto.ExactHeadEnergyAudit.

Conditional RH reduction; the uniform/cofinal energy bound remains Open.

| Declaration | Kind |
| --- | --- |
| [zero_coefficients_not_exact_head](RH/ExactHeadEnergyAudit.lean#L20) | Checked finite/structural theorem |
| [atom_energy_lower_bound_at_zeta_zero](RH/ExactHeadEnergyAudit.lean#L26) | Checked finite/structural theorem |
| [riemannHypothesis_of_cofinal_atom_energy_bound](RH/ExactHeadEnergyAudit.lean#L51) | Conditional RH reduction |
| [riemannHypothesis_of_primorial_atom_energy_le_one](RH/ExactHeadEnergyAudit.lean#L82) | Conditional RH reduction |
| [riemannHypothesis_of_paper_atom_energy_bound](RH/ExactHeadEnergyAudit.lean#L91) | Conditional RH reduction |

## FiniteWeightedReturnDrift.lean

Namespace: RiemannResearch.Analysis.FiniteWeightedReturnDrift.

Finite normal equations, rank-one updates, and endpoint drift.

| Declaration | Kind |
| --- | --- |
| [endpoint_covariance](Analysis/FiniteWeightedReturnDrift.lean#L20) | Checked finite/structural theorem |
| [endpoint_energy](Analysis/FiniteWeightedReturnDrift.lean#L41) | Checked finite/structural theorem |
| [curvature_energy_eq_prefix](Analysis/FiniteWeightedReturnDrift.lean#L61) | Checked finite/structural theorem |
| [signed_update_telescope](Analysis/FiniteWeightedReturnDrift.lean#L74) | Checked finite/structural theorem |
| [accessible_drift_realized](Analysis/FiniteWeightedReturnDrift.lean#L90) | Checked finite/structural theorem |
| [rank_one_normal_update](Analysis/FiniteWeightedReturnDrift.lean#L128) | Checked finite/structural theorem |

## ExactHeadAtomReturnMoments.lean

Namespace: RiemannResearch.RH.ExactHeadAtomReturnMoments.

Activated gcd-atom moments and three-label return curvature.

| Declaration | Kind |
| --- | --- |
| [prefixMoment](RH/ExactHeadAtomReturnMoments.lean#L21) | Definition |
| [upperDivisorSignal](RH/ExactHeadAtomReturnMoments.lean#L24) | Definition |
| [activatedMoment](RH/ExactHeadAtomReturnMoments.lean#L27) | Definition |
| [prefixMoment_zero_above_cutoff](RH/ExactHeadAtomReturnMoments.lean#L31) | Checked finite/structural theorem |
| [upperDivisorSignal_mem](RH/ExactHeadAtomReturnMoments.lean#L39) | Checked finite/structural theorem |
| [prefix_pairing_synthesis](RH/ExactHeadAtomReturnMoments.lean#L51) | Checked finite/structural theorem |
| [upperDivisorSignal_prefix](RH/ExactHeadAtomReturnMoments.lean#L66) | Checked finite/structural theorem |
| [endpoint_divisor_signal](RH/ExactHeadAtomReturnMoments.lean#L88) | Checked finite/structural theorem |
| [endpoint_signal_difference](RH/ExactHeadAtomReturnMoments.lean#L101) | Checked finite/structural theorem |
| [triple_curvature_moment](RH/ExactHeadAtomReturnMoments.lean#L117) | Checked finite/structural theorem |

## ExactHeadPhysicalReturn.lean

Namespace: RiemannResearch.RH.ExactHeadPhysicalReturn.

Physical prime signals, the exact lower-class correction, safe-window activated moments,
and the actual optimizer's complete tail return. No asymptotic energy bound is assumed.

| Declaration | Kind |
| --- | --- |
| [gcd_eq_prime_iff_before_square](RH/ExactHeadPhysicalReturn.lean#L36) | Checked finite/structural theorem |
| [prime_atom_eq_one](RH/ExactHeadPhysicalReturn.lean#L59) | Checked finite/structural theorem |
| [upperDivisorSignal_eq_grid_sub_atom](RH/ExactHeadPhysicalReturn.lean#L74) | Checked finite/structural theorem |
| [upperDivisorSignal_zero_head](RH/ExactHeadPhysicalReturn.lean#L108) | Checked finite/structural theorem |
| [upperDivisorSignal_eq_grid_sub_one](RH/ExactHeadPhysicalReturn.lean#L115) | Checked finite/structural theorem |
| [physicalSignal](RH/ExactHeadPhysicalReturn.lean#L126) | Definition |
| [physical_pairing_upper](RH/ExactHeadPhysicalReturn.lean#L129) | Checked finite/structural theorem |
| [physicalSignal_with_reentry](RH/ExactHeadPhysicalReturn.lean#L145) | Checked finite/structural theorem |
| [physicalSignal_eq_activatedMoment](RH/ExactHeadPhysicalReturn.lean#L160) | Checked finite/structural theorem |
| [primorial_physicalSignal_eq_activatedMoment](RH/ExactHeadPhysicalReturn.lean#L176) | Checked finite/structural theorem |
| [physicalSignal_eq_endpoint](RH/ExactHeadPhysicalReturn.lean#L185) | Checked finite/structural theorem |
| [atomResidual_physicalSignal_eq_tail](RH/ExactHeadPhysicalReturn.lean#L201) | Checked finite/structural theorem |
| [square_cutoff_requires_reentry](RH/ExactHeadPhysicalReturn.lean#L241) | Checked finite/structural theorem |

## Verification

The audit records the successful component jobs and BuildBuddy invocations. Publication requires the managed full-project Bazel/BuildBuddy checkpoint; its terminal result supplies the exact published commit and integration evidence. A component import check alone is not a full-project checkpoint.

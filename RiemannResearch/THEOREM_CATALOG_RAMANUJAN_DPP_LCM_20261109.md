# Ramanujan projection laws and LCM target vacancy

## Finite identities

| Declaration | Content |
| --- | --- |
| `projectionObservationLaw_vacancy` in namespace `RiemannResearch.Probability.DPP` | An orthogonal projection observed on a finite orthonormal family gives a DPP on the observation labels. The vacancy at a label is the squared norm of its observation's projection residual. |
| `quotientTarget_basis`, `quotient_projection_eq_lcmBest` | The weighted residue quotient has coordinates at the positive representatives $1,\ldots,L$, with the multiples class last. Its unit constant target can be a coordinate of an orthonormal basis. The quotient projection agrees with the complete Pareto projection onto the full divisor dictionary. |
| `lcm_probe_vacancy_eq_packet_determinant` | With $H_L$ the complete packet Gram and $\Lambda_L(q)=\Lambda(q)$, the constant-target vacancy is $\det(H_L-\Lambda_L\Lambda_L^{\mathsf T})/\det H_L=E_M$. |
| `quotientZero_orthogonal_legal`, `quotientMultiples_orthogonal_legal`, `quotientMultiples_orthogonal_zero` | Grouped zero rows are lifted with a zero multiples coordinate. Positive-half-plane zeros away from the pole give pairwise orthogonality of the three spaces. |
| `lcm_augmented_probe_vacancy`, `lcm_probe_vacancy_split` | The augmented vacancy is exactly $\mathcal R_M$, using the span projection at singular Gram stages. The unaugmented vacancy is the sum of multiples mass, grouped certificate energy, and augmented vacancy. |
| `packetMode_projection_eq_residueMode`, `integerKernel_eq_packetInverseGram`, `kernel_eq_packetFrequencyKernel`, `kernel_eq_packetMode_sum` | Gram–Schmidt on the packets spans the same natural prefix as the residue modes. The integer and Mellin kernels admit the complete packet inverse-Gram expressions. The integer first-site observation uses the Möbius packet values. |
| `kernel_diagonal_re_eq_envelope`, `mellinWindowCount_hole_bounds_envelope` | For a measurable frequency window, its mean count is $A=\int \lvert\zeta(1/2+it)/(1/2+it)\rvert^2\operatorname{Re} A_N(t,t)\,dt/(2\pi)$. The hole probability is between $1-A$ and $e^{-A}$. The count uses the Mellin sampling law. |
| `phaseStrippedPairDet_eq_gram`, `phaseStrippedPairDet_microscopic_tendsto`, `phaseStrippedPairDet_eventually_ge` | For a moving pair with vanishing entrywise error budgets, the complex grouped determinant tends to $1-\lvert K(v)\rvert^2$ at scaled gap $v$. A nonzero limiting gap gives an eventual lower bound of half that limit. |

The vacancy formulas use all nontrivial divisors of $L=\operatorname{lcm}(1,\ldots,M)$. The packet-mode kernels use the natural prefix. These stages can differ even at $M=3$, where $6$ belongs to the LCM dictionary.

## Conditional research reductions

- `lcm_shifted_trial_norm_sq` gives the exact identity
  $$\|\mathrm{errorVector}(f)-\mathrm{certificateVector}\|^2
  =\mathcal R_M+\|f-\mathrm{lcmBest}(M)\|^2.$$
  For fixed distinct positive critical-line zeros, `riemannHypothesis_of_lcm_shifted_trials` applies to a cofinal family of legal trials with a vanishing upper budget on the left.
- `critical_certificate_energy_bounds_of_microscopic` bounds the real grouped projection using both signed frequencies in the comparison rows. The upper bound for $\ell C$ is the relative source square divided by $1/2-d$ when every comparison row budget is at most $d<1/2$. `critical_certificate_tendsto_of_microscopic` gives $C_j\to0$ under a uniform margin and relative source square $o(\ell_j)$.
- `riemannHypothesis_of_cofinal_augmented_vacancy` applies to moving finite families when their certificate energies and augmented vacancies both tend to zero on the same cofinal schedule.

The open arithmetic obligation is an upper bound forcing the complete augmented vacancy to zero. A microscopic real row bound controls the certificate term. A clustered complex pair determinant is a bound on a different matrix.

## Continuation: automatic source decay and legal packet refits

- `microscopicRealRowBudget_card_le` and `card_div_log_le_of_microscopic`
  prove the counting premise proposed in the handoff: a row bound d controls
  m/log(N+1) by d/2, including empty families.
- `relativeCriticalSourceSq_div_log_le_of_microscopic` gives the explicit
  bound S/ell <= C0/(2 ell) + (d/2)e(4+e), using the actual-zero reciprocal sum.
- `critical_certificate_tendsto_of_microscopic_actual_zeros` removes the
  separate source-decay hypothesis for cofinal periods and moving distinct
  positive actual critical-line zeros. **Open:** an eventual uniform
  microscopic row margin d<1/2 for the chosen moving schedule.
- `lcm_moving_remainder_tendsto_limit_of_microscopic` identifies the remaining
  vacancy limit with the squared distance to the full legal closure.
- `riemannHypothesis_of_microscopic_remainder_upper` and
  `riemannHypothesis_of_microscopic_shifted_trials` assemble the strengthened
  certificate theorem with the complete LCM criterion.
  **Open:** a complete remainder or shifted-trial upper budget tending to zero.
- `lcmPacketRefit_mem`, `lcmPacketRefit_error_completion`, and
  `lcmError_le_packet_refit` construct a legal screened-packet correction and
  retain its exact Rayleigh gain and displacement from the enlarged optimizer.
- `lcm_remainder_packet_refit_transition` retains both signed changes in
  multiples mass and zero-certificate energy when stages and zero families change.
  **Open:** quantitative control of accumulated gains sufficient for vanishing error.

Source modules: `RH/ParetoResidueMicroscopicSource.lean`,
`RH/ParetoLCMMicroscopicRemainder.lean`, and `RH/ParetoLCMVariational.lean`.
See [the continuation record](Microscopic_Source_and_LCM_Refits_20261109.md)
for hypotheses, external calculations, and published references.

# Squarefree primorial displacement and CRT carries

Source: the user-provided *Squarefree projection displacement and infinite
CRT carries*, 9 November 2026, Sections 6–13. The companion Lean modules
implement the complete primorial stages and the conditional closing tests.
They use the cutoff-indexed period `primorial (n + 3)` from
`SquarefreeStageExhaustion`. Repeated periods between primes give the same
finite space. Every squarefree conductor eventually divides these periods.

## Established identities and convergence

| Agenda item | Lean module and declarations | Content |
| --- | --- | --- |
| 1 | `QPrimorialMatchedDisplacement` — `normalizedPairing_deficit`, `normalizedPairing_tail_bound`, `normalizedPrimePairing_tendsto`, `normalizedPeriodPairing_tendsto` | The complete signed pairing detects the Pareto residual energy along any cofinal included conductor. The whole period itself is an admissible probe with absolute error at most its inverse square root. |
| 1 | `QPrimorialMatchedGram` — `paretoCoefficients_normal`, `stageDisplacement_expansion`, `normalizedPairing_gram`, `normalizedLargestPrimePairing_tendsto` | The coefficients are the difference of the two complete inverse-Gram solves on the same divisor list. |
| 2 | `QPrimorialPrimeCarry` — `schurForcing_exact`, `schur_equation`, `schurForm_coercive`, `primeComponent_tendsto` | The finite Pareto carry solve is retained in the test lift. The form has lower bound `zetaTwo / 2` in Q coordinates, and the finite prime component tends to the actual prime component. |
| 3 | `QEuclidCarryRay` — `conductor_squarefree`, `carryBranch_eq_weighted_floor`, `sum_infinite_branches`, `branches_pareto_norm_summable`, `projected_carry_sum_ne_zero` | Every squarefree root admits a geometrically controlled ray in both complete norms. A composite root leaves a nonzero projected carry sum. |
| 3 | `QPrimorialRayAssembly` — `canonical_telescope`, `exists_diagonal_branch_decomposition` | The inhomogeneous weights are the actual coefficient differences. A stage-dependent common depth gives boundary norm below `2^(-n)` and the signed sum tends to the actual displacement. |
| 4 | `QPrimorialMatchedDisplacement` — `metricGap_exact`, `metricGap_pos`, `metricGap_tendsto` | The exact gap is the squared Pareto displacement plus the Q residual's metric correction. It is strictly positive at every finite stage and tends to `zetaTwo * inner ℝ qOne witness`. |
| 5 | `QSquarefreeWitnessHead` — `prime_anchor_exact`, `prime_anchor_witness_tail` | The explicit squarefree trial with any prime anchor above the head gives an exact signed tail pairing for the faithful witness. |
| 6 | `QFiniteForcingData`, `QParetoMetric`, `QSquarefreeDisplacementRigidity`, `QPrimeCarryProjection` | The generalized forcing formula reuses the physical tail estimate. The existing metric identity, faithful witness, prime detector and projected-carry span apply to the same squarefree closure. |

## Conditional research reductions

- **Open** — a cofinal upper bound approaching zero for the normalized
  complete Gram row. The conditional conclusion is
  `QPrimorialMatchedDisplacement.riemannHypothesis_of_cofinal_normalizedPairing`.
- **Open** — a cofinal upper bound approaching zero for the complete signed
  Schur forcing on the unit prime tests. The conditional conclusion is
  `QPrimorialPrimeCarry.displacement_zero_of_cofinal_schurForcing`.
- **Open** — a signed estimate forcing the combined prime contribution of
  the diagonal branch assembly to vanish. The boundary estimate is
  unconditional.
- **Open** — arbitrarily small cofinal upper bounds for the complete metric
  gap. The conditional conclusion is
  `QPrimorialMatchedDisplacement.residual_zero_of_cofinal_metricGap`.
- **Open** — a complete tail bound for the prime-anchor trial and the faithful
  witness. The conditional conclusion is
  `QSquarefreeWitnessHead.residual_zero_of_prime_anchor_witness_tail`.
  Membership of the displacement in the prime span alone leaves the
  prime component as a separate target.

## External finite interval evidence

The following enclosures are in units of one millionth. The pairing is
`zetaTwo * p * inner ℝ (qResidue p) d_j` for the largest prime divisor of
the stage period. All endpoints are rounded outwards.

| Period | Prime | Normalized pairing interval | Pareto squared residual interval |
| ---: | ---: | ---: | ---: |
| 6 | 3 | [25913, 26978] | [78118, 78469] |
| 30 | 5 | [28348, 32273] | [37082, 37886] |
| 210 | 7 | [18459, 28183] | [24671, 26197] |
| 2310 | 11 | [4991, 34524] | [18970, 22372] |

These computations use the unnormalized Q masses, so the factor
`zetaTwo` is already present in the Gram row. In a residue class
represented by `1 ≤ a ≤ L`, sum 128 terms and put `x = a + 128L`.
The Q tail lies in `[1/(Lx), 1/(Lx) + 1/x²]`. The Pareto tail lies
in `[1/(L(x+1)), 1/(Lx) + 1/(x(x+1))]`. These follow by integral
comparison for positive decreasing weights. Use fixed-point integer
intervals with denominator `10^32` and round outwards at every
operation. For each complete interval system `Ac=b`, choose a rational
approximate inverse `R` of the midpoint matrix and a rational approximate
solution `c₀`. Bound `β = ‖I-RA‖∞ < 1` and use
`‖c-c₀‖∞ ≤ ‖R(b-Ac₀)‖∞/(1-β)` before forming the signed Gram row.
The Q and Pareto bounds for `β` at period 2310 are 0.001666 and 0.001670.

The intervals certify positivity at these finite stages. They are
external arithmetic evidence. The cofinal upper bound and vanishing of
the actual residual remain open.

## 10 November 2026: stronger certificates

The follow-up [research note](SquarefreeCRTPrioritiesStrengthening20261110.md)
maps all six priorities and records the exact new hypotheses.

| Priorities | New module | Strengthening |
| --- | --- | --- |
| 1 | `QPrimorialPairingRefinement` | Uniform little-o error at scale inverse square root of the included conductor; finite nonpositive-pairing bound `E_n <= 1/m`. |
| 2, 4 | `QPrimorialSchurEnergy` | Coercivity constant improves to `30*zetaTwo/59`; one scalar self-forcing energy detects displacement vanishing; exact gap retains the carry and metric remainders. |
| 1, 2, 4 | `QPrimorialSchurCertificate` | Completion-of-square identity and rigorous upper/lower bounds on the actual scalar energy from an approximate trial and its complete dual residual bound. |
| 3 | `QPrimorialRayProjection` | Actual projected branch limits; a diagonal making both vector and normalized moving-conductor boundaries negligible. |
| 5 | Existing `QSquarefreeWitnessHead` | The exact prime-anchor witness identity is retained and rechecked. No actual growth or tail-product provider has been proved. |
| 6 | All four modules exported | 29 new theorem declarations, with full-project server validation required before publication. |

**Open:** cofinal smallness of the complete Gram row, scalar Schur energy,
approximate-certificate upper endpoint, or witness tail product. None of
the new boundary or positivity theorems is asserted to discharge these
arithmetic obligations.

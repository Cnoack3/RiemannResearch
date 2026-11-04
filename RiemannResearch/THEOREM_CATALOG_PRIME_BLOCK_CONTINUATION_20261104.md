# Prime-block continuation — final verification catalog, 4 November 2026

This catalog supersedes the staged scope notes in earlier checkpoints. All named modules below are published and project-checked. No proof of RH is claimed.

## New actual arithmetic theorems

- `RH/FinitePrimeDerivativeProjection.lean` and `RH/QPrimeDerivativeProjection.lean`: exact finite tensor derivative optimizer, normal equations, complete physical Q error, and full squared-norm remainder.
- `RH/FinitePrimeDerivativeExpansion.lean`, `RH/QPrimeDerivativeAtoms.lean`, and `RH/QPrimeDerivativePrimitive.lean`: explicit subset coefficients, actual divisor-atom interface, finite legal membership, exact physical derivative, and minimization against every finite coefficient vector. Only primality and distinctness of the finite prime family are assumed.
- `RH/QPrimeDerivativePeriodMean.lean`: exact actual full-period sum qL²/(2M), with every signed divisor identity discharged.
- `RH/QPrimeDerivativeEnergyNoGo.lean`: actual full norm bound ‖F‖²≥q³L/(4M²), unconditional norm-squared divergence along the first primes, and no uniform energy budget. This is an arithmetic no-go for the explicit derivative-optimal primitives, not for arbitrary legal approximants.
- `RH/QPrimeValuationFactorLegality.lean`: radical-compatible one-prime factors collapse on positive valuation levels; every odd-prime factor is constant. A nonzero legal such factor implies target closure/RH, so its existence remains Open.
- `RH/QValuationConditionalLegality.lean`: the actual orthogonal projection of g_p onto its own valuation subspace is illegal at every odd prime.
- `RH/QParityFactorLegality.lean`: exact parity decomposition φ(1)1+2(φ(0)−φ(1))g₂, legality iff legality of φ(1)1, and conditional RH implication when the even value is nonzero.
- `RH/QPeriodicRationalTail.lean`, `Analysis/ArithmeticProgressionSquareTail.lean`, and `Analysis/ArithmeticProgressionSquareSeries.lean`: finite telescoping, summability, complete infinite tails, and the actual Q-Hilbert periodic error bound.
- `RH/ZetaTwoElementaryRationalBounds.lean`: 29/18<ζ(2)<5/3 for the full series.
- `RH/QPeriodSixActualCertificate.lean`: actual legal trial g₂+g₃+(2/3)g₆ has complete squared Q error <1/16.
- `RH/QPeriodThirtyActualCertificate.lean`: actual legal trial g₂+g₃+(4/5)g₅−(1/5)g₆+(1/5)g₁₅+(1/5)g₃₀ has complete squared Q error <27/1000, improving <1/32.

## Conditional reductions and auxiliary theorems

- `RH/QPrimorialPacketGain.lean`: actual monotone cofinal packet errors; exact recurrence/product/exponential bounds; legal closure iff relative packet gains are nonsummable; RH consumers allowing a nonsummable benchmark with a summable nonnegative deficit. The actual gain lower estimate remains Open.
- `RH/QPrimorialRelativeGain.lean`: added `riemannHypothesis_of_prime_lower_with_summable_defect`; its local arithmetic lower bound remains a hypothesis.
- `Analysis/ResidualGainCounterexample.lean`: explicit positive gains r_n=1/(n+2)² and exact error E_n=(n+2)/(2(n+1))≥1/2. Abstract counterexample only; not an arithmetic counterexample to the primorial gains.
- `Analysis/DirectionalGainCertificate.lean`: exact directional projection remainder and robust lower estimates without matrix inversion.
- `LinearAlgebra/DerivativeOptimizerPeriodMean.lean`: generic signed finite-sum and weighted Cauchy interfaces. Their inputs for the actual primitive are now discharged by the arithmetic modules above.
- `NumberTheory/PrimeProductEnergyGrowth.lean`: exact L/4^m product and geometric lower bound (3/8)(5/4)^(m−2), divergence, and explicitly conditional arbitrary-energy consumers.
- `RH/QPrimeBlockCertificates.lean`: exact rational data and conditional complete-energy consumers. The actual trial norm upper bounds are separately instantiated above.

## Mathematical proofs and remaining research

The companion research note `RH/PrimeBlockProductResearch20261104.md` proves the radical-measurable derivative-closure identity, derivative and pointwise convergence via Euler's product, singularity of the auxiliary infinite product law, the global regularization budget dichotomy, a stronger target-error lower bound, the period-six optimizer lower bound, and the resulting relative gains >3/4 and >53/125. These additional claims have the mathematical-proof scope identified in the report; they are not all new Lean theorems.

The decisive Open premises are (i) nonsummable actual projection gains, possibly in cofinal packets and with summable defects; or (ii) a bounded coupled regularized spectral/primitive-energy budget. Equality of the legal closure with the full radical-compatible primitive space is also Open. No counterexample to these RH-sensitive statements is asserted.

Bagchi (2006), Remark 8, DOI 10.1007/BF02829783 supplies the published squarefree closure criterion. Standard Euler products, Hilbert projections, Schur algebra, and inverse-problem theory are cited with their assumptions in the report. In particular, a Tikhonov range assumption is not used to prove its own RH-sensitive premise.

## Successful publication evidence

| Code checkpoint | Commit | Build scope | Build / cache seconds |
|---|---|---|---|
| `job_gT7rSdLM-4cevZ0KV2NdZ6wI2dqv4V9H` | `d3650c09a38a31e84cd23b5e0ac8f6c849796d25` | aggregate + 3 modules | 93.632 / 9.546 |
| `job_8PqEaJmXXCfjsKiqC6vFKKQ71aBWU3Le` | `ced6c556be5458ee9b760e4fb01c5124b6497191` | aggregate + 8 modules | 38.761 / 8.480 |
| `job_RRTZ4P1KaZ-YWhoMA695ofYCbQIwAGHl` | `5e6890c8c1b63619417ae9908aca915b9f1dc057` | aggregate + 4 modules | 45.800 / 8.779 |
| `job_GRtDcKaD03Wu0R5QdNw9B_Qpleq0L_U7` | `d7892b67ff03c20a92f9e07f8be26e9d5dba5adb` | aggregate + 4 modules | 59.684 / 8.451 |
| `job_lyazU0Q2TVb18TGW3v-vHGSQg4imDf7z` | `2987a7e923230dc9153b042f96f5e02c540b988c` | aggregate + 5 modules | 55.549 / 8.527 |

All rows are terminal successes with pushed=true. Their successful candidate checks took 9.383, 9.300, 8.004, 6.548, and 20.188 seconds respectively. These times are server-reported verification, not connection or research duration. Representative axiom reports for all main actual no-go, complete-trial, legality, and conditional-RH statements contained only propext, Classical.choice, Quot.sound. No new axioms, sorry, or admit were used. Wolfram and exact Python computations are diagnostics and are not substituted for these checks.

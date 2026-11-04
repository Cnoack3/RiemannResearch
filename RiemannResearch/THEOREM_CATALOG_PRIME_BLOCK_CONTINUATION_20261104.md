# Prime-block continuation, 4 November 2026

## Conditional research reductions

`RH/QPrimorialPacketGain.lean` identifies the actual nested projection gains on arbitrary monotone cofinal packet endpoints. It proves exact recurrence, finite product and exponential identities, and legal closure iff packet relative gains are not summable. The RH consumer has exactly this unresolved arithmetic premise. A second consumer allows an arbitrary nonnegative nonsummable lower sequence with a summable additive deficit.

`RH/QPrimorialRelativeGain.lean`: `riemannHypothesis_of_prime_lower_with_summable_defect` permits infinitely many prime exceptions, provided their total nonnegative deficit is summable. The actual gain lower bound remains **Open**.

## Established abstract obstruction

`Analysis/ResidualGainCounterexample.lean`: gains r(n)=1/(n+2)^2 are positive and below one, yet the exact residual d(n)=(n+2)/(2(n+1)) stays at least one half. This is an auxiliary scalar counterexample, not a counterexample to actual primorial arithmetic gains.

## Provenance and scope

Bagchi (2006), Remark 8, DOI 10.1007/BF02829783 supplies the published squarefree closure criterion; existing project projection and scalar-product modules supply the formal chain. New arguments are elementary deductions. No all-primes provider or RH proof is asserted.

The coherent candidate passed server job `job_32W99kXvKtxQzNCojDPJwQwZefxacS3o`, verified=true, exit_code=0, 9.383 seconds. Publication requires the subsequent project checkpoint. Axiom inspection of the packet-defect RH consumer and positive-gain counterexample returned only propext, Classical.choice, Quot.sound.

## Checkpoint 1 publication

Published `d3650c09a38a31e84cd23b5e0ac8f6c849796d25` through successful job `job_gT7rSdLM-4cevZ0KV2NdZ6wI2dqv4V9H`. Validation scope: full aggregate plus all three changed modules. Server build: 93.632 s; cache preflight: 9.546 s.

## Finite product projection and prime-coordinate rigidity

- `RH/FinitePrimeDerivativeProjection.lean`: explicit finite Bernoulli tensor derivative solution, normal equations, admissibility, exact captured energy, full remainder, and minimization on the tilted-mean-zero hyperplane.
- `RH/QPrimeDerivativeProjection.lean`: actual complete QHilbert error and full remainder for the Boolean lift of that candidate. These equations do not by themselves assert bounded primitive energy.
- `RH/QPrimeValuationFactorLegality.lean`: all positive valuation levels collapse under radical constraints. At odd primes every such factor is constant, even under the weaker radical-compatible hypothesis. An actual nonzero legal member of a single odd-prime valuation subspace implies target closure and RH; its existence remains Open.
- `RH/QValuationConditionalLegality.lean`: the actual orthogonal projection of g_p onto its own valuation subspace is illegal for every odd prime p. This is an unconditional no-go for coordinate conditioning as a legality-preserving operation.
- `LinearAlgebra/DerivativeOptimizerPeriodMean.lean`: exact signed-sum mean identity under explicit divisor-sum hypotheses, and finite weighted Cauchy energy lower bound. Full primorial primitive divergence remains a paper derivation plus these verified ingredients.
- `Analysis/DirectionalGainCertificate.lean`: exact trial-direction remainder and robust lower bounds without matrix inversion.
- `Analysis/ArithmeticProgressionSquareTail.lean`: elementary finite telescoping bounds for reciprocal-square progression tails.
- `RH/QPrimeBlockCertificates.lean`: exact rational finite data for periods6 and30, plus explicitly conditional complete-energy consumers. Full Q-series assembly is separately proved in the research note and is not silently represented by a finite kernel calculation.

The coherent group passed snippet job `job_F_ZW8CGIhdIbBipEQmSz15ShpUAdr4ZF`, verified=true, exit_code=0, 9.300 s. Representative axiom reports for tensor minimization, physical error, rigidity RH consumer, projection nonlegality, rational certificate, and weighted-energy bound contain only propext, Classical.choice, Quot.sound. Final project acceptance requires the following checkpoint.

## Checkpoint 2 publication

Published `ced6c556be5458ee9b760e4fb01c5124b6497191` through successful job `job_8PqEaJmXXCfjsKiqC6vFKKQ71aBWU3Le`. Validation: aggregate plus all eight changed modules; build 38.761 s, cache preflight 8.48 s. Standalone import issue was corrected before this successful checkpoint.

## Explicit finite legal primitive and parity completion

- `RH/FinitePrimeDerivativeExpansion.lean`: full subset expansion and signed coefficient cancellation of the finite product optimizer.
- `RH/QPrimeDerivativeAtoms.lean`: finite Boolean monomials are actual divisor indicators; lifted derivative atoms equal the physical anchored differences.
- `RH/QPrimeDerivativePrimitive.lean`: explicit finite residue combination is legal for every distinct prime family; its actual derivative is the tensor optimizer, with exact complete Q-error and full remainder against every coefficient vector. No additional arithmetic premise beyond primality and distinctness.
- `RH/QParityFactorLegality.lean`: a radical-compatible parity factor equals φ(1)1+2(φ(0)−φ(1))g₂. Its legality is equivalent to legality of φ(1)1; nonzero even value of a legal factor gives an RH consumer.

Combined candidate job `job_D3VsOapdufZgUWNgrqsqE5x3Csz0Soic` succeeded, verified=true, exit=0, 8.004 s. Inspected axioms for finite legal membership, the full physical remainder, and parity RH consumer contain only propext, Classical.choice, Quot.sound. Publication requires the next project checkpoint. The complete primitive-energy divergence, derivative-closure identity, and regularization dichotomy are mathematical proofs in the accompanying report, not silently asserted by these finite formal interfaces.

## Checkpoint 3 publication

Published `5e6890c8c1b63619417ae9908aca915b9f1dc057` through successful job `job_RRTZ4P1KaZ-YWhoMA695ofYCbQIwAGHl`. Aggregate plus four changed modules; build 45.800 s, cache 8.779 s.

## Actual period mean, complete tails, and scalar escape

- `RH/QPrimeDerivativePeriodMean.lean` proves the actual cumulative primitive over its full product period equals qL²/(2M); all divisor-sum inputs are discharged for a nonempty finite distinct-prime family.
- `Analysis/ArithmeticProgressionSquareSeries.lean` proves summability and complete infinite reciprocal-square progression tail bounds from nonnegative finite telescoping bounds.
- `RH/QPeriodicRationalTail.lean` combines complete tails with the existing exact residue regrouping, yielding an unconditional actual QHilbert error bound for any bounded periodic vector. All omitted mass is retained.
- `NumberTheory/PrimeProductEnergyGrowth.lean` proves L/4^m ≥ (3/8)(5/4)^(m−2) for the first m primes and divergence. Its arbitrary-energy consumer retains an explicit period-energy lower-bound premise.

Combined snippet `job_npUihTYbk-DdwslXZXdCxqoxZV8x6jGw` succeeded, verified=true, exit=0, 6.548 s. Four representative theorem axiom reports contain only propext, Classical.choice, Quot.sound. The next checkpoint determines publication.

## Checkpoint 4 publication

Published `d7892b67ff03c20a92f9e07f8be26e9d5dba5adb` through successful job `job_GRtDcKaD03Wu0R5QdNw9B_Qpleq0L_U7`. Aggregate plus four changed modules; build 59.684 s, cache 8.451 s.

## Complete arithmetic no-go and actual finite trial certificates

- `RH/QPrimeDerivativeEnergyNoGo.lean`: **unconditional actual-Hilbert theorem**, not a scalar consumer: the explicit derivative-optimal primitive satisfies ‖F‖² ≥ q³L/(4M²); its complete norm squared tends to infinity along the first primes, and it has no uniform energy budget. Every period-mean and prefix-to-full-norm input is discharged. This closes the formal scope gap previously noted above for the primitive-energy obstruction. It does not constrain arbitrary legal approximants.
- `RH/ZetaTwoElementaryRationalBounds.lean`: unconditional 29/18 < ζ(2) < 5/3, including the full infinite series.
- `RH/QPeriodSixActualCertificate.lean`: actual legal trial g₂+g₃+(2/3)g₆ has complete squared Q error <1/16.
- `RH/QPeriodThirtyActualCertificate.lean`: actual legal trial g₂+g₃+(4/5)g₅−(1/5)g₆+(1/5)g₁₅+(1/5)g₃₀ has complete squared Q error <27/1000, hence <1/32. These are actual Q norm theorems, not finite-head surrogates.

Combined snippet `job_5UXllW1G6BgyvUekVe4TXiH6-i_Vjmtu` succeeded, verified=true, exit=0, 20.188 s. Axiom inspection of both trial norm bounds, both legal memberships, actual primitive norm divergence and no-budget theorem returned only propext, Classical.choice, Quot.sound. Final publication requires the subsequent checkpoint. No RH proof is asserted: actual nonsummable projection gains or a bounded regularized primitive budget remain Open.

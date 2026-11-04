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

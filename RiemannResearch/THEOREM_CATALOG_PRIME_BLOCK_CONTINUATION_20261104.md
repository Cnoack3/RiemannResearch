# Prime-block continuation, 4 November 2026

## Conditional research reductions

`RH/QPrimorialPacketGain.lean` identifies the actual nested projection gains on arbitrary monotone cofinal packet endpoints. It proves exact recurrence, finite product and exponential identities, and legal closure iff packet relative gains are not summable. The RH consumer has exactly this unresolved arithmetic premise. A second consumer allows an arbitrary nonnegative nonsummable lower sequence with a summable additive deficit.

`RH/QPrimorialRelativeGain.lean`: `riemannHypothesis_of_prime_lower_with_summable_defect` permits infinitely many prime exceptions, provided their total nonnegative deficit is summable. The actual gain lower bound remains **Open**.

## Established abstract obstruction

`Analysis/ResidualGainCounterexample.lean`: gains r(n)=1/(n+2)^2 are positive and below one, yet the exact residual d(n)=(n+2)/(2(n+1)) stays at least one half. This is an auxiliary scalar counterexample, not a counterexample to actual primorial arithmetic gains.

## Provenance and scope

Bagchi (2006), Remark 8, DOI 10.1007/BF02829783 supplies the published squarefree closure criterion; existing project projection and scalar-product modules supply the formal chain. New arguments are elementary deductions. No all-primes provider or RH proof is asserted.

The coherent candidate passed server job `job_32W99kXvKtxQzNCojDPJwQwZefxacS3o`, verified=true, exit_code=0, 9.383 seconds. Publication requires the subsequent project checkpoint. Axiom inspection of the packet-defect RH consumer and positive-gain counterexample returned only propext, Classical.choice, Quot.sound.

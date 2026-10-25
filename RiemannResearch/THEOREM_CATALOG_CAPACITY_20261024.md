## Capacity and signed-energy continuation — 24 October 2026

Research memorandum: [CapacityEnergyResearchAudit20261024.md](RH/CapacityEnergyResearchAudit20261024.md).

Established reusable results:

- `RH/ParetoAmplitudeCertificates.lean`: exact head/tail certificate gap, monotone convergence to complete P energy, explicit accuracy cutoff, and factor-two preservation of regularized reciprocal summability.
- `RH/PrimeBalancedSignedTail.lean`: actual prime-balanced floor identity, complete signed floor and quotient tails, and the first Mertens window.
- `RH/PrimeHeadRefinedCertificates.lean`: actual Q-to-P trial realization and complete P energy identity; raw and regularized finite certificates.
- `RH/SquarefreePrimeHeadStage.lean`: exact finite squarefree packet legality and capacity lower bound from every raw certificate.
- `Analysis/NormalizedSignedEnergy.lean`: exact diagonal plus signed cross decomposition; with divergent mass, convergence is equivalent to vanishing normalized signed cross term.
- `Analysis/RelativeGainSaturation.lean`: quantitative finite lower-bound gain budget and exact defect product.
- `RH/SquarefreeRelativeGainCriterion.lean`: actual squarefree relative-gain nonsummability is equivalent to saturation; positive limiting defect bounds partial gain mass.
- `RH/ActualPrimeHeadSignedCriterion.lean`: least-prime monotonicity, positive actual errors, and equivalence of refined versus actual regularized reciprocal-mass divergence.
- `RH/DensePrimeHeadSignedCriterion.lean`: Bertrand anchor bound, complete error at most 9N, unconditional consecutive-head reciprocal divergence for 9N and refined certificates, exact harmonic-average identity, and diagonal bound 9/H_M.
- `RH/CountermodelExactHeads.lean`: nonarithmetic exact-head Pareto model with zero trial mean, energy N+1, and covariance min(N,M)+1. No arithmetic legality claim.

Conditional research reductions:

- `RH/SquarefreeSignedCorrelationCriterion.lean`: RH from actual finite legality, full energy certificates, reciprocal divergence, and vanishing normalized signed cross budget. **Open:** arithmetic mass and cross inputs for arbitrary chosen families.
- `RH/ActualPrimeHeadSignedCriterion.lean`: actual least-prime family consumer discharges legality and certificate conditions. **Open:** selected mass and signed cross estimates.
- `RH/DensePrimeHeadSignedCriterion.lean`: explicit harmonic and refined dense-head consumers discharge mass divergence. **Open:** normalized signed cross decay; no other arithmetic asymptotic hypothesis in these consumers.
- `RH/SquarefreeRelativeGainCriterion.lean`: RH from divergent lower-bound relative block gain mass. **Open:** actual inverse-Schur gain provider and divergent mass.

Unconditional squarefree saturation and RH remain unproved. No reverse RH-to-squarefree-saturation provider is introduced. Standard axiom audits do not discharge theorem hypotheses.

---

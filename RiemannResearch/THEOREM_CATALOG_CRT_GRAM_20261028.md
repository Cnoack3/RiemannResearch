# CRT Gram minimizers: theorem catalog supplement

28 October 2026. See [research memorandum](RH/CRTGramMinimizersResearch20261028.md).

## Established statements

Module `RH/QCRTGramMinimizer.lean`, namespace `RiemannResearch.RH.QCRTGramMinimizer`:

- `optimizer_feasible`, `completion`, `norm_completion`: actual coprime CRT seed, complete affine feasible set, and target-zero/target-one minimization.
- `energy_schur`, `optimizer_normal`: exact signed Gram equations, with the inverse supplied by proved linear independence.
- `seed_energy_gain`, `energy_le_seed`: exact energy reduction and comparison to the explicit coprime-counting seed.
- `objective_norm_gap`, `objective_error_gap`, `objective_gap_le_tail`: squared displacement between the two minimizers bounded by the complete Q tail of the constant vector.
- `missing_prime_value`: an exact head ending immediately before an omitted prime forces value 2 at that prime.

## Conditional research reduction

`riemannHypothesis_of_bounded_energy` requires a uniform bound on the actual complete norm energy of the constructed minimizers, squarefree periods, and the explicit expanding prime cover.

Open: supply a finite constant B bounding every stage's minimum energy. Neither the divergent explicit seed nor finite numerical improvements discharge this provider.

## Separate computational evidence

Exact rational Python certificates bracket the actual minima at L=30,210,2310,30030. Full-tail floating-point computations reach L=9699690. These numerical intervals have not been formalized in Lean. See the accompanying computation bundle and the research memorandum for exact witnesses, executable certificate scripts, and completed verification logs.

## Exact-head correction certificates and conductor gaps

See [continuation memorandum](RH/MinimumEnergyCorrectionCertificates20261028.md).

Established Lean statements:

- `RH/QResidueEnergyCertificates.lean`: complete signed correction gain with its
  norm-square remainder; one-direction optimization; exact dictionary-enlargement
  and head-enlargement energy identities and their monotonicity consequences.
- `RH/QCRTCorrectionCertificates.lean`: actual compensated correction blocks,
  automatic zero-head membership and squarefree legality, and the complete signed
  finite coefficient certificate. The stage-independent bound is still Open.
- `RH/QCRTFiniteCertificates.lean`: binary legal vectors at periods 6 and 30,
  exact heads 2 and 5, complete energy at most 1; canonical stages j=1 and j=4
  therefore have minimum energy at most 1.
- `RH/QCRTConductorGap.lean`: exact head agreement propagates across conductor
  gaps; every period-210/head-10 and period-30030/head-15 feasible vector has
  complete energy greater than 1. In particular,
  `minimumEnergyApproximant_fourteen_gt_one` rules out C=1 for the entire
  canonical diagonal. An arbitrary finite common bound remains Open.

The 23 rational trial-vector certificates in the
[experiment bundle](https://chatgpt.com/library?file_id=libfile_3a2612c77a048191b8ec721ccd53ffca&account_id=personal) extend slower/smaller head schedules. Their independent Python checker includes the entire infinite
tail. They are not Lean numerical theorems. Trial-vector lower bounds are not
asserted as lower bounds on the minima; the conductor-gap Lean statements are
separate actual lower certificates.

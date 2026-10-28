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

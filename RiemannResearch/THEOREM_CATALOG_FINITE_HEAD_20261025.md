# Finite-head convergence: theorem catalog supplement

25 October 2026. Source: the user's finite-head projection convergence request.

## Established statements

All results below are unconditional. The convergence hypothesis in the general
Hilbert results is supplied by the existing strong projection convergence
theorems in the two application results. No RH or constant-target membership
hypothesis occurs.

- `Analysis/FiniteCoordinateConvergence.lean`:
  `Analysis.finite_abs_sub_eventually` and
  `Analysis.finite_max_abs_sub_tendsto` upgrade pointwise real convergence
  to uniform convergence over a fixed finite set.
- `RH/FiniteHeadHilbertConvergence.lean`:
  `ZetaTwoHilbert.qSequence_head_max_tendsto`,
  `ZetaTwoHilbert.qSequence_uniform_on_head`,
  `Pareto.hilbertSequence_tendsto_of_tendsto`,
  `Pareto.hilbertSequence_head_max_tendsto`, and
  `Pareto.hilbertSequence_uniform_on_head` apply this to the actual physical
  Q and Pareto coordinates.
- `RH/FiniteHeadProjectionConvergence.lean`, namespace
  `RiemannResearch.RH.FiniteHeadProjectionConvergence`:
  `q_optimizer_head_max_tendsto`, `q_optimizer_uniform_on_head`,
  `pareto_projection_head_max_tendsto`, and
  `pareto_projection_uniform_on_head` specialize to the standard projections.

The maximum statements use `Finset.Icc 1 H` and require `1 ≤ H`.
The epsilon statements permit every natural H, including the empty head H = 0.
The Q stages are squarefree; the standard Pareto stages use all conductors.
The limiting projections depend on the measure. These results assert neither
uniform convergence over all positive integers nor convergence to the constant 1.

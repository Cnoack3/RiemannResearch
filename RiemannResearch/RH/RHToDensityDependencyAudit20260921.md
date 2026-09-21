# RH-to-residue-density: dependency audit

Audited project: `RiemannResearch`, commit
`8882f23b9965fe409a48fda1f792a471a436826b`, 2026-09-21.

This is a source audit and classical proof route, not a Lean proof of the missing theorem.
No verification jobs were submitted by the audit agent.

## Exact missing declaration

```lean
theorem closedSpace_eq_top_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    RiemannResearch.RH.Pareto.CoefficientStabilization.closedSpace = ⊤
```

`RH/ResidueClosureDensity.lean` already proves
`CoefficientStabilization.closedSpace_eq_top_iff_one_mem`.
Consequently it suffices to prove that RH implies membership of `hilbertOne`
in the actual closed residue span. This converse is mathematically known,
but no checked provider was located in this project or Mathlib.

The exact hypothesis is still explicit in
`RH/FirstCoordinateTailGap.lean` and `RH/MellinDeficitRHTest.lean`.
The forward implications from density/vanishing gap to actual Mathlib RH
are already established and do not discharge this converse.

## Source and proof route

Source: Bhaskar Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space
reformulation of the Riemann hypothesis*, Theorems 1 and 2 and Lemma 3:
<https://arxiv.org/pdf/math/0607733>.
This reference supports the statement and the following proof strategy.

Write `M f(s) = integral_1^infinity f(floor x) x^(-s-1) dx` and
`g_d(n) = (n mod d)/d`. The project proves the arithmetic Mellin identity

    M g_d(s) = (d^(-1) - d^(-s)) zeta(s)/s.

For epsilon > 0 consider actual finite vectors

    F_{L,epsilon} = - sum_{d=1}^L mu(d) d^(-epsilon) g_d.

They belong to the residue span by construction. Their Mellin transforms are

    zeta(s)/s * (sum_{d<=L} mu(d)d^(-s-epsilon)
                 - sum_{d<=L} mu(d)d^(-1-epsilon)).

Under RH, the classical argument proves two norm limits in order:

1. For each fixed epsilon > 0, as L tends to infinity the displayed transforms
   converge in boundary L2 to

       H_epsilon(s) = zeta(s)/s *
         (1/zeta(s+epsilon) - 1/zeta(1+epsilon)).

2. As epsilon tends to zero through positive values, H_epsilon converges in
   boundary L2 to 1/s, which is the Mellin transform of the constant vector.

The represented Mellin isometry transfers these limits to the actual
weighted Hilbert space. Closedness gives membership of the constant, and
`closedSpace_eq_top_iff_one_mem` finishes. Neither limit can be replaced by
pointwise convergence alone.

## Substantive analytic dependencies not located

* **Littlewood conditional convergence and bounds.** RH implies that the
  ordered finite sums of mu(n)n^(-s) converge locally uniformly for Re(s)>1/2.
  The dominated-convergence argument also needs a quantitative bound,
  uniform in the finite cutoff L: for every epsilon,delta>0, these partial
  sums are O_{epsilon,delta}((1+|Im(s)|)^delta) on
  Re(s)>=1/2+epsilon. Bagchi's Lemma 3 states this input and omits its proof.

* **RH-Lindelof growth.** The product with zeta(s)/s needs square-integrable
  boundary domination for the first limit.

* **A uniform shifted zeta quotient estimate.** For 0<epsilon<1/2 the second
  limit requires uniform boundary domination. Bagchi derives
  |zeta(s)/zeta(s+epsilon)| <= C |s|^(epsilon/2) on the critical line from
  the paired Hadamard product for xi under RH and a Gamma-ratio bound.
  Pointwise nonvanishing of zeta to the right of the line does not give
  this uniform estimate.

* **Boundary isometry assembly for these finite and limiting vectors.**
  The project has represented finite-energy Mellin/Plancherel and strong
  boundary trace infrastructure. A route through arbitrary Hardy functions
  would additionally require `GeneralHardyConverse`, which
  `RH/HardyConverseBoundaryStatus20260918.md` explicitly records as unproved.
  The direct represented-vector argument should avoid adding that extra
  dependency where possible.

Bounded source searches found no Littlewood, Hadamard or Lindelof provider.
The existing `DampedMobiusSeed`, `DampedMobiusCoefficients`, and
`DampedMobiusCoefficientEnergy` modules supply exact finite floor/divisor
identities and coefficient-energy estimates, not the two required norm
limits. An energy bound on arithmetic coefficients is not automatically
an energy bound on their residue synthesis.

## Critical Lean convergence distinction

Mathlib's `ArithmeticFunction.LSeriesSummable_moebius_iff` states

```lean
LSeriesSummable (fun n => (ArithmeticFunction.moebius n : Complex)) s
  <-> 1 < s.re
```

This is unconditional. `Summable` for complex-valued terms describes
unconditional, hence absolute, summation. Littlewood's RH consequence in
the larger half-plane is convergence of **ordered partial sums**, which
must be expressed using `Tendsto` of finite initial sums. It would be false
to replace that input by `LSeriesSummable` for Re(s) between 1/2 and 1.

## Status

The RH-to-density implication is a missing formalization of a known
classical theorem. The assertion that the actual gap is zero without
assuming RH is the unsolved arithmetic/RH question. These are distinct
obligations. No provider or elimination of the `hDensity` hypothesis is
claimed by this audit.

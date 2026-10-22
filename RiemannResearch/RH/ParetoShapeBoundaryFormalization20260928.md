# Pareto shape thresholds and the shape-one limit (2026-09-28)

This continuation formalizes the user's Pareto capacity discussion and strengthens it in three directions. The development adds 47 theorem declarations. The coherent proof candidate was checked with no proof placeholders; the selected principal declarations use only propext, Classical.choice, and Quot.sound. Publication additionally validates the source modules and affected dependents. Domain-specific hypotheses remain listed below.

## Sharp energy threshold

For alpha > 0, sigma = Re(s) > 0, and
w_alpha(x) = x^(-alpha) - (x+1)^(-alpha), the actual Mellin cell energies obey

    sum_n ||(n+1)^(-s) - (n+2)^(-s)||^2 / w_alpha(n+1) < infinity
      iff alpha < 2 sigma.

`shapeMellinEnergy_summable_iff` proves this equivalence without a zeta-zero or RH premise. The normalized certificate and every finite shift have the same exact threshold. Critical-line parameters specialize to alpha < 1.

At the boundary the proof supplies the explicit lower bound

    E_(2 sigma)(s,x) >= (sigma * 2^(-sigma) / 2) / (x+1).

Reverse triangle bounds the numerator below by (A-B)^2, where A=x^(-sigma), B=(x+1)^(-sigma), and the boundary denominator factors as (A-B)(A+B). The integral formula for normalized cell masses proves monotonicity and propagates harmonic divergence to larger shapes. The earlier integral Cauchy bound supplies convergence below the boundary.

The same comparison also proves the exact weight order:
for alpha,beta > 0, some positive constant C satisfies w_alpha(n+1) <= C w_beta(n+1) for all n iff beta <= alpha. Two-sided global comparison holds iff alpha=beta. A smaller shape therefore cannot obtain the Pareto(1) criterion through a two-sided comparison of weights.

## Actual boundary blow-up

The development generalizes the existing finite-sum Fatou argument to arbitrary filters. It proves that the actual full and normalized Mellin energies tend to positive infinity as alpha approaches 2 Re(s) from below, after every finite deletion. No zero or RH hypothesis occurs. This is stronger than divergence of an energy majorant and still does not itself imply capacity divergence.

## Uniformity at shape one

`shapeLegalTailEnergy_continuousAt` proves continuity at every positive shape for each actual legal finite combination, retaining its full infinite tail and mixed terms. Dominated convergence uses the summable energy at half the reference shape.

`shapeLegalTailEnergy_one` identifies the endpoint exactly with the original complex Pareto tail norm. For any a<1, `shape_endpoint_coercivity_iff` proves equivalence between:

* one epsilon controlling every coefficient vector at shape 1;
* that same normalized epsilon controlling every coefficient vector and every positive shape alpha in (a,1).

Existence of a positive such constant is equivalent to bounded original Pareto(1) tail capacities, without any zeta or density hypothesis. Its equivalence to not RH retains the explicit classical input RH -> closedSpace=top.

Conversely, arbitrarily small normalized coercivity ratios in such a neighborhood imply RH without assuming the RH-to-density direction.

Certificate divergence alone does not prove capacity divergence. Separate bounds for every smaller shape also do not produce one bound uniform as alpha approaches 1.

## Comparable weights

`ParetoComparableWeights.lean` uses the actual target and legal residue sums. For c,C>0 and c*p_n <= w_n <= C*p_n, p_n=1/((n+1)(n+2)), it establishes:

* equality of finite-energy domains for every raw real sequence;
* c*||f||^2 <= weightedEnergy(w,f) <= C*||f||^2;
* equivalent approximation by legal residue combinations;
* preservation of the quantitative off-line-zero obstruction, scaled by c.

Approximation implies RH through the previously proved Mellin obstruction. The converse explicitly takes RH -> BaezDuarte.NaturalApproximation. Every weight comparable to 1/(n+1)^2 is covered, using p_n <= 1/(n+1)^2 <= 2*p_n.

## Classical inputs

The original Nyman–Beurling theorem is an L2 fractional-part density criterion. Pareto(1) is the weight in the discrete reformulation used here. Two-sided comparable weights preserve this criterion; changing the Pareto shape does not preserve two-sided comparability.

Critical-line zero existence is now supplied without premises by `RH/CriticalLineZeros.lean`, through the imported and kernel-checked Zeta23 zero-proportion and total-count theorems. The original bounds retain explicit-zero interfaces for reuse; `RH/SubcriticalShapeCoercivity.lean` discharges that input. The RH-to-density analytic implication remains explicit.

Primary sources:
* Bagchi, Theorem 1 and its following paragraph: https://arxiv.org/pdf/math/0607733
* Baez-Duarte's strengthened criterion: https://arxiv.org/abs/math/0202141

The pinned imported proof source is:
https://github.com/anthropics/formal-math/tree/fbdc36bbf17d20af3fd0447c6d1a8a02773c9844/zeta23

The selected closure now contains 140 imported modules, with unchanged Lean/mathlib versions. `exists_critical_zero` and the stronger arbitrarily-high simple-critical-zero theorem are proved consumers of that import, not axioms.

## Unconditional subcritical coercivity and moving shapes

`exists_uniform_subcritical_shape_coercivity` supplies one C>0 such that

    alpha(1-alpha)|A(n,c)|^2 <= C E_alpha(n,c),  0<alpha<1.

Thus `exists_subcritical_shape_capacity_rate` bounds every finite capacity by C/[alpha(1-alpha)], and every fixed subcritical shape has a positive normalized energy gap. For shapes bounded below by any a0>0, `exists_subcritical_shape_normalized_gap_rate` bounds normalized energy below by delta(1-alpha), with one delta>0.

`subcritical_normalized_small_tail_shapes_tendsto_one` proves that normalized trials of vanishing complete energy must approach shape one when bounded away from shape zero. `not_subcritical_normalized_energy_ratio_tendsto_zero` further excludes energy little-o of 1-alpha. These results supply no approximating trials at shape one and do not prove RH. See `RH/Zeta23Consequences20260928.md`.

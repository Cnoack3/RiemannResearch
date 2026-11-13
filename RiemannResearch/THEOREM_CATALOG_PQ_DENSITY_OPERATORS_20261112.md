# P/Q density operators and the remaining RH premise

Date: 2026-11-12 (user-facing date).
Source: user-provided correction reserving B for dQ/dP.
Base examined: 8b94e4c6fcadf811881e42aa2999f5c099b643c4.

## Notation and scope

For physical n >= 1:
P(n)=1/[n(n+1)], Q(n)=1/[zeta(2)n^2].
Bf(n)=(n+1)f(n)/[zeta(2)n], Df(n)=f(n)/n, Rf(n)=f(n)/(n+1).
B inverse is zeta(2)n/(n+1). B always means QDensityMetric.B here.
Historical QShiftedReciprocal.B implements R; new modules use local notation R.
The physical index n is encoded at normalized l2 coordinate n-1.
All density results below use every conductor k>=2.

## Established declarations

Module: RH/QDensityMetricInverse.lean
Namespace: RiemannResearch.RH.QDensityMetricInverse

| Declaration | Meaning |
|---|---|
| inverse, inverse_apply | Bounded continuous linear inverse density |
| inverse_B, B_inverse, densityEquiv | Two-sided bounded linear equivalence B |
| qSequence_inverse | Physical multiplier zeta(2)n/(n+1) |
| D_eq_density | Df=zeta(2) Bf-f |
| inverse_D, R_eq_inverse_D | B inverse D=zeta(2) R |
| R_eq_inverse | R=I-B inverse/zeta(2) |
| pareto_inner_inverse | <f,g>_P=<f,B inverse g>_Q |
| q_inner_density | <f,g>_Q=<f,Bg>_P |
| norm_comparison | (zeta(2)/2)||f||_Q^2 <= ||f||_P^2 <= zeta(2)||f||_Q^2 |
| DP, DP_toPareto, DP_physical | D_P=T D_Q T inverse; D_P T=T D_Q; physical division by n |
| map_closure | B(cl S)=cl(BS) for any submodule |
| mem_density_closure_iff | Bf in cl(BS) iff f in cl S |
| density_closure_eq_top_iff | Density is preserved and reflected by B |

Module: RH/QDensityClosureTransfer.lean
Namespace: RiemannResearch.RH.QDensityClosureTransfer
Here S=QFullResidueProjection.legalSpan and V=QFullResidueProjection.closure.

| Declaration | Meaning |
|---|---|
| map_legalSpan | Operator image of S equals the corresponding generator span |
| full_D_map_dense | cl(D S)=H, from the existing full-conductor theorem |
| full_R_map_dense | cl(R S)=H |
| full_augmentedClosure_eq_top | cl span{g_k,Bg_k}=H |
| densityClosure_eq_image | cl(B S)=B(V) |
| densityClosure_eq_top_iff | cl(B S)=H iff V=H |
| fullClosure_eq_top_iff_density_generators_mem | V=H iff all B g_k belong to V |
| fullClosure_eq_top_iff_density_invariant | V=H iff B(V) is contained in V |
| density_target_mem_iff | B1 in cl(B S) iff 1 in V |

Full R-density is transferred by B inverse D=zeta(2)R, not by inverting D.
The complete P statements follow from the sequence-preserving equivalence and equivalent norms.

## Conditional research reductions

| Declaration | Exact open premise | Conclusion |
|---|---|---|
| riemannHypothesis_of_densityClosure_eq_top | cl(B S)=H | Mathlib RiemannHypothesis |
| riemannHypothesis_of_density_target | B1 in cl(B S) | Mathlib RiemannHypothesis |
| riemannHypothesis_of_density_invariant | For every f in V, Bf is in V | Mathlib RiemannHypothesis |

All use the existing QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure.
That bridge takes 1 in V explicitly, transfers to the Pareto legal closure, and
uses the existing Mellin separation theorem. No RH premise is discharged by
full_D_map_dense or full_augmentedClosure_eq_top.
No converse RH=>V=H is asserted.

## Why the abstract shortcut fails (paper proof, not a new Lean theorem)

In l2 on positive integers let D0=diag(1/n), a=(1/n), and W=a-perp.
W is a proper closed hyperplane. If y is orthogonal to D0 W, self-adjointness
gives D0 y in span(a), so y is constant; the only constant l2 sequence is zero.
Thus D0 W is dense. For any c>0 set B0=(I+D0)/c and R0=diag(1/(n+1)).
B0 is positive and boundedly invertible, R0=B0 inverse D0/c, and
D0 W is contained in W+B0 W. Hence D0 W, R0 W and W+B0 W are all dense,
although W is proper. D0 and R0 are compact and injective.

This refutes the general operator-theoretic inference to full totality.
It does not refute totality of the arithmetic residue family.
It shows that arithmetic information or a source bound is still needed.

## Research agenda

1. Open, highest priority: produce finite legal v_j with Dv_j -> D1 and
   bounded source norms, or a bounded cofinal subsequence.
   QReciprocalTargetLift.riemannHypothesis_of_bounded_D_target is the consumer.
2. Open: prove a complete O(alpha_j) regularized cost for explicit cofinal
   cutoffs and positive alpha_j -> 0. Retain the parameter-change correction
   and infinite tails when using inverse-Gram minimizers.
   QReciprocalCostEquivalence.mem_closure_iff_regularized_cost is the exact
   closure equivalence.
3. Open: force the actual residual 1-Pi_V 1 to vanish, preserving
   ||1-Pi_VN 1||^2=1-b_N^T G_N inverse b_N and its limiting remainder.
4. Open: prove density leakage (I-Pi_V)B|V is zero from arithmetic.
   This is equivalent to V=H, rather than a free consequence of measure change.
5. Open: prove saturation for Dg_2, then prove any conductor propagation needed.
   The exact existing limit is pi^2/64 minus ||Dg_2-Pi_V Dg_2||^2.
6. Open: combine CRT interpolation with uniform complete Q-tail/source-energy
   estimates; neither finite-coordinate agreement nor profinite continuity
   alone supplies a bounded legal lift.
7. Open: audit and formalize any desired converse from RH to this exact
   target closure or full totality. Keep RH, 1 in V and V=H distinct.

## Verification evidence

Focused acceptance:
- Job job_W7uADcOlCs7XcldAS62aR12J-Z6wNsQw
- Bazel --config=buildbuddy //RiemannResearch/RH:QDensityClosureTransfer
- verified=true, exit_code=0, server verification duration 61.101 seconds.
- Includes both new modules and all transitive imports.
- Closure module SHA256: 158e0c1076ce2191ca425002a5b4f1c48940a8548afefabac56b56be29d1549c.
- Full project acceptance and exact publication commit are provided by the
  required server checkpoint; a focused check is not that publication result.

The new source introduces no unproved domain-specific axioms or proof placeholders.
Its RH declarations retain the exact open hypotheses displayed above.
The companion PDF/TeX distinguishes formal declarations from paper arguments.

## Literature context

Luis Baez-Duarte, A strengthening of the Nyman-Beurling criterion for the Riemann
hypothesis, Rend. Lincei Mat. Appl. 14 (2003), 5-11.
https://arxiv.org/abs/math/0202141

Luis Baez-Duarte, Arithmetical Aspects of Beurling's Real Variable Reformulation
of the Riemann Hypothesis (2000).
https://arxiv.org/abs/math/0011254

These references motivate target approximation and the L2 requirement;
they do not supply the open bounded-lift or cost estimates above.

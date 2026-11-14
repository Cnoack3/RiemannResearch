# Dirichlet exponential: domain, legality, and an unconditional obstruction

Date: 2026-11-13 (America/New_York).
Source: Christian Noack's follow-up, "what is exp_*(V).... does it retain legality? use lean".
This extends the parity-convolution analysis and the actual Dirichlet-exponential modules.

## Meaning of the question

Let \(H\) be the existing Pareto Hilbert space, with
\[
\|f\|_H^2=\sum_{n\ge1}\frac{|f(n)|^2}{n(n+1)},
\]
and let \(V\) be \(\mathtt{CoefficientStabilization.closedSpace}\), the closed
span of the normalized residue generators.
The multiplication below is Dirichlet convolution. Its unit is delta_1, not
the constant-one arithmetic function.

\[
\exp_\star(f)(n)=\sum_{r=0}^{\infty}\frac{f^{\star r}(n)}{r!},
\qquad f^{\star0}=\delta_1,
\qquad \exp_\star(V)=\{\exp_\star(f):f\in V\}.
\]
The image is first a set of physical sequences; it is not a linear subspace.
In fact \(\exp_\star(f)(1)=e^{f(1)}>0\), so the zero sequence is absent.

## Verification

All three new modules (49 theorems) passed Lean through Bazel/BuildBuddy.
The final import-and-axiom audit succeeded with exit code 0:
[invocation 940a2887-0c1e-4edf-8116-631a8c8b4b6d](https://app.buildbuddy.io/invocation/940a2887-0c1e-4edf-8116-631a8c8b4b6d).
Seven principal declarations were checked with guarded `#print axioms` commands;
each uses only `propext`, `Classical.choice`, and `Quot.sound`.
There is no `sorryAx`, custom axiom, or unproved arithmetic provider in the
counterexample or the full-legality refutation. The optional RH equivalence
retains its converse provider explicitly.
See [verification evidence](ExponentialLegalityVerification20261113.json).

## Kernel-checked conclusions

1. Every real arithmetic input has an absolutely convergent exponential series
   at each fixed coordinate. No global boundedness or Hilbert-energy hypothesis is needed.
2. Every bounded physical input has an actual exponential in H, using the
   existing generalized-divisor factorial moment theorem.
3. Preservation of V for every bounded input from V is equivalent to V=H.
   The forward implication already follows from the input zero:
   exp_*(0)=delta_1, and the existing project proves delta_1 in V iff V=H.
   This bounded preservation condition implies Mathlib's RiemannHypothesis.
   The reverse RH-to-density theorem remains an explicit provider in the
   optional iff-RH declaration.
4. There is a positive f in H whose convolution square and exponential have
   infinite Pareto energy. Thus H is not a Dirichlet convolution algebra,
   and the coefficientwise exponential is not an everywhere-defined map H->H.
5. Full preservation of legality on V is false, unconditionally. If V is
   proper, the zero input is an obstruction; if V=H, the positive H
   counterexample is an obstruction. This is not a disproof of RH.
6. The centered exponential exp_*(f)-delta_1 belongs to V if all positive
   powers belong to V and their complete squared energies satisfy a common
   factorial bound. Neither power legality nor the energy bound is silently
   supplied by coefficientwise convergence.

## Explicit energy counterexample

Set \(c_a=(a+1)^{-3/4}\), \(f(2^a)=2^a c_a\) for \(a\ge0\), and
\(f(n)=0\) off powers of two. Then
\[
\sum_{n\ge1}\frac{f(n)^2}{n^2}=\sum_{a\ge0}(a+1)^{-3/2}<\infty.
\]
At each power of two,
\[
\frac{(f\star f)(2^a)}{2^a}
=\sum_{j=0}^a c_jc_{a-j}
\ge(a+1)c_a^2=(a+1)^{-1/2}.
\]
Consequently,
\[
2P(\{2^a\})(f\star f)(2^a)^2\ge\frac1{a+1}.
\]
The harmonic series forces the complete convolution-square energy to diverge.
Since \(f\ge0\), \(\exp_\star(f)\ge(f\star f)/2\) coefficientwise, so its
complete energy also diverges.

The sparse input is an actual ArithmeticFunction, defined using an injective
extension from a |-> 2^a. Its H-vector is built using the proved square
summability; the counterexample does not assume H is closed under convolution.

## Main declarations

| Module | Declaration | Result |
|---|---|---|
| NumberTheory/DirichletExponentialDomain.lean | convolutionExp_summable_at | Actual coefficientwise exponential for every real arithmetic input. |
| NumberTheory/DirichletExponentialDomain.lean | convolutionExp_at_one; convolutionExp_ne_zero | First coefficient is exp(f(1)); exponential never equals zero. |
| NumberTheory/DirichletExponentialDomain.lean | convolutionExp_quadratic_lower_of_nonneg | Quadratic lower bound without a boundedness hypothesis. |
| RH/ParetoExponentialLegality.lean | expImage_not_submodule | The exponential image is not a submodule. |
| RH/ParetoExponentialLegality.lean | physicalExp_square_summable_of_bounded | Bounded physical inputs have finite exponential energy. |
| RH/ParetoExponentialLegality.lean | retainsBoundedLegality_iff_density | Bounded legality preservation iff V=H. |
| RH/ParetoExponentialLegality.lean | riemannHypothesis_of_retainsBoundedLegality | Bounded legality preservation implies RH. |
| RH/ParetoExponentialLegality.lean | retainsBoundedLegality_iff_rh | RH equivalence with explicit hDensity converse provider. |
| RH/ParetoExponentialLegality.lean | centered_exponential_mem_of_positive_power_legality | Positive-power legality plus factorial energy gives centered legality. |
| RH/ParetoExponentialCounterexample.lean | sparseInput_square_not_pareto_summable | Explicit positive H input has convolution square outside H. |
| RH/ParetoExponentialCounterexample.lean | sparseInput_exp_not_pareto_summable | Its actual coefficientwise exponential is outside H. |
| RH/ParetoExponentialCounterexample.lean | exists_exponential_outside_hilbert | Failure of an everywhere-defined H-valued exponential. |
| RH/ParetoExponentialCounterexample.lean | not_retainsLegality | Unconditional failure of full V-legality preservation. |
| RH/ParetoExponentialCounterexample.lean | exists_legal_input_without_legal_exponential | A legal input exists whose exponential has no legal representative. |

## Published context and computation provenance

- Mathlib's [p-series development](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/PSeries.html)
  supplies the summability criterion and harmonic-series obstruction. These
  results are used inside the Lean proof, not imported as unchecked facts.
- Mathlib's [exponential development](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Algebra/Exponential.html)
  supplies the ordinary scalar exponential-series identity at coordinate one.
  No Banach-algebra norm for Dirichlet convolution on H is assumed.
- Luis Báez-Duarte, [A strengthening of the Nyman–Beurling criterion for the Riemann hypothesis](https://www.bdim.eu/item?id=RLIN_2003_9_14_1_5_0),
  Rendiconti Lincei, 14 (2003), 5–11, provides the published integer-dilation
  approximation context. This citation does not discharge the project's
  explicit RH-to-Pareto-density formalization dependency.
- Wolfram Language independently checked
  (a+1)((a+1)^(-3/4))^2=(a+1)^(-1/2),
  ((a+1)^(-1/2))^2=(a+1)^(-1),
  and sum_{a>=0}(a+1)^(-3/2)=Zeta[3/2].
  It reported the harmonic series as divergent. These are external symbolic
  checks only; none supplies a Lean hypothesis or proof step.
  WolframContext returned an internal error; the direct evaluator succeeded.

## Remaining RH boundary

The false full-preservation statement cannot be used as an RH route.
The valid bounded-preservation equivalence does not prove density; it identifies
the same unsupplied density obligation in exponential language. For individual
bounded generators g_k, ambient exponential energy is proved, while closed-span
membership remains a separate approximation question. Centering removes the
zeroth-term obstruction but does not establish legality of positive convolution
powers.

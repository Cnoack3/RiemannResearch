# Formalization audit of the explicit fifth-power squarefree gap

29 October 2026. Requested target: Kumchev et al., Theorem 1, for every real
x >= 2, a squarefree integer in (x, x + 11*x^(1/5)*log x].

## Status

**The full interval theorem is not yet proved in Lean.**

This continuation verifies an error in a displayed inference in the cited
proof, proves corrected local spacing results with explicit hypotheses,
and certifies rational constants for a possible repair. It does not replace
the requested theorem by the elementary square-root gap theorem.
No external theorem, numerical computation, or missing provider is added
as a custom axiom. RH remains unproved.

The target, in ordinary Lean notation, is:

```lean
∀ x : ℝ, 2 ≤ x →
  ∃ r : ℕ, Squarefree r ∧ x < (r : ℝ) ∧
    (r : ℝ) ≤ x + 11 * x ^ (1 / 5 : ℝ) * Real.log x
```

This statement is recorded here as an open target, not exported as a theorem.

## A certified problem in equation (4.3)

Source: Kumchev, McCormick, McNew, Park, Scherr and Ziehr,
*Explicit bounds for large gaps between squarefree integers*,
Journal of Number Theory 254 (2024), 336–357.
Primary sources:

- https://arxiv.org/html/2211.09975v3
- https://www.nathanmcnew.com/Explicit2.pdf
- https://doi.org/10.1016/j.jnt.2023.07.003

Lemma 6 sets V = a*b*(b^2-a^2). Its equation (4.3) uses
b^2-a^2 >= (3/4)*b^2 to infer a lower bound with denominator
(3/4)*a*b^3. The reciprocal comparison goes in the other direction.

The exact witness a=2, b=8, numerator N=2, error theta=0 gives

```text
|N-theta|/[a*b*(b^2-a^2)] = 1/480
1.98/[(3/4)*a*b^3]       = 33/12800
1/480 < 33/12800.
```

These gaps are positive and even, 2a <= b, N is nonzero and even, and
|theta| < 1/50. The checked declaration
SquarefreeGapSpacing.reciprocal_step_counterexample proves the failure
of the claimed numerical implication.

**This is not a counterexample to Theorem 1, nor a claim that these numbers
are an actual four-node squarefree configuration.** It refutes the displayed
algebraic inference from the inequalities and parity facts cited there.

A second scope issue occurs in Lemma 6's nonvanishing argument: it cites (3.7),
which was established in the small-b branch b <= 0.004M of Lemma 5.
For the larger range needed in Lemma 6, the proposed repair is to use
the weaker triple-product estimate

  (199/100)*M^4 <= 3*x*a*b*(b-a).

The new Lean theorem states this estimate as an explicit hypothesis;
it does not silently assume the stronger (3.7) throughout the larger range.

## Verified spacing results

File: NumberTheory/SquarefreeGapSpacing.lean.

The proof uses the exact identity for the third divided difference of x/t^2
at the paired nodes u, u+a, u+b, u+a+b. Its negative is

  x * [1/(u^2*v*w*z) + 1/(u*v^2*w*z)
       + 1/(u*v*w^2*z) + 1/(u*v*w*z^2)],

where v=u+a, w=u+b, z=u+a+b. Each denominator has degree five.
Bounds follow directly by replacing each positive node by its lower or
upper bound. No numerical differentiation or mean-value axiom is used.

Established declarations:

- reciprocal_step_counterexample: exact failure of the disputed inference.
- paired_divided_difference: the exact rational four-node identity.
- inverseSquareThirdMagnitude_le and inverseSquareThirdMagnitude_lower:
  the bounds 4*x/L^5 <= magnitude <= 4*x/M^5 for nodes in [M,L].
- even_integer_error_lower: a nonzero even integer differs from an error
  of magnitude at most 1/50 by at least 99/50.
- corrected_spacing_of_numerator: the repaired terminal implication
  (99/200)*M^5/x <= a*b^3, from its explicit numerator and analytic bounds.
- paired_numerator_identity and pairedNumerator_even: exact denominator
  combination and parity of the actual integer linear combination.
- paired_spacing_of_even_numerator: the same corrected spacing from the
  actual reciprocal-square expressions, proving the analytic bound internally.
- paired_numerator_ne_zero: obtains nonvanishing from the corrected
  triple-product bound, 5h <= M, the error bound, and a lower bound for
  the third divided difference.
- paired_spacing_of_triple_product: combines these steps. It assumes
  x>0, M>0, M<=u, 0<a<b, h>=0, 5h<=M, u+a+b<=(21/20)M,
  the preceding triple-product bound, an even integer N, and the exact
  numerator/error representation with |theta|<=2bh/M^2.
  It proves (99/200)*M^5/x <= a*b^3. Nonvanishing of N is proved internally.

The last theorem is a genuine local spacing result. It is **not yet the full
Lemma 6 for elements of the paper's set S(M)**: constructing the numerator
representation and proving the triple-product input from membership in S(M)
remain obligations. It is also not the final squarefree interval theorem.

## Exact certificates for a proposed constant repair

File: NumberTheory/SquarefreeGapConstants.lean.

The correct direct terminal coefficient is 0.4950 rather than 0.6600.
Conservative downstream replacements are:

| Quantity | Printed value | Replacement |
|---|---:|---:|
| Paired spacing coefficient | 0.6600 | 0.4950 |
| Cube-root spacing coefficient | 0.8706 | 0.7910 |
| Cluster coefficient | 1.4959 | 1.6464 |
| Product coefficient | 0.2173 | 0.2391 |
| First coefficient in (5.11) | 0.4346 | 0.4782 |
| Third coefficient in (5.11) | 2.9918 | 3.2928 |
| Coefficient in (5.14) | 0.0154 | 0.01694 |
| Changed sigma3 coefficient | 0.0308 | 0.03388 |
| First sigma4 coefficient | 1.2105 | 1.3323 |
| Second sigma4 coefficient | 1.4182 | 1.5608 |

repaired_coefficients verifies the defining rational polynomial comparisons,
including 0.791^3 < 0.495 and the cubed comparison behind 0.01694.
coefficient_inflation verifies that each of the last three replacements
is bounded by 1.101 times its printed value.
These certificates do not themselves prove all of the intervening
real-power summation estimates.

Retaining the paper's other component estimates, the proposed repaired
Section 6.1 totals are 0.9991 and 0.9952. repaired_sieve_totals verifies
the exact arithmetic, and repaired_margins proves both are below 1-1/h
when h>=2000. Thus the arithmetic margins are consistent with retaining
the final constant 11. The analytic hypotheses which feed those totals
are **not discharged** by these numerical certificates.

Wolfram independently checked the reciprocal witness and rational
comparisons. Lean's kernel checks are the proof evidence; Wolfram output
and floating-point computations are not trusted proof inputs.

## Remaining obligations for the requested theorem

The required work includes:

1. Derive the pair/triple spacing bounds and the exact error representations
   for members of the paper's odd near-integer set S(M). The repaired
   triple-product estimate must be proved in the full range where it is used.
2. Prove the paired-spacing dichotomy, ordered-set packing, geometric interval
   covers, and even-gap power-sum estimates used to bound S(M).
3. Formalize the sieve/inclusion-exclusion estimates and the explicit
   prime-count bound used for the small-prime contribution.
4. Certify the prime-square reciprocal sum and every needed logarithm,
   exponential, and real-power numerical estimate.
5. Prove the intermediate-range fourth-power gap estimates and their
   comparison with 11*x^(1/5)*log x.
6. Supply a verified finite-range replacement for the externally reported
   squarefree-gap computation through 10^18. The paper explicitly uses this
   computation to dispose of x up to exp(41). A publication reporting a
   computation is not a Lean certificate.

The authors' numerical notebook is available at
https://github.com/agreatnate/explicit-k-free-integer-bounds.
It generates constants; importing its decimal output does not establish
the inequalities in Lean.

## Effect on the RH research

The already checked complete-Q conductor-gap norm estimate, actual optimizer
cost theorem, squarefree anchors, signed energy budget, and conditional RH
consumer are unchanged. They do not depend on the disputed inference.

The previous report's fifth-power application remains an external paper-level
input. This audit prevents promoting that application to a checked Lean
theorem prematurely. Neither the moving-prediction growth bound nor a
subpolynomial cumulative energy provider has been proved.

## Verification record

Only the coordinator submitted Lean jobs; all verification was serialized.
The saved-module import and eight-declaration axiom audit succeeded in
job_3LL7qePLmbDB_q8QMrnkFjV1aeDTNXeE, with server verification time
13.258 seconds and negligible queue time. Every audited declaration depends
only on propext, Classical.choice, and Quot.sound. The initial import reported
two missing-header style warnings; the headers were then added to match the
repository convention. The final checkpoint rechecks the saved sources.
All declarations have complete proof terms; there are no admitted proofs
or added custom axioms. The final checkpoint is reported in the completion message.
Server verification time is reported separately from client request time.
Workspace-opening and polling round trips were not separately instrumented.

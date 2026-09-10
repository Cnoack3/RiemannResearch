# Formalization of the vanishing-damping quotient argument

September 10, 2026.

Source: the user-provided ordinary mathematical argument in
`RH_Two_Seed_Signed_Tail_Repair_Handoff_2026-09-09.md`, continuation headed
“The vanishing-damping quotient norm is uniformly bounded,” equations
(N1)–(N31). The working extraction was `norm_obligation_proved.md`.

**Status: partial formalization.** The concrete base regularization is defined
in Lean, and its arithmetic, quotient geometry, and general Abel analysis have
checked proofs. The concrete tail transfer is also proved. The unconditional
base bound in (N2), weak convergence, and density conclusion have not been
fully formalized.
The assembly theorem is a conditional research reduction. Its domain-specific
hypotheses are not axioms, and a clean axiom audit does not discharge them.

## Actual objects

All application declarations below use namespace
`RiemannResearch.RH.Pareto`. The ambient `ThresholdHilbert` is the existing
complete Hilbert realization of sequences with weight `1 / (n * (n + 1))`
on positive integers. Its `hilbertDilation` is the actual scaled integer
dilation, and `hilbertResidue` is constructed from the actual residue sequence.

`dyadicQuotientSubspace` is the orthogonal complement of the range of
`I - T₂`. `dyadicQuotientProjection` is its genuine bounded orthogonal
projection. Membership is proved equivalent to `T₂* f = f`; it is not
postulated. The proofs establish the full Pythagorean equality, contraction,
`Q T₂ = Q`, `Q T_m Q = Q T_m`, and the quotient dilation energy bound.

`dyadicRegularizedFamily ε` is the actual product-index series for
`G_{ε,1}` in (N1), with physical Möbius index `m + 1`. The coefficient
contains Mathlib's Möbius function and real powers. The normalization uses
the real Dirichlet series `∑ n≥1, n^(-(1+ε))`. Its summability and positivity
are proved for positive damping; identification with the complex zeta
function is not needed for the present declarations and is not claimed.

`dyadicRegularizedRawRectangle` and `dyadicRegularizedRectangle` are concrete
finite arithmetic sums, with their exact projection identity proved.
`DyadicRegularizedSeriesSummable` is deliberately distinct from
`DyadicRegularizedNormBound`: Lean's default value for a nonsummable `tsum`
must not be used to claim a result about a convergent arithmetic series.

## Checked supporting components

| Module | Mathematical content | Relation to the source proof |
| --- | --- | --- |
| `Analysis/AbelPrefixBound.lean` | Exact finite Abel summation with the terminal term; prefix order preserves geometric weighted order; a nonnegative sequence with linear prefix bound has a summable and uniformly bounded normalized Abel sum. | The general implication used in (N28)–(N29). The arithmetic logarithmic prefix bound itself is not assumed proved. |
| `Analysis/AbelCoboundary.lean` | Exact finite and infinite discounted telescoping; linear-operator orbit identities; averaging an invariant vector plus a coboundary. Every use of a vector series has its convergence hypotheses visible. | The general algebra in (N17), (N18), and (N23). |
| `Analysis/AbelOrbitGrowth.lean` | Exact scalar geometric moment; square-root orbit growth proves norm summability and `‖A_r v‖ ≤ C / sqrt (1-r)`; for `1/2 ≤ r < 1`, `‖A_r((I-B)z)‖ ≤ 4 C sqrt (1-r)`. | The quantitative implication from (N22) to the coboundary estimate in (N23). It does not construct the specific potential `Z` or prove its orbit growth. |
| `Analysis/AbelGramBound.lean` | From diagonal growth `‖v_j‖² ≤ D(j+1)` and a nonnegative off-diagonal majorant with prefix sums at most `A N`, proves `‖A_r v‖² ≤ D + 2 A`, including vector-series summability. The proof expands the exact norm-square recurrence before estimating all mixed terms. | The general Gram-to-Abel implication in (N26)–(N30), using a simpler sufficient finite recurrence. |
| `RH/DampedMobiusSeed.lean` | Exact finite divisor regrouping, normalized dilated-residue identity, density compensation, actual damped Möbius coefficients, and the zero-damping divisor cancellation. | The locally finite arithmetic identity underlying (N16). This does not identify an infinite projected series using Mellin moments. |
| `RH/DyadicRegularizedNorm.lean` | Actual quotient geometry, arithmetic family, finite rectangles, scalar convergence, damping bounds, and conditional norm and transfer assembly. | The geometric part of (N6), the exact statement of the base norm target, and the final norm calculation once the analytic estimates are supplied. |
| `RH/DyadicQuotientAbel.lean` | Constructs the actual induced integer-dilation semigroup; proves its physical power-orbit formula, that `QR₂` is fixed by every induced dilation, and that `Q1 = 1`; connects the concrete step orbit and coboundary estimates to the general Abel theorems. | The operator connection in (N6), the mean-vector invariance in (N21), and actual-operator versions of the general estimates. Concrete orbit and Gram estimates remain hypotheses. |
| `RH/DyadicTailQuotient.lean` | Constructs each actual `H_X` and `Q_X`, proves their support and variational characterizations, exact arithmetic transfer, and transfer of projected-series summability and squared norm. | Section 7's transfer to all `X,d` is supplied. The final theorem still requires the base arithmetic summability and base bound. |

The existing `RH/MertensElementary.lean` helper `sum_floor_weight` was made
public without changing its proof, so finite regrouping can reuse it.

## Exact remaining formal inputs

The declaration `dyadicRegularizedNormBound_of_analytic_estimates` requires:

1. `hseries : DyadicRegularizedSeriesSummable`, including convergence of the
   actual Hilbert-valued product-index series for every `0 < ε ≤ 1/2`.
2. Constants `A, R ≥ 0` and a proof `hstep` that the actual
   `dyadicStepAbelOrbit ε` has norm at most `A`, uniformly in that interval.
3. A proof `herror` of the actual norm estimate

   \[
   \left\|G_{\varepsilon,1}-
   \left(Q1+\frac{QR_2}{\log 2}-\mathsf A_{3^{-\varepsilon}}QT_3 1\right)
   \right\|\le R\sqrt\varepsilon.
   \]

Given these inputs, Lean proves both series summability and the uniform base
norm bound, with the explicit constant

\[
\left(\|Q1\|+\|(\log 2)^{-1}QR_2\|+A+R\right)^2.
\]

`dyadicStepAbelOrbit_norm_sq_le_of_gram` reduces the second input to actual
diagonal and off-diagonal inner products of
`Q T_(3^(j+1)) 1`, and the linear prefix bound for their majorant. This
specialization assumes the underlying Gram data, not an average-norm bound.

`DyadicTailRegularizedNormBound` states the full original (N2), for every
positive integer `X`, every `d ≥ X`, and every `0 < ε ≤ 1/2`:

\[
\exists C\ge0,\qquad \|G_{\varepsilon,d}\|_{H_X}^2\le Cd.
\]

The module constructs `H_X` as the orthogonal complement of the actual
point atoms before `X`, and proves that membership is exactly vanishing
of every coordinate before `X`. Its actual `Q_X` is the projection onto
`H_X` intersected with the orthogonal complement of `(I-T₂)H_X`, with the
variational fixed-adjoint characterization proved. Theorems
`dyadicTailRegularizedFamily_eq_transfer`,
`dyadicTailRegularizedSeriesSummable_of_base`, and
`dyadicTailRegularizedNormBound_of_base` establish the full concrete
transfer. There is no remaining arbitrary-projection or transfer-identity
hypothesis in these specialized theorems.

The supporting analytic providers still marked **Open** in the formalization
ledger are:

| Provider | Required content |
| --- | --- |
| Critical quotient norm | The exact fold/martingale norm (N5), its completeness/density statements, and the BV and dyadic-resolution estimates used in (N8), (N12), (N14), (N22), and (N26). |
| Uniform arithmetic cancellation | The quantitative Möbius cancellation and uniform parameter differentiation in (N9)–(N15), constructing the concrete quotient vectors `e_ε`. Existing finite Möbius identities do not supply these analytic estimates. |
| Infinite arithmetic identification | Absolute convergence of the projected arithmetic series, the exact quotient identity (N16), and its justified summation into (N18). The checked finite identity alone is insufficient. |
| Concrete seed potential | The boundary identifications of `W, U, V, Z`, the full identity (N21), and the concrete square-root orbit bound (N22). The mean vector `QR₂` and its invariance are already constructed and checked; the potential and its growth remain to be supplied. |
| Step orbit estimates | The actual logarithmic Gram estimate (N26), the continued-fraction/logarithmic prefix bound (N28), and their specialization to the actual orbit in (N30). |
| Remainder | The concrete normalization asymptotics and the above estimates combined to produce `herror`, equation (N24). |
| Recovery | Equation (N31), weak convergence, Mazur recovery, and the density claim (N4). The concrete tail spaces, arithmetic transfer, and transfer of summability and norm bounds are already proved. |

Here **Open** means that this Lean development does not yet contain the
checked provider. It does not mean that the ordinary mathematical statement
has been refuted or that it is a new open problem.

## Verification interpretation

The combined source check for the five initial modules and their nineteen
project dependencies succeeded in job
`job_ZCTw7NClrA7097BFcPaPA11Epa-GQCcY`, with exit code zero and
`verified: true`. Submitted-source SHA-256:
`f62a029a535db65fe055c3888d876ede01466c2fe861b964ad2e63807e6ff9f7`.

The audited endpoints for the prefix estimate, exact invariant/coboundary
identity, quantitative coboundary bound, finite centered Möbius identity,
quotient dilation identity, scalar summability, and conditional norm assembly
depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The final combined development check includes all eight new modules and
nineteen existing project dependencies. It passed in job
`job_H3BDnrCxPZVm2eNwx5awrKGwWOkal1rV`, with `verified: true`, exit code zero,
and submitted-source SHA-256
`376022424baaf8952e72ca2f01a98601658cfdd52fdbb7cc51a5687087a389c0`.
The additional Gram, induced-operator, concrete step reduction, full tail
transfer, tail summability, and conditional tail-norm endpoints also use
only those standard foundational axioms.

The final repository checkpoint validates the separated project modules.

There are no added `sorry`, `admit`, project axioms, or unsafe declarations.
Neither the conditional assembly nor its axiom report is an unconditional
Lean proof of (N2). RH and the full-energy exact-head repair obligation are
not established by this formalization.

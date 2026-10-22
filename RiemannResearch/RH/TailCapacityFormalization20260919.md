# Tail-capacity formalization: coverage and remaining RH obligation

Source: user-provided `RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`.
This report records the scope of the accompanying Lean modules. Stage `n`
uses moduli 2 through `n+1`; the Markdown's largest-modulus stage N is
`n = N-1`. Every capacity uses the entire Pareto Hilbert tail.

## Established declarations

| Written argument | Module | Main declarations |
| --- | --- | --- |
| Inverse Gram capacity, normalized constrained minimum, rank-one identities | Analysis/FiniteGramCapacity | `capacity_eq_norm_sq`, `constrained_completion`, `normalized_energy`, `capacity_rank_one_half` |
| Actual tail independence and point projection | RH/ParetoTailCapacity | `finiteTailAtom_independent`, `pointProjection_eq_synthesis`, `pointError_eq_inv_capacity`, `tailCapacity_tendsto_iff` |
| Exact screened source and Schur gain | Analysis/FiniteGramScreenedCapacity | `screened_gram_entry`, `screenedSource_eq`, `screened_linearIndependent`, `capacity_screened_add`, `capacity_telescope` |
| Complete signed CRT/digamma tail formulas | RH/ParetoFullTailCRT | `normalizedResidue_hilbert_tail_crt`, `normalizedResidue_full_tail_digamma`, `normalizedResidue_combination_full_tail_crt` |
| Actual dual certificate alternative | RH/ParetoTailCapacityDuality | `tailMinimum_increment`, `tailCapacity_monotone`, `canonicalTailCertificate_isCertificate`, `canonicalTailCertificate_norm_sq`, `tailCapacity_bounded_iff_exists_certificate` |
| Certificate regularity and signs | RH/ResidueTailCertificateRegularity | `tailCertificate_not_summable_firstMoment`, `tailCertificate_both_signs_arbitrarily_far` |
| Legal dilation correction and exact energy gain | RH/TailCapacityDilationCorrection | `dilationCorrection_mem_finiteSpace`, `dilationCorrection_tail_energy`, `dilationCorrection_capacity_gain` |
| Finite point-to-constant conversion, with exact modulus budget | RH/PointTargetDilationSynthesis | `pointDilationSynthesis_mem`, `finite_point_to_one_error` |
| Omitted-prime obstruction | RH/OmittedPrimeResidueBarrier | `prime_jump`, `omitted_prime_point_error_bound`, `omitted_prime_tail_energy_bound` |
| Scalar logarithmic transfer | Analysis/PointLogarithmicTransfer | `point_lower_of_sqrt_comparison`, `capacity_upper_of_point_lower`, `exists_late_failure_of_fixed_contraction` |
| Actual dyadic rate obstruction, conditional on the Burnol envelope | RH/PointTargetLogarithmicBarrier | `dyadicPointError_pos`, `dyadic_point_envelope_of_log_envelope`, `point_no_fixed_dyadic_fraction` |

The last rate theorem assumes the explicitly named
`PointBurnolLogLowerEnvelope`; no provider is asserted. The full-tail CRT
formula uses already established progression integral/digamma identities.

## Conditional research reductions

`riemannHypothesis_of_tailCapacity_tendsto` proves Mathlib's
`RiemannHypothesis` from `TailCapacityDivergence`.
`riemannHypothesis_of_fullCapacity_tendsto` gives the equivalent full-Gram
saturation implication. `riemannHypothesis_of_no_tailCertificate` proves the same conclusion from
nonexistence of an actual Hilbert tail certificate. These inputs are not
axioms and neither is discharged.

The decisive missing theorem remains:

```lean
Tendsto tailCapacity atTop atTop
```

Equivalently, one must exclude every vector satisfying
`IsResidueTailCertificate`. Nonnegative gains, finite strict improvements,
and finite numerical data do not imply that their sum diverges.

## Why the regularity theorem does not finish the proof

Hilbert membership does not imply the absolute first-moment condition
used in `tailCertificate_not_summable_firstMoment`. For example, the
anchored sequence f(1)=0 and f(n)=(-1)^n for n>=2 has squared Pareto norm
1/2, has both signs arbitrarily far out, and has divergent absolute first
moment. It is the actual Hilbert vector
`hilbertOne - 4 • residueAtom 0 + paretoPointHilbert 0`.

This example is not claimed to satisfy the certificate pairing equations.
It explains why a new argument using those equations is needed; it is
neither a counterexample to RH nor a refutation of a possible arithmetic
regularity theorem for certificates.

## Coverage limits

The determinant ratio, the strong convergence/minimum-norm uniqueness
form of the canonical certificate, the explicit hypothetical off-line
zero certificate and its sharpened Mellin bound, the full cumulative
dilation-correlation divergence criterion, the original exact-head conditional-mean transfer, and the classical RH converse
are not newly formalized in this change.

The logarithmic lower envelope still needs a Lean version of Burnol's
analytic lower bound, its continuous-to-discrete comparison, and the
logarithmic scale asymptotics. The finite point-to-constant construction
and scalar transfer steps are separate checked ingredients. Burnol's
[Theorem 1.3](https://arxiv.org/pdf/math/0103058) supports the cited
analytic input; it does not supply capacity divergence.

Floating-point values in the source document remain exploratory and are
not interval-certified Lean arithmetic.

No unconditional RH declaration, `sorry`, `admit`, project-local
`axiom`, or `unsafe` declaration is added.

## Verification and unconditional RH attempt

The combined source check succeeded in job
`job_z_w0zMtLJV63U3913JnFY5fXFUZQ-kVn`.
The selected capacity, CRT, regularity, obstruction, finite-transfer, rate,
and conditional RH declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`.
This axiom audit does not discharge hypotheses appearing in their types.

A separate unconditional RH attempt, job
`job_UqapgWzdQZ0QoxEz8G2d2dStKWl2AAzR`, applied the checked capacity
implication and asked `aesop` to close the remaining limit. Lean rejected
the incomplete proof with the exact remaining goal:

```text
B : ℝ
⊢ ∃ a, ∀ (b : ℕ), a ≤ b → B ≤ tailCapacity b
```

This is the required divergence itself. The failed tactic is not a
refutation of RH. No failed proof or placeholder was saved as a Lean theorem.
The final checkpoint validates the ordinary module imports and publication.

Publication integration preserves the newer origin/main additions at base
`fa2b00a919246d5b15e5e5c1e055993a85ffeb8c`; the initial verified development remains
saved at local commit `b946d8273c7c399239ce0d75478979cc66b67193`.

# Density-augmented prime and squarefree approximation — 8 November 2026

Source: user-provided residue-quotient argument, formalized in the
`RiemannResearch.RH.QDensityMetric` namespace.

## Definitions and exact identities

- `QDensityMetric.lean` defines the continuous linear density operator
  `B = (1 / zetaTwo) • (id + QReciprocalMetric.D)`.
- `qSequence_B_physical` identifies its positive physical multiplier as
  `(n + 1) / (zetaTwo * n)`; `weight_mul_density` checks `P(n) B(n) = Q(n)`.
- This `B` is the density `dQ/dP`. The older `QShiftedReciprocal.B`
  divides by `n + 1` and remains a distinct operator.
- `QDensityAugmentedSpan.lean` defines `approximation m = m • D (qResidue m)`.
  `approximation_sequence` gives `(n mod m) / n`.
  `approximation_eq_density_combination` proves the exact identity
  `approximation m = (zetaTwo * m) • B (qResidue m) - m • qResidue m`.
- `approximation_error_norm_sq` is the full infinite Q-energy identity.
  No omitted-tail estimate is assumed.

## Unconditional closure results

- `approximation_tendsto`: convergence in the complete Q-Hilbert norm.
- `one_mem_augmentedClosure_of_unbounded`: every unbounded conductor set
  suffices after adjoining its density images.
- `one_mem_prime_augmentedClosure`: primes alone suffice.
- `one_mem_squarefree_augmentedClosure`: one belongs to the closed span
  of `g_m` and `B g_m` for squarefree `m > 1`.
- `map_augmentedSpan` and `pareto_one_mem_squarefree_augmentedClosure`:
  the same physical squarefree generator family has one in its Pareto closure.

The only hypothesis in the general family theorem is unboundedness of that
family. The prime and squarefree specializations have no domain-specific
hypotheses. None of these declarations asserts an RH proof, unaugmented
legal-span membership, or density of the entire augmented space.

## Verification provenance

The complete standalone proof passed server job
`job_x7Frhgf8wYgglkoUGqEnNL0r4YUpfb5u` with exit code 0 and
`verified = true`. Its two final closure theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.
The server reported 30.401 seconds for verification, after about 149 seconds
queued. This is distinct from workspace-opening and transport delays.

The repository module check and four-theorem axiom audit also passed as
`job_piYkTWWPVwKoHsY8ktS25358MjmoXXJQ` (exit code 0, `verified = true`,
25.004 seconds reported by the server, no queue delay). The general, prime,
squarefree, and Pareto declarations all use only the three standard foundations
listed above.

This integration separates the reusable density operator from its approximation
application and exports both modules through `RiemannResearch.lean`.
Publication requires the repository's server checkpoint for the integrated
source; the earlier standalone check alone does not certify that integration.

## Squarefree density-image obstruction

The module `RH/QDensitySquarefreeObstruction.lean` distinguishes the span of
density images alone from the augmented span above. Here `B` is exactly
`QDensityMetric.B = dQ/dP`, not the shifted reciprocal operator.

Its continuous functional is
`Lambda(f) = f(1)/2 - 2*f(2)/3 - 3*f(3)/4 + 4*f(4)/5`.
The signed identity `densityFourSite_B` gives
`Lambda(B f) = (f(1) - f(2) - f(3) + f(4))/zetaTwo`.
Thus `densityFourSite_B_qResidue` vanishes for every conductor other than four,
whereas `densityFourSite_qOne` is exactly `-7/60`.

Established declarations, with no domain-specific hypotheses:

- `one_not_mem_densityClosure_of_four_not_mem`: any conductor family omitting
  four has density-image closed span excluding one.
- `densityClosure_ne_top_of_four_not_mem`: that closed span is proper in QHilbert.
- `one_not_mem_squarefree_densityClosure` and `squarefree_densityClosure_ne_top`:
  squarefree density images cannot approximate one and are not dense in L²(Q).
  The indexing set includes every squarefree natural number; restricting to
  conductors greater than one cannot remove the obstruction.
- `pareto_one_not_mem_squarefree_densityClosure`: the same physical density
  images cannot approximate one in the Pareto norm.

The prime family is a subfamily, so it has the same obstruction. The earlier
augmented-span membership theorem remains valid: it uses both `g_k` and `B g_k`.
The full integer conductor family includes four, so this obstruction does not
settle its density.

The isolated Lean proof passed Bazel/BuildBuddy job
`job_DMDpMKlpxprVeg4TdcD0Hl7FYoG7zvSL` with exit code 0 and
`verified = true` (63.635 seconds reported for verification).
This is scoped proof evidence; publication additionally requires the full-project
server checkpoint for the integrated source.

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

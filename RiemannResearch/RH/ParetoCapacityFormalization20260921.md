# Pareto capacity formalization — 21 September 2026

Source: user-provided argument in
`RH_Pareto_Capacity_Exact_Bounds_and_Critical_Shape_2026-09-21.md`.
This report records the precise declarations and their assumptions.

## Stage convention

The repository's stage `n` uses generators g_2,...,g_(n+1).
Thus the source note's N equals n+1.
The original weights are 1/[j(j+1)] at physical site j>=1.
New shape weights are a^(-alpha)-(a+1)^(-alpha); the physical tail starts at a=2.

## Original Pareto(1) capacity

The existing `ParetoTailCapacity.pointError_eq_inv_capacity` proves
pointError(n)=1/(tailCapacity(n)+2). Existing finite Gram and
`TailCapacityJointCorrections` declarations give the exact constrained
minimum 1/tailCapacity(n) for nonempty dictionaries.

`FirstCoordinateTailGap.tailCapacity_bounded_iff_not_RH` now states the
requested bounded-capacity equivalence directly. It takes the explicit
argument

```lean
hDensity : RiemannHypothesis → closedSpace = ⊤
```

This is the classical RH-to-density direction in Bagchi, Theorem 1:
https://arxiv.org/pdf/math/0607733.
The provider has not been proved in this addition. No project axiom is
introduced. The already-established direction from not RH to positive gap
does not require that argument. No positive or zero limiting gap is proved.

## Concrete rough-integer certificates

Module: `RH/ParetoRoughTailCertificates.lean`.

- `differenceCertificate` is the actual two-point Hilbert vector
  p(p+1)e_p-p(p-1)e_(p-1), with p=k+2.
- `differenceCertificate_norm_sq` proves its exact squared norm 2p^2.
- `differenceCertificate_inner_residue` retains the signed divisor term:
  its pairing with g_d is 1/d minus the indicator of d dividing p.
- `differenceCertificate_observation` proves actual finite-dictionary
  feasibility when p avoids all dictionary moduli.
- `tailCapacity_le_rough_certificate` and
  `tailCapacity_le_prime_certificate` bound the existing full-tail capacity.
- `differenceCertificate_sum_norm_sq` proves orthogonal finite averaging.
- `averagedRoughCertificate_norm_sq` and its observation theorem construct
  an actual feasible vector with squared norm the reciprocal of the
  finite inverse-energy mass.
- `roughCertificate_affine_energy_completion` proves exact finite-family
  optimality for every signed coefficient vector with sum one:
  energy=1/mass + squared distance from the inverse-square average.
  The corresponding lower-bound and equality-characterization theorems
  prove that this average uniquely minimizes energy within the family.
- `tailCapacity_mul_coprimeMass_le` passes to the entire infinite coprime
  sum using the proved summability of the actual reciprocal-square terms.
- `tailCapacity_le_eulerProduct` proves the full finite Euler-product bound
  for any nonzero even common multiple P of the dictionary moduli.
- `tailCapacity_le_factorial_eulerProduct` uses P=(n+1)! explicitly.
  Its prime factors are precisely the primes at most n+1.

The Euler-product identity is supplied by the existing
`ParetoEulerProduct.coprimeReciprocalSquareMass_eulerProduct`; it is not
assumed. All full-tail mixed terms remain in the actual Gram capacity.

The new finite-stage helpers in `ParetoTailCapacityDuality` prove
`finiteTailCertificate_energy_completion` and
`finiteTailCertificate_capacity_le`. In particular a feasible trial z has
exact energy C_n + ||z-tailMinimum(n)||^2. Infinite-dictionary observations
are not required for these finite conclusions.

These upper bounds are not uniform in the growing dictionary. They do not
prove either boundedness or divergence of the optimal capacities.

## General Pareto shapes and the critical boundary

Module: `RH/ParetoShapeMellinEnergy.lean`.

The definitions use the actual complex power difference and the actual
Pareto cell mass. Theorems establish:

- Positivity and the exact integral identity for `shapeCellWeight`.
- Weighted cell Cauchy–Schwarz.
- Summability of actual Mellin cell energy whenever
  0<alpha<2 Re(s).
- The full tail bound
  ||s||^2 a^(alpha-2 Re(s))/(alpha(2 Re(s)-alpha)).
- For the normalized coefficient
  m_s(a)=(a^(-s)-(a+1)^(-s))/s, the corresponding bound without ||s||^2.
- `criticalNormalizedTailEnergy_le`: the exact displayed upper-bound
  constant 2^(alpha-1)/(alpha(1-alpha)) for 0<alpha<1.
- `criticalShapeMellinCellEnergy_lower`: a harmonic lower bound at alpha=1.
- `criticalNormalizedTailEnergy_not_summable`: genuine nonsummability of
  the normalized critical-line certificate at alpha=1.

These analytic theorems are unconditional and do not assume zeta vanishing.
The boundary proofs reuse the existing critical-mode energy obstruction.

## Full finite legal combinations for the new shapes

Module: `RH/ParetoShapeCapacity.lean`.

`shapeLegalCombination` is the actual finite complex combination of all
residues in the indicated dictionary. `shapeLegalTailEnergy` is its entire
infinite weighted tail. Its summability is proved from boundedness of finite
residue combinations and summability of the actual shape weights.

`zero_shapeLegal_tail_hasSum` proves the exact signed arithmetic zero
pairing, using the existing Mellin residue formula.
`zero_shapeLegal_capacity_bound` then proves the uniform coefficient
inequality with the explicit tail constant.
`shapeFiniteCapacity` is the actual supremum of the squared head value
divided by the full tail energy, over every finite coefficient vector.
`zero_shapeFiniteCapacity_le` bounds this supremum.
`critical_shapeFiniteCapacities_bddAbove` bounds all stages for 0<alpha<1.

The last critical-line theorem explicitly assumes

```lean
hz : riemannZeta (MellinFrequency.criticalPoint t) = 0
```

It assumes neither RH nor not RH. Classical existence of critical-line
zeros is known, but a kernel-checked existence provider is not added here.
Thus the proof in Lean is parameterized by any actual critical-line zero;
the analytic energy threshold itself needs no such input.

## Certificates whose support escapes into the tail

Module: `RH/ParetoTailCertificateEscape.lean`.

`residue_two_tail_norm_sq_le` bounds the actual g_2 tail energy by
1/[4(N+1)]. With the actual normalization <g_2,z>=1/2 and physical
support at sites j>=M, `normalized_certificate_support_energy_lower`
proves ||z||^2>=M. The accompanying
`normalized_certificate_escaping_support_energy_tendsto` proves that
the squared norms of any such family tend to infinity. These results
have no RH or zeta-zero hypotheses and use the complete infinite tail.

## Scope and acceptance

The original note's continuous ambient-space caution is explanatory:
these arithmetic generators are unit-cell step functions. Non-step
annihilators in a larger continuous space do not automatically obstruct
either the constant or first-cell target.

The capacity, Euler-product, shape-energy, critical-boundary,
finite-family optimality, and general moving-support lower bound are
formalized above. The full Euler bound is obtained by finite exhaustion;
this addition does not separately construct the infinite averaged Hilbert
vector or prove its infinite-family equality characterization.

Development candidates were checked in serialized Lean jobs. Final
acceptance is the repository checkpoint, which audits the source, builds
changed modules and their local reverse dependents, and publishes only
after successful validation. The publication commit is recorded in Git.
No sorry, admit, local axiom, or unsafe declaration is introduced.

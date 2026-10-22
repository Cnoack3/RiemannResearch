# Compressed-dilation reconstruction of the RH obstruction

Date: 2026-09-22

## Outcome

This attempt does not prove the Riemann Hypothesis. It proves an exact
reconstruction of the existing projection residual from the first-coordinate
defect, with a geometric error bound, and proves that the compressed integer
dilations of that one defect separate the entire annihilator space.

Source: independently developed continuation of the user's Pareto
projection-defect and all-annihilator handoff. No novelty is claimed.

## Exact setting

Let H be the real sequence Hilbert space with weights 1/[n(n+1)], n >= 1.
Let S be the closed span of g_d(n) = {n/d}, d >= 2, let Q be the orthogonal
projection onto K = S^perp, and put r = Q1, rho = Qe_1.
The library realizes these as limitResidual and firstHeadResidual.

For B >= 1 define U_B f(n) = f(floor(n/B)), with f(0)=0.
The project's hilbertDilation is B U_B. Define the actual bounded operator

    A_B = Q U_B

on all of H. The new module proves, without RH or a tail-bound hypothesis,

    A_B(H) subset K,       A_B(S) = {0},
    A_B Q = A_B,           A_B A_C = A_(BC),
    ||A_B x||^2 <= (1/B)||x||^2.

Here A_1 = Q on H; it acts as the identity on K.

## Exact reconstruction

The first-point identity e_1 = 1 - U_2 1 becomes

    rho = r - A_2 r.

For every M >= 0, Lean proves

    r - sum_{j=0}^{M-1} A_2^j rho = A_2^M r,

and

    ||r - sum_{j=0}^{M-1} A_2^j rho||^2 <= 2^(-M) ||r||^2.

The partial sums converge strongly to r. The generic proof is valid for a
continuous linear map A whenever ||Ax||^2 <= q||x||^2 for every x, with
0 <= q < 1; it does not assume contraction only at the initial vector.

All terms of the actual reconstruction belong to K. This convergence
reconstructs the possible obstruction r; it does not establish legal
approximation of 1.

## One defect detects every obstruction

The verified theorem annihilator_eq_zero_of_inner_firstHead_orbit_zero states:

    z in K and <z, A_B rho> = 0 for every positive integer B imply z = 0.

The proof first propagates these equalities through the dyadic powers using
A_B A_2 = A_(2B), and then takes the verified strong reconstruction limit.
This yields <z, A_B r> = 0. Projection orthogonality identifies that pairing
with <z, U_B 1>. The integer threshold functions U_B1 separate every vector
in H, so z = 0.

In ordinary Hilbert-space terminology the orbit {A_B rho: B >= 1} has dense
linear span in K. The Lean declaration proves the exact separation statement
above, not an additional packaged closed-span equality.

## Why RH is still missing

The equation r = rho + A_2 r has the forcing vector rho. A strict contraction
does not force its solution to be zero when this forcing vector is nonzero.
The reconstructed series determines r from rho, but proves no estimate
forcing rho = 0.

The previously verified sufficient condition for actual Mathlib
RiemannHypothesis remains a bounded cofinal subsequence of

    N ||tail_N rho||^2.

That upper-bound provider is still open. The unconditional all-annihilator
theorem proves that every nonzero rho has these quantities tending to
infinity; it does not prove their boundedness. The alternative target is
divergence of the actual first-head capacity. That divergence is also open.

## Formal source

- Analysis/ContractiveNeumannReconstruction.lean:
  finite identity, squared error estimate, and strong convergence.
- RH/ParetoResidualDilation.lean:
  actual compressed semigroup, first-head reconstruction, and annihilator
  separation by the compressed orbit.

The new results have no domain-specific assumptions. The generic module's
explicit linear-algebra assumptions are discharged in the actual RH module.
No sorry, admit, project-local axiom, or unsafe declaration is introduced.
Final verification and publication are reported with the checkpoint result.

Combined source verification: job_geHw5Bsra-F-98k2VqZheRjR7QZBZvto,
exit code 0, verified true, no warnings. Audits of the generic convergence,
actual semigroup, actual geometric error, and annihilator separation report
only propext, Classical.choice, and Quot.sound. The existing RH consumer's
bounded-tail assumption was printed explicitly and remains undischarged.

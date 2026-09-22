# Pareto signed-average continuation in Lean — 22 September 2026

Source: the attached `Pareto_Direct_Attempt_Sublinear_Energy_2026-09-22 (2)(1).md`, Sections 3–4 and 7. This continuation adds 20 theorem declarations. No proof of RH is claimed.

## Current arithmetic-to-energy chain

During this task a concurrent session published commit `8f80cd8cb6899e67cd1c2c675c904cc06c73b3a4`. It supplied the arithmetic-to-energy proof that this session had also independently checked. The final continuation uses those published declarations and does not add duplicate versions.

`NumberTheory/FiniteFloorTail.lean` and `RH/CanonicalMobiusWindowCancellation.lean` prove the finite floor-tail identity and fixed-window cancellation estimate. `RH/CanonicalMobiusSublinearEnergy.lean` proves

\[
\frac{\|u_N\|_P^2}{N}\le\frac1N+b^2+\frac4K
\]

from the intermediate-window bound |u_N(j)|≤bN for N<j≤KN, retaining the complete infinite far tail. Its theorem `canonicalMobiusHilbert_sublinear_of_mobius_cancellation` proves

\[
M(N)/N\to0,\quad m_N\to0
\quad\Longrightarrow\quad
\|u_N\|_P^2/N\to0.
\]

Both classical PNT limits remain explicit hypotheses: their checked providers are not supplied here. This is a formalization gap for known arithmetic inputs, distinct from the open research estimates below.

The current `ParetoSublinearResidualTail.lean` derives normalized residual-tail divergence when the residual is nonzero. This continuation adds `riemannHypothesis_of_mobius_cancellation_and_bounded_tail`, proving actual Mathlib RH from the two arithmetic limits and

\[
\exists C\in\mathbb R:\quad N T_N\le C
\text{ for arbitrarily large }N,
\qquad
T_N=\sum_{j>N}\frac{|r(j)|^2}{j(j+1)}.
\]

That upper bound is not proved.

## Signed averages and complete covariance

`RH/CanonicalMobiusSignedAverages.lean` defines actual finite Hilbert-space combinations

\[
F=\sum_{k\in s}\lambda_k u_k.
\]

It proves finite-span and closure membership, and exact head agreement through N whenever k≥N on s and Σλ_k=1. It also defines the manuscript's dyadic average and verifies its exact head.

The covariance entries are identified with their complete infinite weighted sums:

\[
\mathcal C^{(N)}_{k\ell}
=\sum_{j>N}\frac{u_k(j)u_\ell(j)}{j(j+1)}.
\]

`signedMobiusAverage_tail_energy` and `signedMobiusAverage_norm_sq` prove the exact identities

\[
\|F\mathbf1_{j>N}\|_P^2
=\sum_{k,\ell\in s}\lambda_k\lambda_\ell\mathcal C^{(N)}_{k\ell},
\qquad
\|F\|_P^2
=\frac{N}{N+1}+\sum_{k,\ell\in s}\lambda_k\lambda_\ell\mathcal C^{(N)}_{k\ell}.
\]

Every signed cross term is retained. The quadratic form is nonnegative.

`riemannHypothesis_of_frequently_bounded_signed_covariance` proves:

**For finite signed averages with coefficient sum one and all indices at least N, a fixed upper bound on their full tail-covariance energies along arbitrarily large N implies actual Mathlib RH.**

This criterion requires no PNT premise or sublinear-energy premise. Its boundedness provider remains open.

## Finite-stage singularity is now resolved

`RH/CanonicalMobiusTailNondegeneracy.lean` proves that every finite legal vector is periodic in physical coordinates. A factorial supplies a common period for all finitely many conductors. If its entire infinite tail vanishes, its first physical value must therefore vanish.

Consequently:

- `signedMobiusAverage_covariance_pos`: every admissible finite average with N≥1 has strictly positive tail energy;
- `signedMobiusAverage_covariance_zero_imp_sum_zero`: every zero direction of the actual tail quadratic form, over positive candidate indices, has total coefficient sum zero.

Thus the source's general possibility of an admissible covariance-null vector cannot occur for these finite canonical families. This is a specialization, not a refutation of the manuscript's general singular-matrix statement. It gives no uniform lower bound as N grows and does not exclude asymptotically small covariance energy.

## Precise remaining work toward RH

- **Arithmetic formalization:** supply checked providers for M(N)/N→0 and m_N→0.
- **Open research estimate:** construct a bounded cofinal subsequence of the actual normalized residual tails, or of the signed tail-covariance energies.
- **Not established:** RH, vanishing projection residual, convergence of optimal errors to zero, a bounded subsequence of canonical energies, the logarithmic refinement, or the inverse/pseudoinverse optimizer.

The important new research target is the actual signed quadratic form above. Finite-stage singularity cannot make its admissible energy exactly zero.

## Verification and reproducibility

The earlier combined independent development passed Lean in job `job_KXI8O7mPEuQJ5RRS6A7h_C0jfkgVR9E-`. Its standard axiom audits reported only `propext`, `Classical.choice`, and `Quot.sound`. Publication of an initial partial checkpoint encountered a concurrent import-file conflict; that unpublished work was retained. The final continuation was moved to the current published base, preserving the concurrent arithmetic development.

Current project workspace token: `ws_YCBn4_yOwTvJ6_8f5sZf9beWp7vIYaNZ`.
Base commit: `8f80cd8cb6899e67cd1c2c675c904cc06c73b3a4`.

The final combined check and affected-module publication checkpoint provide the acceptance record. No `sorry`, `admit`, project-local axiom, or unsafe declaration is introduced. Standard axiom audits do not discharge the explicitly stated arithmetic or research hypotheses.

Final combined source check: job `job_B9mr_r762eGfgaLBkud2d0vlvsUAgLkH` succeeded with exit code 0, `verified: true`, no warnings, and only the standard axioms for the three principal conclusions. Publication uses changed-module and local reverse-dependent validation.

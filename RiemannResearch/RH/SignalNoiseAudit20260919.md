# Signal-to-noise PDF formalization and remaining obligations

Source: Christian Noack, user-provided *A Signal-to-Noise Program for the Riemann
Hypothesis*, July 21, 2026, file signal_to_noise_RH_program (2)(1).pdf.
Audit date: September 19, 2026.

## Established finite and Hilbert results

- IntegratedRamanujanCovariance.packetCombination_variance_pos proves strict
  full-Pareto variance for nonzero finite combinations of distinct conductors
  greater than one. It supplies no uniform spectral estimate.
- LinearAlgebra/FiniteSignalNoise proves covariance completion, unique
  minimization, the Rayleigh inequality and attainment, and the scalar
  signal lower bound for a symmetric positive definite matrix with a
  specified solution of its normal equations.
- RamanujanSignalNoise constructs that solution for the actual arithmetic
  covariance from the actual Gram inverse. Writing \(m\) for the projected
  mass, it proves \(m<1\), \(Cv=\lambda\), uniqueness,
  \(R=m/(1-m)\), error \(1/(1+R)\), and optimal coefficients \(v/(1+R)\).
  No arithmetic inverse witness is an unresolved hypothesis.
- ConductorDegreeObstruction.fixed_prime_support_one_not_mem_closure proves
  Conjecture 8.2, allowing nonsquarefree conductors too. It uses the existing
  continuous Mobius coordinate and large squarefree witness. The theorem
  error_identity retains the exact Riesz correction; centered_signal_bound
  gives the full Hilbert variance bound.
- ParetoOccurrenceGreen telescopes actual CRT progression weights into
  exact digamma block sums and occurrence Green entries.
- MobiusFloorTail proves the floor-coordinate head/tail split and the
  corrected residual conditional on the explicitly stated inclusion-exclusion
  equality. Its unconditional arithmetic endpoint theorem refutes the
  printed constant-free expression.

File stems above identify modules, not necessarily declaration namespaces.
Most arithmetic results live in RiemannResearch.RH.Pareto; the optimizer
and degree obstruction have their own subnamespaces.

## Corrections to preserve in future work

If \(C+1=T_{\le x}+T_{>x}\), then
\(C-T_{>x}=T_{\le x}-1\), not \(-T_{\le x}\).
The printed identity fails at \(r=1\). The general equality identifying
the coprime count with the Mobius floor sum is an explicit hypothesis of
the current correction theorem; it has not been smuggled in as an axiom.

The occurrence gap formula must retain its initial fixed-zero block:
at \(x=11\), the first free position is 14 but \(C(13)=1\).
Proposition 5.2 requires joint covariance nonsingularity.
Proposition 9.2 requires positive free-atom mass, e.g. integer \(x\ge3\).
The Green inverse convention must include its sign and Pareto centering.
Conjecture 11.2 must concern squared norm \(O(x^2\log x)\).

## Paper-level analytic progress and open obligations

A separate detailed audit proves \(q_x^{occ}=O(x^{-1/4})\), and more generally
\(O_\varepsilon(x^{-1/3+\varepsilon})\), by adapting the original factored
Dirichlet polynomial in Heath-Brown's *The Differences Between Consecutive
Smooth Numbers*, Section 2, https://arxiv.org/pdf/1808.02947.
The short sum in a squarefree-smooth gap need not be zero. Its nonsquarefree
mass is bounded by counting repeated-prime multiples. The original
polynomial is retained unchanged, so the later estimates still apply.
This is an analytic proof in the accompanying audit, NOT a Lean theorem,
a new project axiom, or an RH proof. Formalizing its external analytic input
and transfer argument remains Open.

For the witness at the product \(m\) of the first \(D+1\) primes, paper-level
estimates \(B_m\le8m^2\) and PNT imply the necessary degree growth
\(d(x)\log d(x)\ge(1/2-o(1))\log\log x\) for the proposed scalar bound.
These asymptotic estimates are not newly formalized.

- **Open:** atom-reuse convergence \(A_x\to0\), hence the exact-head conjecture.
- **Open:** Conjecture 6.2's scalar variance rate, Open Problem 7.2, and the
  corrected squared-distance version of Conjecture 11.2.
- **Open:** a proof of the shell divergence in Conjecture 11.1. Unbudgeted
  cofinal reindexing is RH-equivalent and supplies no independent estimate.
- **Open formalization:** the Nyman-Beurling/RH converse, the specific
  primorial occurrence and gcd-atom subspace identifications, their
  tridiagonal Green duality, and the full arithmetic count identity.
  Existing ConductorProjectionRH supplies the sufficient closure-to-RH
  implication, not that converse.

All new source proofs use only ordinary Mathlib foundations.
No unresolved analytic research obligation is inserted as a provider
of an unconditional theorem.

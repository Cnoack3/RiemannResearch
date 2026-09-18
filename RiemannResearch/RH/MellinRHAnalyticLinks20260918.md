# Chebyshev Mellin transform and RH: verified analytic links

Date: 2026-09-18.

## Established statements

Write
M(s) = -zeta'(s)/(s*zeta(s)) - 1/(s-1).

RH/ChebyshevMellin.lean proves integrability and the actual identity

    integral_(1,infinity) (psi(x)-x) * x^(-s-1) dx = M(s), Re(s)>1.

Here psi is Mathlib's Chebyshev.psi and zeta is its riemannZeta.
This is a complex Bochner integral, with complex powers on positive real x.
The proof uses checked Abel summation, the von Mangoldt Dirichlet series,
and the unconditional linear bound for psi.

Analysis/LogDerivZeroOrder.lean proves the general local order calculation:
if f is analytic at s, has finite analytic order there, and f(s)=0, then
its logarithmic derivative has meromorphic order -1. No simplicity
hypothesis is used.

RH/ChebyshevMellinRH.lean proves:
- meromorphicAt_meromorphicError: M is meromorphic at every s != 1,
  including its possible poles at zeros.
- logDeriv_order_at_zero: the logarithmic derivative of zeta has order -1
  at every zero away from 1. Finiteness of the zeta-zero order is proved
  by an existing provider, not assumed in this specialization.
- meromorphicError_order_at_zero: M itself has order -1 at every zeta zero
  with s != 0,1.
- analyticAt_meromorphicError_iff: for s != 0,1, M is analytic at s if and
  only if zeta(s) != 0.
- riemannHypothesis_iff_error_analytic: Mathlib's RiemannHypothesis holds
  if and only if M is analytic at every s with 1/2 < Re(s) < 1.

The last proof uses zeta reflection and the already checked equivalence
between Mathlib RH and the critical-strip zero condition. It proves an
equivalence and supplies no proof of either equivalent assertion.

## Scope still open

These results discharge the initial Mellin identity, meromorphic extension
away from 1, the local zero/pole obstruction, and an exact RH analyticity
criterion. They do not establish convergence of the original integral for
Re(s)<=1.

Still requiring formalization are the signed-energy-to-holomorphy/Hardy
steps, the quotient by the report's reference Z_b, its pole cancellation
and zero multiplicities, cancellation of M's apparent singularity at 1
with the correct filled-in value, and the numerical residues -m_rho/rho.
A simple-pole order calculation does not determine that residue.

The actual SignedArithmeticDampedBound for every positive damping and
SignedArithmeticSubpolynomialBound for every positive exponent remain
unproved mathematical targets. Neither follows from the equivalence above.

## Verification and provenance

The combined concrete candidate passed Lean in
job_C7tfSrDmuJQwuxK2OYIL5jz2joUadUVg with exit_code 0 and verified true.
Axiom inspection of error_mellin_identity, meromorphicError_order_at_zero,
analyticAt_meromorphicError_iff, and riemannHypothesis_iff_error_analytic
reported only propext, Classical.choice, and Quot.sound.
The final project checkpoint validates the saved modules, exports, and
affected dependents; its publication commit is reported in the conversation.
No project-local axiom, proof placeholder, or unsafe declaration is added.

Source for the requested statements: user-provided
V_Zeta_Vector_Spaces_Research_2026-09-16.md, Sections 12-19.
The integral proof uses Mathlib's LSeries_eq_mul_integral_of_nonneg and
ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div.
The local proof uses analyticOrderAt_deriv_of_pos and meromorphicOrderAt_div.
No mathematical novelty is claimed.

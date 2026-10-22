# Hardy converse and boundary traces: exact Lean coverage

Date: 2026-09-18.

## Proved: strong boundary traces for represented finite-energy transforms

Analysis/WeightedMellinBoundary.lean defines boundaryTrace as the unitary
L2 Fourier transform of the logarithmic lift at the boundary exponent.
For FiniteEnergy f s, and EVERY real sequence sigma_n > s/2 tending to s/2:

- transform_boundary_L2 proves convergence of the actual interior Mellin
  transforms as L2 elements to boundaryTrace.
- transform_boundary_integral proves
  integral_R |M_f(sigma_n+2*pi*i*w)-boundaryTrace(w)|^2 dw -> 0.
- transform_boundary_difference_integrable proves these squared differences
  are genuinely integrable; the convergence is not an artifact of the
  totalized Bochner integral.
- boundaryTrace_norm_sq proves ||boundaryTrace||_2^2 = E_s(f).

No L1 assumption is imposed on the undamped logarithmic lift.
The boundary trace is not identified with the ordinary boundary integral,
which need not converge. No values of F on the boundary are prescribed.

## Proved: represented-function converse

Analysis/WeightedMellinConverse.lean proves:
- finiteEnergy_of_bounded_approximating_energies, via Fatou:
  bounded energies along exponents >=s tending to s yield endpoint finite
  energy and the same bound.
- finiteEnergy_iff_hardy_of_interior:
  under the explicit assumption that E_u(f) is finite for EVERY u>s,

      FiniteEnergy f s <-> HardyH2 (transform f) (s/2).

This is a proved converse within that represented class. It is not the
general representation theorem.

## Exact remaining formalization obligation

GeneralHardyConverse is a Lean Prop:

    for every alpha and F with HardyH2 F alpha,
    there exists measurable f with FiniteEnergy f (2*alpha),
    and transform f z = F z for every Re(z)>alpha.

It has NO proof and is NOT introduced as an axiom.
The standard classical half-plane Paley--Wiener theorem is the mathematical
result requested here; its general Lean formalization remains incomplete.

The missing analytic step is to recover the common time-domain function
from an arbitrary Hardy family. One route proves, for inverse Fourier
transforms u_sigma of the vertical L2 functions,

    u_b(t) = exp(-(b-a)*t) u_a(t), alpha<a<b.

This requires deriving horizontal covariance from holomorphy. Uniform
vertical bounds then force zero support on t<0; Fatou gives endpoint L2
integrability, and logarithmic change of variables gives the representation.
No proof of that covariance has been added.

hardy_boundary_of_general_converse proves the remaining assembly: IF
GeneralHardyConverse is supplied, every Hardy function has an L2 trace with
the stated square-integral convergence. Its representation premise remains
an explicit open obligation.

## Verification and RH scope

The combined candidate passed Lean in
job_CLqAvKPlHJP-pnAhGrTvvEyRgV3CKOFW, verified true, exit code 0.
Main theorem axiom checks show only propext, Classical.choice, and Quot.sound.
That axiom list does NOT discharge explicit theorem hypotheses.
The publication checkpoint separately compiles the saved modules.

No sorry, admit, project-local axiom, or unsafe declaration is added.
The signed arithmetic energy bound and RH remain unproved. Boundary
convergence is analytic infrastructure and supplies no arithmetic estimate.

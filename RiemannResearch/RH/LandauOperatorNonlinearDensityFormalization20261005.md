# GitHub suggestion: signed operator assembly and nonlinear density transfer

Source base: efa338295fe4ea9331e4f90086c4c7137feb5952. Research date: 2026-10-05.

## Exact retained objects

The actual residual is
E_d(T)=H_d(T)-I+T*C_d/(2*pi*N(T)).
The full C_d uses every integer frequency 1,...,d and every divisibility pair;
no composite conductor or prime-power interaction is removed. All actual
zeros retain analytic multiplicity and the original N(T) normalizer.

The new ActualLandauOperatorResidual module proves a Euclidean operator
remainder bound from the already checked actual rational scalar provider,
and a norm limit for log d(T)<=c*sqrt(log(T+3)), every fixed c.
This limit concerns E_d. The arithmetic main term remains in the equality;
it does not by itself prove a phase-Gram frame gap or RH.

LandauGrowingSupport retains exactly
exp(7ell/2-L)+L^2*exp(5ell/2-L)+L*exp(2ell-L).
The exact rpow identity and polynomial-exponential majorant give the
square-root-log support limit without a density premise.

## Nonlinear density input and its complete consumer

Write v(s)=4s/(3-2s), q=12M/(3-2delta)^2 and
A=K exp(q*delta-M*v(delta)). The explicit analytic premise is

    strictTail T s <= K exp(-M*v(s)) + E.

Convexity yields the tangent envelope A exp(-q*s)+E.
The exact closed cosh budget keeps both finite endpoints and the negative
q+ell companion term. The additive remainder becomes
E*(cosh(ell/2)-1). Thus a fixed low-height count and all logarithmic
remainders must remain in E until an independently justified absorption.
The operator consumer keeps d/(2*N(T)), and the finite invertibility
consumer still requires its actual scalar density, Landau norm and gap.

The stable cutoff is physically admissible precisely when
R<=M-ell/2, under ell>=0, R>=0 and B=4M-3ell+2R>0.
A positive cutoff margin automatically makes q>ell. Its exact cancellation
is exp(ell)*exp(ell*delta-M*v(delta))=exp(ell-R).
These are scalar results and do not supply the analytic density premise.

## Sources and verification boundary

Chourasiya--Simonic, An explicit form of Ingham's zero density estimate,
Theorem 1 and Table 1:
https://arxiv.org/html/2507.15184v2#S2.SS1 .
The theorem bounds a difference of actual inclusive counts and therefore
retains its finite N(sigma,H). The published analytic proof still requires
Littlewood counting, Gabriel convexity, mollifier bounds and the fourth
zeta moment; those providers remain Open in Lean.

Gonek, A Formula of Landau and Mean Values of zeta(s), Theorem 1 (1985):
https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf .
This supports the contour strategy. The new assembly uses the repository's
proved sufficient fixed-c=2 scalar estimate, not an imported sharper
classical Landau bound.

Wolfram Language returned zero for the nonlinear rate and tangent-remainder
identities and exp(-p*h) for the exact optimized support cancellation.
These are auxiliary symbolic checks. Isolated Lean checks verified the
scalar cutoff and envelope proofs, the generic Euclidean norm bound and the
finite-tail additive-error transfer. The integrated actual-zero consumers,
import graph and publication are validated by the checkpoint and rebuild.
No density provider, frame gap or Riemann Hypothesis is asserted by citation.

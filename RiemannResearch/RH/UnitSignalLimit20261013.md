# Unit-signal residue limit: Lean continuation and rate audit

Source: user-provided `Final_Limit_Unit_Signal_Residues_2026-10-11 (1).md`.
Date: 2026-10-13 (verification resumed).

Continuation on 2026-10-18: the actual dilation/detector bridge and the
inverse-Gram first-coordinate formulas are now supplied by
`QFloorDyadicEnergy.lean` and `ZetaTwoUnitSignalDilation.lean`.
See [the exact identities and remaining scalar obligation](UnitSignalDilationResearch20261018.md).

## Scope and verification

This continuation separates the general Hilbert-space normalization, the
scalar consequences of the dilation estimate, and the actual inverse-square
arithmetic realization. A conditional theorem does not establish its hypotheses.
The source files were initially drafted while the Lean server was unavailable.
The verification and publication status must be taken from the accompanying
server report; merely possessing these files is not evidence of a kernel check.

`Analysis/UnitSignalProjection.lean` constructs the normalized optimizer from
Mathlib's orthogonal projection, proves the exact Pythagorean remainder,
uniqueness, the quarter-mass error formula, the nested-stage difference
identity, and convergence under convergence of the underlying projections.

`Analysis/UnitSignalTwoScale.lean` supplies real-algebra consequences of the
explicit squared dilation bound. It does not assume that an unknown arithmetic
estimate has been proved for the actual residue optimizers.

`RH/ZetaTwoParitySignal.lean` proves the complete real multiples-mass identity,
the actual even and odd vectors, their norms and orthogonality, and positivity
of the conductor-3 pairing. `RH/ZetaTwoUnitSignal.lean` uses those vectors to
instantiate the normalization theorem, constructs the all-conductor finite
stages and closed span, and proves unconditional convergence of the actual
normalized optimizers and the exact limiting-error formula. The four separate modules passed server job
`job_gz3QFNBGiQj80LxZBDsVlHlig5_Dd4HE` with exit code 0 on 2026-10-13.
Eight selected axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. Publication was resumed on 2026-10-18 after a cache-upload
failure; the final checkpoint validates the source integrated with current
main and its exports before publication.

## Exact analytic normalization

For target energy q and nonzero projected target s, the optimizer with the
required signal and zero complementary signal is U=(q/||s||^2)s. If
delta=||Y-s||^2, then

    ||U-Y||^2 = q*delta/(q-delta).

Every admissible F satisfies the exact identity

    ||F-Y||^2 = ||U-Y||^2 + ||F-U||^2.

Taking q=1/4 gives delta/(1-4*delta). This proves uniqueness and the
minimum value without dropping a remainder. For nested spaces, it also gives
||U_L-U_M||^2=e_M-e_L. Convergence of projections and positivity of the
limiting projected energy imply convergence of the normalized optimizers;
vanishing of the limiting error is not used in that convergence argument.

## A square-root-free detector

Write kappa=zeta(2), e=e_infinity and ell=U_infinity(1). The manuscript's
head identity and dilation bound give

    2*(kappa*e + ell)^2 <= (kappa*e)^2.

Indeed, with t=1-4*delta>0, e=delta/t and ell=-r(1)/t, its left side is
2*(kappa*delta-r(1))^2/t^2. The bound before normalization is
2*(kappa*delta-r(1))^2 <= kappa^2*delta^2.
For kappa>0 and e>=0, the normalized polynomial inequality implies ell<=0
and (ell=0 iff e=0). The abstract scalar module retains the polynomial
inequality as a hypothesis. The concrete provider is now established by
`allConductorLimit_polynomial_detector` in `ZetaTwoUnitSignalDilation.lean`.

An eventual or subsequential bound

    ell_M >= -(kappa/4)*e_M - epsilon_M,  epsilon_M -> 0,

combined with convergence and the limiting detector forces e_infinity=0.
This is a conditional reduction, not an established bound for the optimizers.

## Finite estimates and an important obstruction

Put x=delta_(2M), y=delta_M, z=(1-4*x)*ell_(2M)/kappa. The exact two-scale
identity yields (x+z)^2<=x*y/2. The algebraic consequences include

    z >= -b       ==> x <= y/2 + 2*b,
    z >= -x/4-b   ==> x <= (8/9)*y + (8/3)*b.

Thus a single-stage bound ell_(2M)>=-kappa*e_(2M)/4 implies
delta_(2M)<=(8/9)*delta_M. This finite implication is valid. Requiring that
same strict contraction along every sufficiently large consecutive dyadic
stage is NOT a viable RH strategy: it would force a polynomial rate in M,
contradicting the known logarithmic approximation lower bound.

Here is the transfer of the rate obstruction. For d<=M the function

    f_d(t) = {1/(d*t)} - (1/d)*{1/t}

is constant with value g_d(n) on (1/(n+1),1/n], apart from endpoints, and
vanishes for t>1. It lies in Burnol's space B_(1/M). If D(lambda) is the
distance from 1_(0,1] to B_lambda, then

    D(1/M)^2 <= delta_M^Pareto <= kappa*delta_M^Q.

Burnol's Theorem 1.3 therefore gives
liminf (log M)*delta_M^Q > 0. Under failure of RH the distance already has
a positive limit; under RH the zero sum in that theorem supplies the positive
constant. Fixed dyadic contraction is incompatible with either case.
This literature-to-discrete transfer is a paper argument here; the logarithmic
lower bound has not been formalized by these modules. The original manuscript
does not claim a universal finite-stage sign, so this is a restriction on a
possible continuation, not a refutation of its stated results.

The absolute vanishing-error condition in manuscript (25), and sparse
nonchained subsequence conditions, must be distinguished from such an
impossible uniform contraction schedule.

## Concrete obligations after the 2026-10-18 continuation

- Established: reuse of the existing bounded `QFloorDilation.floorDilation`,
  unrestricted legal invariance, and exact finite cutoff doubling.
- Established: a direct complete-Q dyadic energy identity and the sharper
  squared-norm bound 1/2, needed beyond the old 2/m transfer bound.
- Established: the actual limiting polynomial detector, exact signed head
  identity, finite normalized two-scale estimate, and both loss terms.
- Established: physical first-coordinate formulas for the actual inverse-Gram
  coefficients, and the equivalent finite signed coefficient allowance.
- Formalize the harmonic basis portion separately; it is not required for
  the projection/dilation route.
- Prove the actual scalar lower estimate needed to force ell=0. This is the
  substantive RH-strength open step, not supplied by convergence.
  The new cofinal-subsequence theorem keeps this allowance explicit.
  The limiting quarter lower bound is itself equivalent to zero error.

The existing `ZetaTwoOptimizerStage.lean` uses a squarefree-only dictionary.
It must not be substituted for the all-conductor span in this argument:
floor dilation sends g_d to g_(m*d)-g_m/d and need not preserve squarefreeness.

## Sources

1. The attached manuscript, especially Sections 2--6, for the statements and
   projection/dilation proof strategy.
2. B. Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
   of the Riemann hypothesis*, Proc. Indian Acad. Sci. Math. Sci. 116 (2006),
   137--146, Theorem 1 and its comparable-weight observation:
   https://arxiv.org/html/math/0607733v1 . This supports the mathematical RH
   interpretation; it is not newly formalized by the scalar algebra module.
3. J.-F. Burnol, *A lower bound in an approximation problem involving the zeros
   of the Riemann zeta function*, Theorem 1.3:
   https://arxiv.org/pdf/math/0103058 . This supports the analytic rate
   obstruction. The transfer to the present finite Q spaces is explained above.

No claim of mathematical novelty or proof of RH is made.

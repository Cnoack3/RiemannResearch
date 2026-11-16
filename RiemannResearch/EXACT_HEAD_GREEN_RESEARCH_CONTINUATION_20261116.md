# Exact-head Green profiles: Lean continuation and research agenda
Date: 2026-11-16. Repository: Cnoack3/RiemannResearch.

Source: the attached 17-page *Best Nyman Beurling for RH.pdf*, internally titled
*Exact-Head Green Profiles in the Nyman--Beurling Program*, 27 July 2026.
This is not the longer A1--A2 audited revision from the RH part 2 review.

## Continuation: actual optimizer and a strict quadratic gap

The finite optimizer identification is now proved in Lean. The gcd-atom and
floor upper spans agree for every positive period. Their weighted normal
residuals agree on every nonterminal residue, so their q and profile agree.
First differences recover all proper-divisor coefficients; the period-endpoint
atom is zero on the optimization domain.

The strongest current conditional theorem permits

$
W_x E_x \le k^2 q_x^2+Cq_x,\qquad
m_x\le(1-\delta)q_x+B,\qquad 0\le k<\delta.
$

It gives (delta-k)^2 q <= 2(delta-k)B+2C+2/(x+1), hence a cofinal
uniform bound for the legal exact-head approximants and RH. This is a conditional
research reduction: the actual uniform dispersion and signed-moment bounds
remain open. It does not assume q is bounded while proving that conclusion.

R1 now has external exact-rational certificates at x=5,7,11,13. They use the
repository's complete Pareto tail formulas, outward rational rounding and
Neumann defect checks, not a floating-point accuracy assumption. The individual
endpoint computations have not yet been replayed in Lean. Source and precise
bounds are retained next to the earlier numerical records. No finite set of
certificates proves the cofinal analytic hypotheses.

## Earlier relative-dispersion target (the k=0 case)

The paper asks for E_aff=o(1/log x) and a signed affine moment tending to zero.
The first Lean reduction instead suffices with constants delta>0,
C>=0 and B such that, on a cofinal sequence of actual primorial stages,

$
W_x E_x \le Cq_x,\qquad m_x\le (1-\delta)q_x+B.
$

The simpler bounded-moment condition m_x<=B is the special case delta=1.
The relative-rate improvement is from the paper's preferred E_x=O(q_x/x)
to E_x=O(q_x/W_x). The absolute o(1/log x) formulation is a separate route;
it alone does not assert a bound on W_x E_x/q_x.

Here W_x=sum_{1<=d<=x} mu(d)^2/d, E_x is the weighted squared profile error,
and m_x=sum mu(d) h_x(d)/d. The profile need not be affine.
The signed moment may grow with the residual energy; it must retain a fixed
proportional deficit below q_x, up to an additive constant. No coefficient
compactness, PNT, asymptotic nonsingularity, or prior bound on q_x is assumed.

The exact signed root r=q+tau and the profile Cauchy estimate give

$
\tau^2\le aq,\qquad (r-m)^2\le Cq,\qquad
\delta^2q\le 2\delta B+2C+2a.
$

For delta=1 this gives q<=2B+2C+2a.

For the actual periodized Pareto weights and the exact head, a=1/(x+1).
The full norm is terminal+q; terminal<=1. Thus the actual legal Hilbert
approximants have uniformly bounded norms along cofinal heads. The repository's
bounded-exact-head closure theorem then gives RH.

This is a **conditional RH theorem**, not an unconditional RH proof.
No actual uniform provider for the two displayed analytic bounds is obtained.

## Concrete finite data and a supplied primorial family

`Pareto.MobiusHeadGreen.riemannHypothesis_of_cofinal_mobius_profile_deficit`
allows arbitrary periods and takes:

- periods P_x>x;
- real coefficients c_x(d), d in {1,...,P_x};
- c_x(d)=mu(d) when 1<=d<=x;
- every nonzero coefficient has d dividing P_x;
- upper normal equations at active coefficients:
  score_x(d)=0 when d>x and c_x(d) is nonzero;
- the two cofinal analytic bounds above.

The legal seed span here is the full positive-index span, `Set.Ici 1`.
It constructs the legal NB residue extension

$
f_x(n)=P_x\left(\sum_d\frac{c_x(d)}d\right)\left\{\frac n{P_x}\right\}
-\sum_d c_x(d)\left\{\frac nd\right\}.
$

proves f_x(n)=sum_d c_x(d) floor(n/d) below P_x, proves f_x=1 on
1<=n<=x, proves the signed root, tail-charge bound and full terminal split,
and then concludes RH.

The additional `MobiusHeadGreenNormal.lean` module constructs the finite
normal coefficients from actual weighted least squares, including dependent
columns and zero weights. All upper divisor normal equations are obtained;
no inverse-Gram premise or numerical oracle is used.

It supplies `greenPeriod x = primorial (x+1)`, proves x<greenPeriod x and
the squarefree coverage, and constructs `primorialNormalCoefficients x`.
The theorem `riemannHypothesis_of_primorial_profile_deficit` therefore has
only the two cofinal analytic estimates as its remaining mathematical inputs.
The harmless shifted cutoff guarantees a period larger than every integer
head; at the odd-prime cutoffs in the numerical table it is the same primorial.

The gcd-atom fit is now formally identified with this floor-normal construction.
`ExactHeadAtomOptimizer.floor_residual_eq_atomResidual` proves the residual
identity. Its primorial q and profile specializations identify the exact data
appearing in the conditional RH criterion.

## Low-conductor budget without circular boundedness

The formalized actual-weight estimate is

$
E_{\mathrm{low}}(D)\le\frac{q_xD(D+1)}{8(x+1)}.
$

Its sharper version retains both the actual support mass and the exact
squarefree sum. It holds for arbitrary D, not just D<=x.

For the weaker relative criterion, it suffices to choose D so that

$
W_xD(D+1)\le 8C_{\mathrm{low}}(x+1).
$

Then W_x E_low(D)<=C_low q_x. A moving cutoff on the scale
sqrt(x/W_x), heuristically sqrt(x/log x), is therefore admissible for this
relative budget. This statement does not use a bounded-q assumption; such an
assumption for legal exact heads would already imply RH.

The unresolved task is the complementary moving-conductor energy, combined
with the one-sided signed moment. Applying an all-directions operator bound
does not exploit the source's special optimizer direction.

## Primitive arithmetic and exact affine elimination

The existing integrated Ramanujan packet J_a is used directly. For every
positive d, including nonsquarefree d,

$
\widetilde\rho_d(r)=\sum_{\substack{a\mid d\\a>1}}
\left(J_a(r)-\frac{\varphi(a)}2\right).
$

Pairing against arbitrary finite weights gives the exact primitive score sum.
The canonical affine energy equals its complete divisor square function.
No orthogonality with respect to the Pareto weights is inferred from this
arithmetic centering.

Digit recursion is proved for every natural multiplier p, without primality:

$
G_d=pG_{pd}+D_{p,d}.
$

The boundary score identity uses the exact equation score(pd)=0.
The affine least-squares completion retains all mixed terms.
Adding an affine function to the data only shifts the fitted coefficients;
it does not change the loss. Identifying the actual boundary carry component
with this affine subspace is a remaining arithmetic assembly step.

The actual squarefree-weighted affine minimizer exists uniquely for every
integer x>=2. Exact Cramer equations and a single signed numerator reduce
the signed moment test to finite algebra.

`affine_signed_moment_abs_le` also proves the elementary bound
|m_x|<=|c0|+|c1| by using the repository's uniform reciprocal-Mobius bound.
Thus bounded fitted coefficients suffice for the new criterion without any
PNT input. These finite identities do not give a uniform coefficient bound
for the actual fit by themselves.

## Numerical extension and falsification check

All values below are **external floating-point diagnostics**, not interval
certificates and not Lean computations. The periodized infinite weights are
evaluated using digamma; the entire nonterminal period is included.

| x | q | E_aff | E_G | x E_aff/q | W E_aff/q | signed fitted moment |
|---|---:|---:|---:|---:|---:|---:|
| 17 | 0.01884149241 | 0.00031795900 | 0.00039607721 | 0.286883 | 0.0473797 | 0.00650047 |
| 19 | 0.01332260069 | 0.00010053218 | 0.00022548382 | 0.143374 | 0.0215833 | 0.00180603 |
| 23 | 0.01118024946 | 0.00007166859 | 0.00013678013 | 0.147437 | 0.0192103 | 0.000782666 |

The x=19 fitted coefficients are approximately (0.00753904,-0.0138597).
At x=23 they are approximately (0.00990838,-0.00912833).
No sharp growth of x E_aff/q or the coefficients was observed through 23.
This is a finite falsification check, not evidence establishing a universal
constant or an asymptotic rate. For the strengthened moment criterion, the
measured relative deficits 1-m/q are approximately 0.6550, 0.8644, and 0.9300
at x=17,19,23 respectively. No uniform positive margin is certified.

Independent dense/chunked and event accumulations were compared through 19.
Double and extended-precision event accumulations were compared through 23.
The extended run improves the x=23 signed-root residual from roughly 5.6e-8
to 3.9e-10. The scaled Gram condition number is about 2.49e10; SciPy's weights
and linear solve still use floating point. Agreement does not constitute an
outward-rounded error enclosure.

### Canonical dyadic ledger

| conductor block | E_G block at x=19 | E_G block at x=23 |
|---|---:|---:|
| (1,2] | 8.10509e-6 | 4.87369e-6 |
| (2,4] | 8.62410e-6 | 8.93320e-6 |
| (4,8] | 2.29988e-5 | 1.63074e-5 |
| (8,16] | 9.03356e-5 | 3.98517e-5 |
| (16,x] | 9.54202e-5 | 6.68142e-5 |

The canonical d=1 term is exactly zero. Best-affine d=1 need not vanish;
the retained JSON ledger includes that singleton explicitly. In retained runs
its entry was reconstructed from the full energy minus the d>1 blocks.
Current reproduction sources accumulate it directly. Energy totals and fits
were not changed.

The final block accounts for about 42% of E_G at 19 and 49% at 23.
This supports retaining a separate moving-conductor ledger, but does not
identify an asymptotic transition scale.

## Agenda status and concrete next checks

| Item | Status | Delivered | Remaining acceptance criterion |
|---|---|---|---|
| R1 certified data | Partial: external rational certificates | Complete weight and solve enclosures at 5,7,11,13; diagnostics through 23 | Replay endpoint checks in Lean; certify larger stages |
| R2 dyadic ledger | Computed, external | Canonical and best-affine block energies through 23 | Certified block intervals and larger cutoffs if justified |
| R3 digit/carry formulas | Partial, Lean checked | General digit recursion, primitive arithmetic bridge, affine completion/shift | Identify the actual boundary carry/discrepancy with the affine component |
| R4 signal-specific discrepancy | Open | Actual tail mass, low-conductor bound, strict quadratic gap criterion | Jointly cofinal W E<=k^2 q^2+Cq with k<delta, without assuming bounded q or RH |
| R5 moment admissibility | Partial, Lean checked | Unique fit at all x>=2, exact Cramer moment numerator | Fixed proportional moment deficit m<=(1-delta)q+B; bounded m is sufficient |
| R6 falsification | Extended, external | No blow-up observed through 23 | Further certified stages; no finite test is an asymptotic proof |

Priority order for continuation:
1. Replay the retained rational certificates inside Lean. The external
   complete-weight and normal-solve enclosures at 5,7,11,13 are available;
   larger cutoffs still need outward-rounded event accumulation with every
   simultaneous jump term retained.
2. The atom/floor identification is completed. Use the checked common
   residual and the proper-divisor first-difference formula in certificate assembly.
3. Form the exact signed normal numerator at each cutoff and pursue the
   proportional deficit or a uniform upper bound directly. Bounded coefficients
   are a sufficient stronger route and need no PNT in this reduction.
4. Prove the actual boundary carry/discrepancy decomposition, remove the affine
   component algebraically, and target the weaker W E_tail<=Cq budget.
5. Keep any claimed uniform bound separate from finite diagnostics; check that
   no target-closure or bounded-exact-head premise has been inserted.

## Files and evidence

See [verification and the guarded axiom audit](EXACT_HEAD_GREEN_VERIFICATION_20261116.md).
See [the theorem catalog](THEOREM_CATALOG_EXACT_HEAD_GREEN_20261116.md) for
declarations and focused verification jobs. See
[reproduction sources](ResearchData/ExactHeadGreen20261116/reproduction_sources.md)
and the adjacent JSON files for complete numerical records.

Full publication is gated by the managed Bazel/BuildBuddy
`//:RiemannResearch` checkpoint. Focused snippet success alone is not
a full-project checkpoint. No new axioms, sorry, or admitted proofs are used.

# Moving projected-dual quantitative audit — 28 September 2026

Follow-up: `ProjectedDualColumnConcentrationAudit20260928.md` records
the subsequent l2 concentration criteria and accumulated Schur bounds.
Their sub-stretched quantitative providers remain Open.

Continuation of Cnoack3/RiemannResearch commit
37b70ace875015abc52da4a504e9b2b9232702b0.

## Conclusion

The inspected projection, orthonormal-coordinate, inverse-Gram, and Schur
results do not supply the required moving physical-tail rate. This
continuation proves quantitative bounds and conditional bridges; it does
not prove a rate provider, vanishing residual, or RH unconditionally.

The reusable results are in RH/ProjectedDualStretchedTail.lean. All energies
and pairings use the complete infinite Pareto Hilbert space.

## Notation and exact estimates

Let P_n be projection onto g_2,...,g_(n+1), let h_d be coefficientRiesz d,
and put

- e_n = tailError n = 1 - canonicalMobiusHilbert n;
- E_(n,d) = ||tailShift_n(P_n h_d)||^2;
- Phi(n) = ((6+log n) log(6+log n))^(1/11);
- w_a(n) = n exp(-a Phi(n));
- delta_(n,d) = correction n d;
- L_d = mobiusDifferenceCLM d limitResidual.

The checked arithmetic provider gives some a>0 and C>=0 such that,
eventually, ||e_n||^2 <= 8+C w_a(n). The existing exact pairing gives,
for 1<d<=n,

    delta_(n,d)^2 <= ||e_n||^2 E_(n,d)
                   <= 8 E_(n,d) + C w_a(n) E_(n,d).

Unconditionally E_(n,d)->0 and delta_(n,d)->L_d. Their convergence has
no supplied quantitative rate.

## New verified quantitative statements

1. Exact physical-head cancellation:
   for i:Fin n, d=i+2,

       E_(n,d) = (G_n^-1)_(i,i) - sum_(k<n) |(P_n h_d)(k)|^2.

   Here k indexes weighted l2 coordinates, not unweighted physical values.
   This is projectedDualTailEnergy_eq_inverse_diagonal_sub_head.

2. Exact orthonormal representation:

       (G_n^-1)_(i,i) = sum_(j<n) modeCoefficient(d,j)^2.

   This is inverse_diagonal_eq_modeCoefficient_sq_sum. Summability of
   these mode coordinates and boundedness of the diagonal do not provide
   a rate for cancellation against the physical head in item 1.

3. Complete physical-tail estimate. Let

       B_(n,d) = sum_(i<n) |coefficientCLM(i+2)(P_n h_d)|.

   Then

       E_(n,d) <= B_(n,d)^2 / (n+1).

   For d=i+2 present at stage n, B_(n,d) is exactly the l1 norm of the
   i-th inverse-Gram column (also the corresponding row by symmetry).
   The proof uses the uniform complete atom-tail bound 1/(n+1), linearity,
   and the triangle inequality. No coefficient bound is assumed.

   The formal declarations are projectedDualTailEnergy_le_coefficient_mass,
   projectedDualCoefficientMass_eq_inverse_column, and
   stretched_projectedDualTailEnergy_le_coefficient_mass.

   Combining this with the arithmetic provider gives, eventually and
   simultaneously for 1<d<=n,

       delta_(n,d)^2 <= [8/(n+1)+C exp(-a Phi(n))] B_(n,d)^2.

   This is correction_eventual_stretched_coefficient_mass_bound. The
   inverse-column mass remains explicit in this unconditional inequality.

4. Nonzero-limit obstruction. If L_d != 0, then for every b<a,

       w_b(n) E_(n,d) -> +infinity.

   Indeed delta_(n,d)^2 is eventually bounded below by L_d^2/2, while

       delta_(n,d)^2 <= 8 E_(n,d)
         + C exp(-(a-b)Phi(n)) [w_b(n) E_(n,d)].

   Both the first term and the coefficient multiplying the bracket tend
   to zero. A bounded cofinal bracket is impossible. This is
   projectedDualTail_stretched_barrier_of_nonzero_correction; the
   unconditional arithmetic-provider assembly is
   exists_projectedDual_stretched_barrier.

## Smallest quantitative projection target isolated here

At the original provider exponent it suffices that, for every fixed d>1,

    for every epsilon>0, cofinally w_a(n) E_(n,d) < epsilon.

This is a liminf-zero requirement on a nonnegative sequence, weaker than
full convergence to zero. The cofinal indices need not be shared by
different d. It forces L_d=0 by the complete product bound and E_(n,d)->0.

With any strict exponent margin b<a it is enough that, for every fixed d>1,

    cofinally w_b(n) E_(n,d) <= K_d

for some finite K_d. For positive n this is exactly a cofinal
E_(n,d) <= K_d exp(b Phi(n))/n bound. The existing o(1) tail result
does not supply this bound.

A more concrete but stronger sufficient inverse-Gram estimate is

    cofinally exp(-b Phi(n)) B_(n,d)^2 <= K_d,  b<a,

equivalently cofinal l1 column growth O_d(exp(b Phi(n)/2)).
This follows from item 3 and is formalized as
limitResidual_eq_zero_of_cofinal_stretched_coefficient_mass.
The coefficient-mass bound itself remains Open. In particular no
n-independent column l1 bound is asserted.

## Connection to the cumulative signed gains

exists_projectedDual_stretched_shell_bridge instantiates the checked
arithmetic exponent. Either of the two physical-tail providers above
forces all L_d to vanish. The previously checked coefficient-limit
criterion then forces limitResidual=0.

Using residual_weighted_dyadic_telescope in ParetoDyadicShellCriterion.lean,
the bridge concludes, for every real weight w and every N,K,

    sum_(j<K) residualWeightedShellGain w (2^j N) = 0.

This is a conditional implication through zero residual, not a new
unconditional estimate for nonzero-residual shell gains. It retains
all signed terms and does not discard a local pairing by global
orthogonality. The existing forward bridge to RH is available, but
the quantitative projection provider has not been discharged.

## Audit of existing candidate providers

- ResidueProjectionCorrectionTail.lean: the moving-tail convergence proof
  bounds the tail by twice the projection-convergence error squared plus
  twice the physical tail of the fixed limiting projection. Both terms
  tend to zero, but neither has a supplied rate.
- ParetoInverseGramDual.lean and CanonicalMobiusStretchedCorrection.lean:
  fixed inverse entries converge and fixed diagonal entries are bounded.
  They control full projected-dual energy; the new exact head subtraction
  identifies the additional cancellation required.
- ResidueOrthonormalCoordinates.lean: squared coefficient modes are
  summable, and fixed coefficient series converge absolutely. These
  statements identify limits but supply neither the required physical-tail
  rate nor the missing Möbius target equality.
- ResidueProjectionSchur.lean: exact Schur updates identify finite gains,
  positive Schur complements, and coefficient increments. They do not
  bound the accumulated inverse-column mass or the complete moving tail.
- ParetoDyadicShellCriterion.lean: telescoping and the signed-gain
  criterion are exact. Their arithmetic upper-control provider remains
  open.

No external analytic theorem was imported. No sorry, admit, project-local
axiom, or unsafe declaration is part of this continuation.

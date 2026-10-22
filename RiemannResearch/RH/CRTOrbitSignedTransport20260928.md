# CRT orbit continuation: signed sparse transport
Date: 2026-09-28
Source snapshot: f585c5d69ddc5c9b494259861596d339e9b70d11

## Conclusion

This continuation does not prove RH. It strengthens the existing orbit argument
by showing that its actual finite optimization energy agrees with the original
Pareto projection energy to o(1/(2^k+1)), unconditionally. It also isolates an exact
one-sided scalar criterion sufficient for RH. That scalar sign assertion remains Open.

Source: the user-provided
RH_CRT_Orbit_Exhaustion_and_Doubling_Invariance_2026-09-20(1).md,
especially Sections 8--9 (orbit construction and proof strategy).
Bagchi, "On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
of the Riemann hypothesis", Theorem 1,
https://arxiv.org/abs/math/0607733, supports the classical weighted-space
equivalence. This development does not assume that equivalence as an axiom
or introduce a new RH-to-density provider.

## Audit of existing coverage

The source snapshot already contains:

- ArgumentDoublingClosure.lean: the actual implication from doubling invariance
  to constant membership and then Mathlib RiemannHypothesis.
- ArgumentDoublingGenerators.lean: the bounded sampling operator, its exact
  operator norm 2, generator/carry identities, and the finite-span obstruction.
- DyadicCarryBlocks.lean: norm convergence of the reversed sampled residues and
  the closed-span carry-gap limit.
- DyadicCarryCRT.lean: exact modular reversal on every coordinate and full
  infinite-energy CRT certificates.
- DyadicCarryQuantitative.lean: the sparse multiple indicator and its bound
  ||b_k||^2 <= 2/(2^k+1)^2.
- DyadicCarryOptimizationLimit.lean: an explicit finite inverse-Gram optimization
  schedule and convergence of its energy to the original unknown defect.

Thus neither the doubling implication nor the O(1/d) distance transport is a
new result of this continuation. The new module is DyadicCarrySignedTransport.lean.
This continuation makes no new assertion of infinite-DPP existence, and does not
use a probabilistic exhaustion statement to exchange quantifiers.

## Definitions and exact finite identity

Work in H with ||f||^2 = sum_{n>=1} |f(n)|^2/[n(n+1)].
Let g_d(n) = (n mod d)/d and S be their closed real span.
Set d_k = 2^k+1 and V_k = span(g_2,...,g_{d_k}).
Let P_k and P be the orthogonal projections onto V_k and S.

Write

    h_k(n) = g_{d_k}(2^k n),
    b_k(n) = 1_{d_k divides n},
    e_k = 1 - P_k 1,
    r = 1 - P 1,
    D = ||r||^2,
    s_k = (I-P_k)b_k.

The repository anchors physical coordinate 0 at zero; the displayed sequences
are for positive n. Modular reversal gives

    h_k + g_{d_k} = 1 - b_k.

Since g_{d_k} belongs to V_k,

    (I-P_k)h_k = e_k - s_k.

The whole carry block is B_k = 2^k g_{d_k} - h_k.
Its actual finite optimal error, represented by
dyadicRepairEnergy k 0 (2^k), is

    E_k = ||(I-P_k)B_k||^2 = ||e_k-s_k||^2.

Orthogonality removes the projection from the covariance:

    <e_k,s_k> = <e_k,b_k>.

Consequently the new checked signed identity is

    E_k = ||e_k||^2 - 2<e_k,b_k> + ||s_k||^2.

No absolute coefficient mass, diagonal-only Gram approximation, or truncated
energy has been substituted.

## New unconditional cancellation estimate

Let T_N discard the first N weighted l2 coordinates, so it keeps physical
indices n>N. Since b_k vanishes at n<d_k, Cauchy--Schwarz gives, for every f in H,

    |d_k <f,b_k>|^2
      <= d_k^2 ||T_{d_k-1}f||^2 ||b_k||^2
      <= 2 ||T_{d_k-1}f||^2.                         (1)

The full tail norm tends to zero for every fixed f. Therefore

    d_k <f,b_k> -> 0.                                (2)

This also holds for every norm-convergent moving family f_k -> f:
apply (2) to f and bound the remaining pairing by
|d_k <f_k-f,b_k>| <= sqrt(2)||f_k-f||.
This is the checked theorem
dyadicMultipleIndicator_scaled_moving_pairing_tendsto_zero.

The finite residuals e_k converge in norm to r unconditionally by increasing
orthogonal projection. Apply the moving theorem to e_k. Also,

    0 <= d_k ||s_k||^2 <= 2/d_k -> 0.

The exact finite energy identity now proves

    d_k (E_k - ||e_k||^2) -> 0,

or equivalently

    E_k = energy(2^k) + o(1/(2^k+1)).                 (3)

The Lean declaration is
dyadicRepairEnergy_zero_head_scaled_difference_tendsto_zero.
This refines the previous O(1/d_k) comparison of square-root energies.
It supplies no rate for energy(2^k) -> D and does not prove D=0.

## Exact remaining scalar condition

Because r is orthogonal to every legal generator,

    <r,h_k> = D - <r,b_k>,

and the same sparse cancellation proves

    d_k (<r,h_k>-D) -> 0.                            (4)

The following is kernel-checked:

    [for every K there exists k>=K with <r,h_k> <= 0]
       iff 1 belongs to S.

For the forward direction, <r,h_k> -> D. If D>0, all sufficiently late
observations are positive, contradicting the cofinal sign condition.
Therefore D=0. Conversely, 1 in S gives r=0 and every observation vanishes.

The module then uses the repository's existing checked density-to-RH
implication to conclude Mathlib RiemannHypothesis from this cofinal sign
hypothesis. No RH-to-density theorem is silently imported.

Open arithmetic obligation:

    prove <r,h_k> <= 0 for arbitrarily large k,

or otherwise prove the equivalent constant-membership/vanishing-defect
condition. Equations (1)--(4) do not establish that sign. In particular,
D>0 is consistent with every unconditional estimate above: the observations
then converge to a positive value, and both finite energies converge to D.

Finite CRT exhaustion and orbit cardinalities do not impose the missing sign
on the actual signed projection residual. This is why the continuation is
an unconditional refinement plus a conditional RH reduction, not an RH proof.

## Verification scope

The principal new energy and scalar-criterion declarations were checked with
#print axioms; their dependency lists contain only propext, Classical.choice,
and Quot.sound. The final repository checkpoint validates the persisted module
and its affected dependents. No sorry, admit, project-local axiom, or unsafe
declaration is introduced.

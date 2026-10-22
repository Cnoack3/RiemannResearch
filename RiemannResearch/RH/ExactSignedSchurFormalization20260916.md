# Exact signed Schur remainder: Lean coverage

Source: `RH_Exact_Signed_Schur_Remainder_2026-09-16.tex`.
SHA-256: `2e67110306b9bb0a0dc7fe3bd54b8057d2e683a6bf6f70f1f15e58281e1a3ce5`.

This continuation formalizes the fixed-head Schur core in the actual Pareto
Hilbert space. It does not claim that all analytic estimates in the manuscript
have been formalized, or that RH has been proved.

## Established results

| Module | Coverage |
| --- | --- |
| `RH/ParetoPointClosure.lean` | The actual point vector at physical index one is (1-D_2/2) applied to the constant target. The dyadic half operator is contractive. Point-target membership in every closed legal space is equivalent to constant-target membership. The point target cannot be a finite legal packet, by periodicity. |
| `LinearAlgebra/FiniteHilbertSchur.lean` | Complete signed normal equations, exact residual energy, completion of the square, inverse-Gram block gain, and the full Gram correction under old-space orthogonal projection. |
| `RH/ParetoSignedSchurRemainder.lean` | Actual remainder `fixedHeadRemainder F = norm(F - delta_1)^2`; strict positivity for every finite legal packet; energy minus one half for first coordinate one; legality and head preservation of finite Schur residuals; the binary seed has energy `Real.log 2`, giving exactly `log 2 - 1/2 - sum c_i inner(z_i, seed)`. The inverse coefficients are supplied by the full Gram equivalence in `FiniteHilbertSchur`. |
| `RH/ParetoSignedSchurRemainder.lean` | Exact projection residual onto the line through a unit-head packet: `R / (1 + 2*R)`. The coefficient-minimization completion identity holds in the actual Pareto norm. |
| `RH/ParetoSignedSchurRemainder.lean` | Relative gains are defined from actual remainders. For positive decreasing remainders, convergence to zero is equivalent to nonsummability of those gains. Legal packets with nonsummable gains imply Mathlib's `RiemannHypothesis` through the proved point-closure and Mellin bridge. Positivity is discharged automatically for legal packets in the RH consumers. |
| `Analysis/ResidualHarmonicGain.lean` | A harmonic lower bound gives the explicit finite bound `d_n <= d_0 * exp(-c*H_n)` and nonsummability. The actual Pareto consumer proves RH conditional on that lower bound and decreasing remainders. The general exact product criterion is reused from `ResidualGainProduct`. |
| `LinearAlgebra/OrthogonalFarSupportBound.lean` | Orthogonal-component Pythagoras, old-space capture from exact support pairings, lower bound for the residualized Gram quadratic form, and signed directional gain bound with factor `1/(1-tau)`. |
| `LinearAlgebra/SchurSubspaceGain.lean` | The whole correction subspace is residualized using the actual old-space projection. Its complete optimized gain is at most `norm(z)^2/(1-tau)`, under explicit tail-capture and support-pairing hypotheses, with no bound on block size. |

Key conditional RH theorem:

`RiemannResearch.RH.Pareto.riemannHypothesis_of_harmonic_fixedHead_gains`

Its substantive premises are legal packets, decreasing actual remainders,
a positive constant (c), and actual relative gains at least (c/(n+1)).
The gain lower bound is not asserted by this development.

## Exact scope of the finite algebra

The Schur formulas quantify over actual finite control families and their
normal equations. `finiteSchurResidual_inverse_gain` uses a linear equivalence
whose action is explicitly the full signed Gram matrix, so it does not replace
the Schur complement with a diagonal or unsigned bound.

This addition does not identify the manuscript's one-edge-per-integer dictionary
with the repository's existing ordinary-budget canonical family. They are
different finite families. Instantiating all formulas with the manuscript's
precise (h_m), (K_L), and (R_L), including the finite spanning proof, remains
a separate provider task. The line-projection distance formula has been checked;
its identification with distance to the manuscript's entire (V_L) is not
claimed here.

## Remaining manuscript obligations

- The rational-frequency Fejer localization estimate and its concrete uniform
  (O(L^2/M)) tail-capture constants.
- The periodic dilation-adjoint averaging estimate, fixed-template expansion,
  and uniform growing-template (O(M^{-3})) mean-zero gain bound.
- The explicit point-target zero-dependent floor, beyond the already proved
  constant-target Mellin obstruction and the new point-target RH implication.
- The manuscript dictionary's finite-budget instantiation and the full-space
  projection-distance identification.
- Most importantly, a sufficient lower bound or nonsummability theorem for the
  actual comparable-budget Schur gains.

No converse from RH to two-seed density is imported as an axiom. The inherited
project proves the approximation-to-RH direction. The converse stated as an
imported input in the manuscript is not promoted to a new Lean theorem here.

## Verification policy

The added proof groups are checked with Lean, followed by the workspace
checkpoint's affected-module validation. Representative axiom audits report
only `propext`, `Classical.choice`, and `Quot.sound`. There are no added
project-local axioms, `sorry`, or `admit` declarations.

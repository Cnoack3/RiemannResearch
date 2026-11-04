# Literal squarefree residue Hilbert basis — 4 November 2026

Source: the user's request for a basis of the closed legal squarefree span.
The construction uses Mathlib Gram–Schmidt and HilbertBasis, following the
project's QSquarefreeCompleteBasis proof pattern with a different dictionary.

## Space and distinction

Write A for the real algebraic span of g_d(n)=(n mod d)/d over squarefree d>=2,
and V for its closure in Q(n)=1/(zeta(2)n^2).

QSquarefreeResidueBasis uses exactly ZetaTwoOptimizerStage.squarefreeAtom.
It does not adjoin qOne. QSquarefreeCompleteBasis instead constructs a basis
of PrimePowerTarget.closureWithConstants; that existing result does not by
itself give a basis of V.

## Construction

Enumerate squarefree conductors 2,3,5,6,7,10,... and orthonormalize their
residue atoms in the complete Q inner product. Each new vector is a finite
legal combination. Finite independence follows from the existing
QCovarianceInvertibility.qResidue_linearIndependent theorem.

The Lean dictionary includes zeros at nonsquarefree conductors and retains
only nonzero Gram–Schmidt innovations. This avoids an independence assumption
in the Hilbert-basis construction itself. It gives the same ordered vectors
after the zero entries are omitted.

The first vector is e_1=4*g_2/sqrt(3). Its constant coefficient is sqrt(3)/2,
so its constant-energy contribution is 3/4. These explicit first-vector
evaluations are ordinary calculations, not new declarations in this module.

## Principal declarations

Namespace: RiemannResearch.RH.QSquarefreeResidueBasis.

- residueVector_orthonormal: actual Q orthonormality.
- residueVector_span and residueVector_closed_span: exact algebraic and
  closed-span preservation.
- residueHilbertBasis: a HilbertBasis of the literal squarefree closure.
- residueProjection_hasSum: unconditional norm-convergent projection series.
- residueProjection_parseval: coefficient energy equals projection energy.
- residueBasis_energy_exact: full energy equals coefficient energy plus
  the entire squared orthogonal residual.
- residueBasis_error_exact: every signed coefficient discrepancy and the
  entire orthogonal residual are retained.
- mem_closure_iff_parseval: membership is exactly Parseval saturation.
- qOne_mem_closure_iff_parseval: the constant belongs to V exactly when
  its complete coefficient-square sum equals 1.

For arbitrary x in QHilbert and f in V, the exact identity is

    ||x-f||_Q^2
      = sum_i (<x,e_i>_Q - <f,e_i>_Q)^2 + ||x-P_V x||_Q^2.

The basis is unconditional. Constant membership, the saturation equality
for qOne, and RH are not concluded.

## Verification and publication

The initial isolated candidate passed job
job_VdXto4SW8ZPldM6GWXd6RIO80XWU_GbJ: verified=true, exit_code=0.
The server reported 61.478 seconds for that run, including its reported
build/check work. Workspace opening took 107.923 seconds separately;
status polling experienced transport timeouts and is not Lean check time.

Axiom inspection of the basis, orthonormality, closed-span identity,
projection series, full energy identity and constant saturation criterion
reported only propext, Classical.choice and Quot.sound.

The final saved module passed job
job_myMBSASniG_nDicDLQC96fA5BsX68UCT: verified=true, exit_code=0.
The server reported 16.374 seconds for the verification run and a 4.8-second
build of QSquarefreeResidueBasis. The new module built without warnings;
unchanged dependency linter warnings were replayed. All six inspected
declarations again reported only the three standard foundational axioms.

The user approved publication of this module, its aggregate import, and this
catalog entry on 4 November 2026. Final publication is gated by the server
checkpoint's source audit and required Lean validation. Its result records
the validation scope and the exact publishing commit.

No new RH hypothesis, local axiom, unfinished proof, or unsafe declaration
is introduced.

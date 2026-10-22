# Concrete Cesaro finite Gram reconciliation (2026-09-18)

## Historical record and present scope

The source files Conditional_IID_Lean_Verification_Status_2026-09-17.md and
Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md record different
kinds of evidence: a verification/publication snapshot and an ordinary
mathematical argument. A mathematical proof in the latter does not establish
that a Lean declaration was checked or published in the former. The original
no-new-check/no-publication statement is not retroactively changed.

This continuation preserves the previously prepared signed-completion modules
alongside current-main finite arithmetic minimization. Publication and project
verification are established only by a successful checkpoint, not this note.
The earlier commit 670345e39129dd4805968f8f08f3bca8c7b5e1ea is retained in its
original workspace; this reconciliation does not discard or rewrite it.

## Signed-completion formalization

- Analysis/FiniteSignedQuadratic.lean: finite signed quadratic expansion,
  transpose pairing, conjugated quadratic, and inverse-based Schur completion.
- RH/ConditionalMeanGram.lean: actual normalized residue means with conductors
  2,...,D+1; head, full Gram and infinite tail Gram matrices; convergence of
  every Gram entry; exact head/tail split; symmetry; the actual tail quadratic
  as an infinite weighted sum of squares and its nonnegativity.
- Concrete S=N^T T N and h=N^T T c0; exact signed expansion, square completion,
  minimization, and an attained constrained minimum.

constrained_tail_isLeast EXPLICITLY takes a feasible c0, a full kernel
parametrization N, and a right inverse B of S. It does not prove those premises.
The series identity and nonnegativity require none of these finite-algebra
premises.

UniformFiniteTailTarget and UniformSignedSchurTarget are propositions, not
proved bounds. finiteTailTarget_of_signedSchurTarget proves only the implication.
The Schur target explicitly includes feasibility, an injective full-kernel
parametrization, and both inverse identities, including the zero-dimensional
correction case. All signed cross terms are retained.

Index convention in ConditionalMeanGram: D is the NUMBER of columns; the
largest conductor is D+1. Thus the source's conductor budget >= Y+1 becomes
Y <= D here. Infinite sums use positive endpoints.

## Results already supplied by concurrent main

The previous version of this note listed rank, strict tail positivity and
inverse formulas as remaining work. That description is no longer accurate
for the repository as a whole:

| Existing module | Concrete result |
|---|---|
| RH/ConditionalFiniteMatrixMinimum.lean | G_posDef, T_posDef, A_surjective for N+1 <= D; actual fullValue/tailValue minima and inverse formulas; fullValue_eq_head_add_tailValue. |
| RH/ConditionalNormalizedMatrixMinimum.lean | normalizedTailMatrix_posDef and normalizedGramMatrix_posDef; literal normalized inverse formulas for the attained full and tail minima. |

These modules use conductors indexed by Finset.Icc 2 D, not Fin D. Their
positivity and rank premises are discharged by actual residue theorems.
They are preserved unchanged. Do not repeat their proofs or classify those
finite facts as unresolved mathematics.

## Small remaining integration obligations

1. To remove the exposed premises from the Fin D signed-completion API, prove
   the coefficient/matrix transport along d -> d+2 from Fin D to
   Finset.Icc 2 (D+1), reuse the existing rank and positivity providers, and
   construct a basis of ker(headMatrix). Its injective synthesis gives a
   positive-definite correction Gram and hence the required inverse. This is
   finite-dimensional integration, not a new arithmetic bound.

## Equation (11.5): formalization completed

RH/ConditionalConductorExhaustion.lean now supplies the previously missing
conductor-exhaustion step, with no RH or uniform-bound premise:

- legal_mem_finiteResidueSubspace proves finite support for the actual legal
  span, including its dilation generators.
- fullValue_antitone proves decrease under conductor enlargement.
- conditionalHeadMinimum_eq_iInf_fullValue proves equality with the infimum
  indexed by all natural D satisfying N+1 <= D.
- tendsto_fullValue_conditionalHeadMinimum proves convergence along the full
  sequence D=N+1+k, not merely an unspecified subsequence.

The finite minima are the existing fullValue, already identified with the
literal normalized inverse-Gram expression. Development verification passed;
both principal declarations' axiom audits contain only propext,
Classical.choice and Quot.sound. The publication checkpoint verifies the saved
module. No conductor rate or uniform-in-N energy estimate follows from (11.5).

Closing (11.5) is not a certification that all other mathematics in the
completion has been formalized; the coordinate/kernel-basis task above remains.
ConditionalMeanFormalization20260917.md and
ConditionalMeanCoverageAudit.md are historical audits; some of their gaps
have since been addressed by new main modules. Their old gap lists must not
be read as a fresh exhaustive audit.

## Exact mathematical frontier

Assertion (11.7), a uniform bound on the actual signed constrained energies,
or a sufficient cofinal subpolynomial replacement, remains OPEN. Invertibility,
attainment, an exact inverse formula, and an implication from a bound do not
supply that bound. No unconditional RH proof, domain-specific axiom, or proof
placeholder is introduced.

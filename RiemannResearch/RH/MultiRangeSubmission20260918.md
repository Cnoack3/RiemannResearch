# Multi-range divisor corrections: Lean submission

Source: `RH_Multi_Range_Divisor_Corrections_2026-09-18.md`, preserved alongside this report.
**No new Lean theorem was successfully verified in this submission.**
The final two proof checks returned `wall_timeout`, exit code `-9`, with no diagnostics, at 180 and 300 seconds. The research note and this status report are being submitted as documentation only. Candidate `.lean` files are saved separately in the recovery package and are not added to the verified module exports.

This submission starts from repository commit `e4d1826cdb73a1aca41707aa64fd220d92298903`.
The final checkpoint, not acceptance into the queue, determines publication status.

## Unverified formalization candidates

- `MultiRangeDivisorCorrections.lean`: exact balanced anchor directions, equality with cancelling floors, legality and zero initial values, finite range synthesis, the solved anchor coefficient, disjoint range assembly, preservation of the canonical exact head, and the complete signed range-energy identity.
- `MultiRangeCompleteness.lean`: finite normalized coordinates for every legal sequence; vanishing initial values force the low coefficients to vanish; explicit reconstruction using only divisors above the initial interval; every legal exact head is a corrected canonical witness.
- `MultiRangeEnergyCertificates.lean`: scalar optimization along arbitrary finite range combinations, including the zero-energy case; iterated preservation of the exact head; an exact signed gain budget and its compulsory head-mass bound; rigorous upper and lower finite-sum certificates for the actual infinite energy.

A range combination is one arbitrary shared deterministic coefficient vector. Optimizing its scalar amplitude does not by itself optimize over all vectors in the range. The new iteration theorem makes no unsupported assertion to that effect.

## Reused existing results

- `CanonicalMobiusConditionalHead.lean` proves the explicit canonical witness and
  `E <= Y(2Y+1)/(Y+2) < 2Y` for positive Y, stronger than the source document's coarse `E<4Y` bound. The audit of `canonicalMobiusHead_energy_le` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- `ConditionalMeanSignedProjection.lean` retains the actual signed infinite pairings, scalar and two-direction Schur completion, and the delayed-correction locality bound.
- `ConditionalMeanGram.lean` supplies the full finite-matrix signed completion with explicit finite inverse premises.
- `ConditionalFiniteMatrixMinimum.lean` establishes actual finite-conductor positive definiteness, existence of minimizers, and the inverse formula.
- `ConditionalConductorExhaustion.lean` establishes decreasing finite-conductor minima and their convergence to the unrestricted legal infimum.
- `CRTPeriodicEnergy.lean` and the exact CRT energy modules own the periodic weighted formulas; they are not replaced by uniform CRT averages.
- `ConditionalMeanSubpolynomial.lean` owns the existing conditional-mean zero obstruction and the conditional implication to Mathlib's `RiemannHypothesis`.

## Explicit open mathematical obligation

`MultiRangeSubpolynomialTarget` is a `Prop` definition requiring an actual cofinal family of the corrected canonical witnesses with subpolynomial conditional-mean energy.
`riemannHypothesis_of_multiRangeSubpolynomialTarget` proves only its implication to RH.
There is no theorem supplying the target, no new axiom, and no RH proof.

## Coverage limits

The source document is submitted in full as a mathematical research note. This does not mean every sentence has been separately kernel formalized.
In particular, its exact block-by-block matrix formula for an arbitrary partition, uniqueness in the specific anchored coordinate chart, and convergence of the *rational truncated optimizer certificates* have not been assembled as new specialized declarations here. The existing finite-matrix results cover their algebraic ingredients and full-energy finite-conductor optimization; they are not a substitute for those exact missing specialized statements.
The new finite-certificate theorem bounds the infinite tail of any supplied legal candidate under its explicit conditional-mean bound. It does not assert that a finite numerical optimum proves a uniform asymptotic estimate.
The strengthened tail-only zero obstruction in the source's equation (10.3) is not claimed as newly checked; the existing full-energy obstruction is reused for the RH implication.

## Verification policy

No candidate Lean declarations are being published as established results. The documentation-only checkpoint skips Lean compilation; success of that checkpoint certifies documentation publication, not proof verification. No unproved arithmetic existence assumption is disguised as a theorem by an axiom audit.

## Recovery

- Workspace: `ws_HgRpBs_2nHztmlD0dQwwPWFDDoGpj4-q`.
- Full candidate job: `job_HRi9ITYZ9mLNO52zB2AGvVVTygZhcIcp`, terminal `wall_timeout` after 180 seconds.
- Narrower construction/energy job: `job_Pc-jl3f7kNLLJ_rEjRWpAGj3thTMn02v`, terminal `wall_timeout` after 300 seconds.
- Earlier compiler diagnostics were used to repair the candidate sources, but the repaired versions have no successful verification result.
- Two status calls returned HTTP 504; job recovery then established both terminal timeout states. No duplicate pending verification was submitted.
- Recovery package: `RH_Multi_Range_Lean_Submission_2026-09-18.zip`.
- Resume by reading the repository state and testing the candidates in small coherent units; preserve the open bound. Add exports and established catalog entries only after verification succeeds.

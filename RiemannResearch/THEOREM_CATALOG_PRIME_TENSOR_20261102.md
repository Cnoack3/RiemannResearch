# Prime tensor CRT verification ledger — 2 November 2026

## Seven-atom rational upper bound — 4 November 2026

`RH/QSquarefreeRationalUpperBounds.lean` proves `complete_norm_lt`,
`legalErrorInfimum_lt`, and `anchoredInfimum_lt`, with strict bound
`361/10000` for the complete infinite Q law. The seven squarefree
conductors are 2, 3, 5, 6, 10, 15, and 30; all coefficients are rational.

- Saved-file check `job_0BXFq4iBPSSYeVblqeP0bxp77beikPg-`: verified=true,
  exit code 0; reported verification duration 60.222 seconds.
- Updated saved-module import and axiom audit
  `job_8dcGsYn_Js5r8oIqES9H3bVFSHqemjYm`: verified=true, exit code 0;
  reported verification duration 28.203 seconds. All three endpoints use
  only propext, Classical.choice, and Quot.sound.
- Final saved-source acceptance and publication are supplied by the
  checkpoint carrying this ledger entry; neither development check alone
  is asserted to validate the entire project.

The companion memorandum `RH/SquarefreeRationalUpperBounds20261103.md`
records the stronger 121-atom bound `5873/1000000` with exact Python
arithmetic and an on-paper infinite-tail proof. That stronger certificate
is NOT a Lean theorem. `RH/SquarefreeRationalReproduction20261103.md`
contains the full scripts and exact data as documentary source. No
protected tools-directory changes are included. The zero-infimum equality
and the proposed cofinal Schur-complement gain estimate remain OPEN.

## Saved-source checkpoint

- Base inspected: `d082427c3a34170c6d35fead5a8d70272978ba20`.
- First published commit: `33e2737107de319c6b661c2dd20d4836857ee1ce`.
- Checkpoint `job_yZD4oE-CPlw5qDd32D9HooPxSfhTbekv` succeeded and pushed.
- Scope: full project aggregate plus `Analysis.FiniteTensorTail`; build 833.326 seconds.
- Second published commit: `f409efc3045e196ed3da3ffeb494c3f7c86aa24e`.
- Checkpoint `job_utM0GTqwoFvydyj5tIvTTxmm1toxGyVv` succeeded and pushed.
- Scope: full project aggregate plus four changed modules; build 1278.133 seconds.
- Development verification for that group: `job_j_sRii0VYjI2bvQ88sHoLHAZ8RrnWHP2` (242.112 seconds).
- The final rational benchmark passed `job_X-47hE00ftTCDBUPSWA4zG61aGy_DYTs` (66.524 seconds); saved-source validation is provided by the checkpoint containing this ledger update.

## Unconditional finite and obstruction results

| Module | Checked statements |
|---|---|
| `Analysis/FiniteTensorTail.lean` | `split_error`, `tail_gram_exact`, `tail_gram_nonneg`, `column_tail_sq`, `column_certificate`: exact complete error split and signed Gram/column certificates |
| `Analysis/HeavyAtomVariance.lean` | `gap_identity`, `variance_le`: sharp scalar variance bound with one atom of mass at least one half |
| `RH/QDivisorGcdCutoff.lean` | `divisorWavelet_cutoff_span_eq`, `qSequence_gcd_of_mem_wavelet_cutoff`: finite wavelet/divisor spans agree and physical coordinates depend on gcd |
| `RH/QSquarefreeAnalysisObstruction.lean` | `residue_three_distance_lower`, `residue_three_not_mem`: positive complete-Q error for the closed squarefree-analysis-row span |

The obstruction concerns analysis rows, not the squarefree synthesis restriction.
The finite cutoff module does not yet formalize the converse characterization
of every gcd-cell function or the complete conditional-expectation formula.
The heavy-atom module proves the scalar inequality; its summed arithmetic
application is a separate on-paper proof.

## Conditional arithmetic certificate and RH

`RH/QTensorCertificate.lean` uses actual normalized divisor-wavelet rows and
actual Q residue columns. `error_le_certificate` includes the complete omitted
tail. `squarefree_closure_of_certificates` and
`riemannHypothesis_of_certificates` consume the explicitly defined
`ArbitrarilySmallCertificates` premise.

**Open:** produce arbitrarily small complete certificates unconditionally.
The final theorem concludes Mathlib's literal `RiemannHypothesis`; it does
not prove the open premise and does not assume an unnamed analytic provider.

## Axiom audit and prior results

Development audits of the listed endpoint theorems reported only
`propext`, `Classical.choice`, and `Quot.sound`, with no project-local axioms
or `sorryAx`. The existing theorem
`QSquarefreeSublinearHeads.arbitrarily_small_linear_cost` was also audited
with the same result; its PNT-based o(H) result predates this work.

The published RH-to-squarefree-density implication, sharp summed gcd
estimate, Cesàro counterexample, operator classification, and other
unlisted arguments are not formalized by these modules. The companion
research memorandum distinguishes those on-paper proofs from this ledger.

## Complete rational benchmark and reproducibility

`QTensorCertificate.Benchmark.complete_norm_lt` proves
`‖errorVector‖^2 < (59 : ℝ) / 1000`, where the actual Q-Hilbert error is
one minus the rational combination with coefficients
1045918/1000000, 1069558/1000000, 604750/1000000 at conductors 2, 3, 6.
The proof bounds the infinite norm by the exact first-period reciprocal
energy 53001021710221/900000000000000. Its audit reports only the same
three standard axioms. It is an unconditional full-tail bound.

The stronger 0.05476–0.05478 enclosure is a separate exact Python rational
computation with integral-test tails, not a Lean theorem. Floating optimizers,
adaptive rows, and polygamma comparisons are explicitly labelled diagnostics.

The companion `RH/PrimeTensorCRTResults20261102.md` contains proofs for
all eight agendas where obtained, counterexamples, exact remaining obligations,
published-source attribution, and the unconditional PNT cutoff refinement.
The companion diagnostic archive supplies runnable Python/JSON and Wolfram
files; `RH/PrimeTensorCRTReproduction20261102.md` records their source in
this repository.
No numerical trend is used as an asymptotic arithmetic provider.

Reproduce changed-source validation with
`lake build +RiemannResearch.RH.QTensorCertificate --quiet`.
The aggregate export was validated in both earlier full checkpoints.

## Signed certificate continuation — 2 November 2026

The follow-up to section 4 extends the two existing modules; no new
aggregate imports or dependency changes are needed.

| Module | New declarations and status |
|---|---|
| `Analysis/FiniteTensorTail.lean` | `anchored_split`, `anchored_tail_le`, `anchored_synthesis_split`, `anchored_certificate`: exact anchor-bias remainder and a signed quadratic majorant |
| Same | `tail_inner_eq`: exact entrywise complete Gram subtraction |
| Same | `tail_sq_add_row`, `columnCertificate_add_row_le`: exact single-row tail split and certificate monotonicity |
| Same | `weighted_diagonal_majorant`: a genuine diagonal PSD majorant for every positive weight family |
| Same | `block_certificate`, `merge_blocks_le`: exact within-block covariance and decreasing block triangle penalty |
| `RH/QTensorCertificate.lean` | `certificate_add_row_le`: monotonicity for actual normalized Q divisor-wavelet rows |
| Same | `anchoredCertificate_eq_error_add_bias`, `error_le_anchoredCertificate`: complete-Q exact identity and upper bound |
| Same | `squarefree_closure_of_anchoredCertificates`, `riemannHypothesis_of_anchoredCertificates`: **conditional research reductions** |

**Open:** `ArbitrarilySmallAnchoredCertificates`. No unconditional
arithmetic provider has been proved. Anchor membership in the finite
retained subspace is required explicitly. The actual gcd-anchor membership
and conditional-cell formulas are not supplied by this continuation.

Successful coherent development checks:
- `job_eWaehDLrrwqSF_Wf0gmoGMzZX3N-DzXj`: 5.432 seconds reported verification,
  exact anchors, row monotonicity, and weighted majorant.
- `job_FwxNFW2Dr7ZlL5vWBzgr1rHe4Y_9tnps`: 5.188 seconds reported verification,
  also including Gram subtraction and block results.
- `job_q-UqE1j5vGcQRzaezTkfQd4wzDMPKoms`: 6.917 seconds reported verification,
  actual-Q assembly and the literal Mathlib RH consumer.

All audited endpoints reported only `propext`, `Classical.choice`,
and `Quot.sound`. These are development checks; final saved-source
publication is certified by the checkpoint carrying this update.
Request round trips, workspace-opening time, and queue/polling delay are
not included in these reported verification durations. The opening
response did not report a duration; the listed jobs started within
0.01 seconds of their server submission timestamps.

See `RH/PrimeTensorSignedCertificates20261102.md` for precise formulas,
provenance, the finite Wolfram diagnostic, and the remaining RH obligation.

## Infimum RH implicators — 2 November 2026

New module: `RH/QTensorCertificateInfimum.lean`.

The actual sets of complete column-certificate, anchored-certificate, and
finite squarefree legal-error values are defined explicitly. Each is
proved nonempty and nonnegative, so each real `sInf` is a genuine
variational infimum. No minimum or attainment is assumed.

- `columnInfimum_eq_zero_iff`: zero column infimum is equivalent to
  the already defined arbitrarily-small-column-certificate premise.
- `anchoredInfimum_eq_zero_iff`: the analogous exact equivalence for
  the signed anchor certificates.
- `riemannHypothesis_of_columnInfimum_zero` and
  `riemannHypothesis_of_anchoredInfimum_zero`: **conditional research
  reductions** concluding Mathlib's literal `RiemannHypothesis`.
- `anchoredCertificate_projection_eq_error`: projected anchors recover
  the exact complete Q error for each fixed synthesis. The target row
  must be retained and the rows must be distinct.
- `anchoredInfimum_eq_legalErrorInfimum`: optimizing over anchors is
  exactly optimizing the actual finite squarefree legal approximation
  error. The proof of this equality already works with one constant
  analysis row for the projected-anchor construction.
- `legalErrorInfimum_le_columnInfimum`: the true-error infimum is no
  larger than the complete column-certificate infimum.
- `riemannHypothesis_of_legalErrorInfimum_zero`: the corresponding
  actual-error criterion, still conditional.
- `legalErrorInfimum_lt_benchmark` and
  `anchoredInfimum_lt_benchmark`: unconditional strict upper bound
  59/1000, using the existing checked rational three-atom certificate.
  Nonnegativity is also proved.

The implication proof is explicit: infimum zero gives a complete
certificate below epsilon squared for every epsilon > 0. Its actual
Q-error norm is then below epsilon, giving squarefree legal closure of one.
The existing capacity/Mellin consumer supplies RH.

**Open:** `columnInfimum = 0`, equivalently the column epsilon provider,
or `anchoredInfimum = 0`, equivalently the anchored epsilon provider.
No theorem in this continuation establishes either equality. In particular,
the strict 0.059 bound does not imply zero, and projected anchors preserve
the exact error rather than make it vanish.

Development verification:
- `job_JyZFHzvvR4mPUk4Ir6nulNN5R3Hm1fvU` succeeded, reported
  verification 36.859 seconds; audited both certificate-infimum RH endpoints
  and the exact projection-anchor identity.
- `job_wrkQUqaUXMSd7bO3FFn4U_QeT_NnR-dv` succeeded, reported
  verification 6.202 seconds; audited exact infimum equality, the actual
  error-infimum RH endpoint, and the finite benchmark.
- All audited endpoints used only `propext`, `Classical.choice`,
  and `Quot.sound`.
- The workspace-resume request round trip was 92.011 seconds. This is
  separate from Lean verification. Both successful jobs had server queue
  delays below 0.01 seconds. Polling and request latency are not kernel
  checking time.

Final saved-source validation and publication are provided by the checkpoint
carrying this catalog update, covering the new module and aggregate export.

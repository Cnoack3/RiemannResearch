# Prime tensor CRT verification ledger — 2 November 2026

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

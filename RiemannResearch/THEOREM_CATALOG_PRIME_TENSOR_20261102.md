# Prime tensor CRT verification ledger — 2 November 2026

## Saved-source checkpoint

- Base inspected: `d082427c3a34170c6d35fead5a8d70272978ba20`.
- First published commit: `33e2737107de319c6b661c2dd20d4836857ee1ce`.
- Checkpoint `job_yZD4oE-CPlw5qDd32D9HooPxSfhTbekv` succeeded and pushed.
- Scope: full project aggregate plus `Analysis.FiniteTensorTail`; build 833.326 seconds.
- The next group passed development verification `job_j_sRii0VYjI2bvQ88sHoLHAZ8RrnWHP2` (242.112 seconds). Its saved-source validation is provided by the checkpoint containing this ledger update.

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

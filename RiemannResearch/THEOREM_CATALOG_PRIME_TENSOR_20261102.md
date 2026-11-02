# Prime tensor CRT verification ledger — 2 November 2026

## Finite orthonormal-row certificates

Module: `Analysis/FiniteTensorTail.lean`.

- `split_error`: exact retained-row and omitted-energy decomposition.
- `tail_gram_exact`, `tail_gram_nonneg`: actual signed residual Gram and positivity.
- `column_tail_sq`: column tail from full norm minus retained coefficients.
- `column_certificate`: complete error upper bound when the target lies in the retained analysis span.

These are unconditional Hilbert-space results. The RH application uses divisor-wavelet analysis rows and squarefree legal synthesis columns. Neither a vanishing arithmetic certificate nor RH is assumed or concluded by this module. Axiom inspection of `column_certificate` in development reported only `propext`, `Classical.choice`, and `Quot.sound`; final saved-source status is supplied by the checkpoint record.

## Open arithmetic provider

Open: construct an actual growing squarefree legal family whose complete certificate tends to zero. This ledger does not promote a conditional reduction to an unconditional RH result.

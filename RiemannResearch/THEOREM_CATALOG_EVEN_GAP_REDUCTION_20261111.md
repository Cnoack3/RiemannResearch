# Even-gap reduction and complete model-transfer catalog

Review base: `6c4fe3312e24b00813bcc5c329cf28ba0fe14333`.
Publication authorized by the user on 2026-11-11. The server checkpoint
audits and validates the integrated project before publication.

## Checked source scope

Four new modules, 30 theorems and 14 definitions, totaling 550 Lean source
lines. No theorem in an existing module is weakened or replaced.

| Module | Theorems | Main declarations |
|---|---:|---|
| `Analysis/EvenGapPrimeReduction.lean` | 12 | `offDiagonal_even_exact`, `prefix_even_exact`, `oddRaw_le`, `evenResidual_enclosure`, `evenResidual_lower`, `evenResidual_tendsto_iff` |
| `Analysis/EvenGapPrimeAsymptotic.lean` | 5 | `normalized_budget_le`, `budget_tendsto_of_width`, `evenResidual_iff_of_width`, `polynomial_width_small`, `evenResidual_iff_polynomial` |
| `Analysis/EvenGapSingularModel.lean` | 3 | `evenRawDefect_prefix_exact`, `model_comparison_exact`, `evenRawDefect_abs_le` |
| `Analysis/ShortIntervalModelTransfer.lean` | 10 | `energy_transfer_exact`, `energy_variational_exact`, `centeredVariance_model_lower`, `energy_transfer_abs_le`, `finiteModel_energy_gram` |

All names above have prefix `RiemannResearch.Analysis.<module>.`.

## Established finite statements

With notation defined in `EVEN_GAP_RESEARCH_20261111.md`,

\[
 C+HN\log H=F_e+O_o,\qquad
 0\le O_o\le4W_o\log^2(N+H+2).
\]

Every one-point error and the complete signed boundary are contained in
`F_e`. The raw odd exception is an actual finite Mangoldt sum, not an
unproved error provider. The bound uses the already checked power-of-two
support of odd prime pairs.

The singular-model equality is valid for every real sequence `sigma` that
vanishes on odd gaps. It retains its actual even-pair defect, complete
one-point drift and boundary correction. The finite model-energy identity
retains the actual mixed term and residual square, and the Gram identity
retains all off-diagonal coefficients.

## Checked research reductions

For positive `H=o(N/log N)` with `H<=N` eventually, the complete normalized
off-diagonal error tends to zero if and only if the normalized `F_e` does.
The polynomial-width consumer proves this for every fixed `epsilon>0`
and every positive integer width eventually bounded by `N^(1-epsilon)`.
These are **conditional research reductions**: the remaining even-error
smallness is Open. Neither side of the equivalence is asserted to hold.

## Analytic input status

| Input | Mathematical status | Status in this development |
|---|---|---|
| Odd raw prime-pair support and logarithmic bound | Unconditional, existing Lean result | Reused directly |
| Corrected odd contribution negligible at variance scale | Unconditional for stated width range | Checked new theorem |
| Triangular singular-series secondary term | Published unconditional theorem | External; not imported as an axiom |
| MRT averaged prime-pair estimate | Published unconditional theorem | External; finite consumer checked |
| Guth--Maynard short-interval estimates | Published unconditional theorem | External; coarse consequence derived on paper |
| Actual signed even defect with mean and boundary corrections | Open | Open |
| Growing Ramanujan-model residual energy at variance scale | Open here | Open |
| Full raw pair-correlation limit | Open | Open |

## Verification evidence

The final saved-module import check is `job_NGZB1XLJSEtV4sPoxLSBoN3v9jvTQlff`:
`backend=bazel`, `state=succeeded`, `verified=true`, `exit_code=0`.
It imports all four saved modules and compiles their transitive dependencies.
Server-reported check duration: 50.659 seconds, excluding workspace setup
and client polling delays.

Build record:
<https://app.buildbuddy.io/invocation/caf7c509-989a-49ea-a094-55032318038a>.

The separate foundation audit is `job_otMt38FT4EhBpddpVgYJ2Kfe7bnTOle0`:
`backend=bazel`, `state=succeeded`, `verified=true`, `exit_code=0`, 52.407 seconds.
Its ten `#guard_msgs` checks assert that the major declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`. The checked audit source and
terminal metadata are `verification_audit.lean` and `verification_axioms.json`.
Audit build: <https://app.buildbuddy.io/invocation/2fd36d48-8ead-4c59-83f0-9ed91a290b7c>.
No whole-project build is claimed. Initial audit attempts failed because the
expected diagnostic line wrapping differed; the final audit matches the
observed output and passes. No mathematical source changed for this fix.

The checks above are prepublication checks. The final publication checkpoint
provides the full-project result separately. Numerical CSV/JSON files in the
review archive are floating-point diagnostics; the sieve and FFT computations are not certified
by Lean. The printed singular-series constant is approximate.

References and precise derivations appear in `EVEN_GAP_RESEARCH_20261111.md`.
